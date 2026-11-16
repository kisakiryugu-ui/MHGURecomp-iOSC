// MHGURecomp iOS touchscreen controls: custom pass-through UIKit overlay.
// iOS 15+, Objective-C (manual retain/release, matching the project Makefile).
// Input goes directly into host_input_update; no virtual SDL controller required.
#import <UIKit/UIKit.h>
#import <CoreText/CoreText.h>
#import <QuartzCore/QuartzCore.h>
#import <GameController/GameController.h>
#import <UniformTypeIdentifiers/UniformTypeIdentifiers.h>
#import <SDL3/SDL.h>
#import <SDL3/SDL_video.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include "config.h"
#include "overlay.h"
#include "touch_overlay.h"
#include "hle/input.h"
#include <dispatch/dispatch.h>

// Queued item/ammo steps are emitted over separate input frames.
static atomic_int s_itemSteps, s_ammoSteps;
static atomic_uint_fast64_t s_stepDueMs;
static uint64_t s_lastWeaponPollMs;
static void queue_steps(BOOL ammo, int steps) {
    atomic_int *dst = ammo ? &s_ammoSteps : &s_itemSteps;
    int old = atomic_load(dst), next = MAX(-6, MIN(6, old + steps));
    atomic_store(dst, next);
}


static atomic_uint_fast64_t s_buttons;
static atomic_int s_buttonRefs[16];
static atomic_uint_fast64_t s_pulseUntilMs[16];
static atomic_uint_fast64_t s_attackUntilMs[16];
static const uint64_t s_manualAttackMask = (UINT64_C(1) << BTN_A) | (UINT64_C(1) << BTN_X) | (UINT64_C(1) << BTN_Y);
enum { TOUCH_COMBO_COUNT = 2, COMBO_MIN_MS = 75, COMBO_TIMEOUT_MS = 250, COMBO_MAX_PENDING = 8 };
typedef struct {
    uint64_t mask, started;
    unsigned pending;
    bool held, releasing;
} TouchCombo;
static pthread_mutex_t s_comboLock = PTHREAD_MUTEX_INITIALIZER;
static TouchCombo s_combos[TOUCH_COMBO_COUNT];
static atomic_uint s_comboActive;
static atomic_bool s_traceCombos;
static atomic_int s_lx, s_ly, s_rx, s_ry;
static atomic_int s_swipeRx, s_swipeRy;
static atomic_uint_fast64_t s_lastSwipeMs, s_centerCameraUntilMs;
static atomic_bool s_iosForeground = ATOMIC_VAR_INIT(1);
static BOOL mhgu_ios_is_foreground(void) {
    return atomic_load_explicit(&s_iosForeground, memory_order_acquire) ? 1 : 0;
}

static uint64_t mhgu_now_ms(void) {
    return (uint64_t)(CACurrentMediaTime() * 1000.0);
}

static void arm_combo(size_t slot, uint64_t mask, uint64_t now) {
    pthread_mutex_lock(&s_comboLock);
    TouchCombo *combo = &s_combos[slot];
    if (!combo->pending && !combo->releasing) combo->started = now;
    combo->mask = mask;
    combo->held = true;
    if (combo->pending < COMBO_MAX_PENDING) combo->pending++;
    atomic_fetch_or_explicit(&s_comboActive, 1u << slot, memory_order_release);
    pthread_mutex_unlock(&s_comboLock);
}

static void clear_combo_locked(size_t slot) {
    s_combos[slot] = (TouchCombo){0};
    atomic_fetch_and_explicit(&s_comboActive, ~(1u << slot), memory_order_release);
}

static void finish_combo(size_t slot, bool cancel) {
    pthread_mutex_lock(&s_comboLock);
    if (cancel) clear_combo_locked(slot);
    else s_combos[slot].held = false;
    pthread_mutex_unlock(&s_comboLock);
}

void mhgu_touch_combo_sampled(uint64_t buttons) {
    if (!atomic_load_explicit(&s_comboActive, memory_order_acquire)) return;
    uint64_t sampled[TOUCH_COMBO_COUNT] = {0};
    pthread_mutex_lock(&s_comboLock);
    uint64_t now = mhgu_now_ms();
    for (size_t i = 0; i < TOUCH_COMBO_COUNT; i++) {
        TouchCombo *combo = &s_combos[i];
        if (!combo->mask) continue;
        bool complete = (buttons & combo->mask) == combo->mask;
        if (combo->releasing) {
            // The guest has to see the pair released before another tap can make a new press.
            if (!complete) {
                if (!combo->pending) clear_combo_locked(i);
                else {
                    combo->releasing = false;
                    combo->started = now;
                }
            }
        } else if (complete && combo->pending && now - combo->started >= COMBO_MIN_MS &&
                   (!combo->held || combo->pending > 1)) {
            sampled[i] = combo->mask;
            combo->pending--;
            combo->releasing = true;
            combo->started = now;
        }
    }
    pthread_mutex_unlock(&s_comboLock);
    if (atomic_load_explicit(&s_traceCombos, memory_order_relaxed))
        for (size_t i = 0; i < TOUCH_COMBO_COUNT; i++)
            if (sampled[i]) fprintf(stderr, "[MHGU Touch] Combo %zu sampled mask=0x%llx\n",
                                    i + 1, (unsigned long long)sampled[i]);
}

// Reference-counted masks keep L/Y/A held correctly if a user presses a combo
// and an ordinary button at the same time. All UIKit presses occur on main.
static void pulse_mask(atomic_uint_fast64_t deadlines[16], uint64_t mask, uint64_t duration_ms) {
    uint64_t until = mhgu_now_ms() + duration_ms;
    for (unsigned bit = 0; bit < 16; bit++)
        if ((mask & (UINT64_C(1) << bit)) && until > atomic_load_explicit(&deadlines[bit], memory_order_relaxed))
            atomic_store_explicit(&deadlines[bit], until, memory_order_relaxed);
}
static void pulse_button_mask(uint64_t mask, uint64_t duration_ms) {
    pulse_mask(s_pulseUntilMs, mask, duration_ms);
}
static void clear_attack_pulse(uint64_t mask) {
    for (unsigned bit = 0; bit < 16; bit++)
        if (mask & (UINT64_C(1) << bit))
            atomic_store_explicit(&s_attackUntilMs[bit], 0, memory_order_relaxed);
}
static void set_button_mask(uint64_t mask, BOOL pressed) {
    uint64_t changed = 0;
    for (unsigned bit = 0; bit < 16; bit++) {
        uint64_t flag = UINT64_C(1) << bit;
        if (!(mask & flag)) continue;
        if (pressed) {
            int before = atomic_fetch_add_explicit(&s_buttonRefs[bit], 1, memory_order_relaxed);
            if (before == 0) changed |= flag;
        } else {
            int before = atomic_fetch_sub_explicit(&s_buttonRefs[bit], 1, memory_order_relaxed);
            if (before <= 1) {
                atomic_store_explicit(&s_buttonRefs[bit], 0, memory_order_relaxed);
                changed |= flag;
            }
        }
    }
    if (!changed) return;
    if (pressed) atomic_fetch_or_explicit(&s_buttons, changed, memory_order_relaxed);
    else atomic_fetch_and_explicit(&s_buttons, ~changed, memory_order_relaxed);
}

static uint64_t touch_button_state(uint64_t now) {
    uint64_t buttons = atomic_load_explicit(&s_buttons, memory_order_relaxed);
    for (unsigned i = 0; i < 16; i++)
        if (now < atomic_load_explicit(&s_pulseUntilMs[i], memory_order_relaxed) ||
            now < atomic_load_explicit(&s_attackUntilMs[i], memory_order_relaxed))
            buttons |= UINT64_C(1) << i;
    if (!atomic_load_explicit(&s_comboActive, memory_order_acquire)) return buttons;
    pthread_mutex_lock(&s_comboLock);
    for (size_t i = 0; i < TOUCH_COMBO_COUNT; i++) {
        TouchCombo *combo = &s_combos[i];
        if (!combo->mask) continue;
        if (now >= combo->started && now - combo->started >= COMBO_TIMEOUT_MS &&
            (combo->releasing || !combo->held || combo->pending > 1)) {
            combo->pending = combo->held ? 1 : 0;
            combo->releasing = false;
            combo->started = now;
            if (!combo->pending) clear_combo_locked(i);
        }
        if (!combo->releasing && combo->pending) buttons |= combo->mask;
    }
    pthread_mutex_unlock(&s_comboLock);
    return buttons;
}

@class MHGUTouchRoot;
static MHGUTouchRoot *s_overlay;
static void poll_overlay_weapon(void);

void mhgu_touch_snapshot(uint64_t *buttons, int *lx, int *ly, int *rx, int *ry) {
    uint64_t now = mhgu_now_ms();
    // SDL host_input_update is run by the app's main thread.
    // Avoid UIKit operations on a possible non-main caller.
    if ([NSThread isMainThread] && s_overlay) poll_overlay_weapon();
    // Step sequencer: no burst of simultaneous X/B/A/Y events on a long flick.
    if (now >= atomic_load(&s_stepDueMs)) {
        int item = atomic_load(&s_itemSteps), ammo = atomic_load(&s_ammoSteps);
        if (item || ammo) {
            int direction = item ? item : ammo;
            uint64_t mask = UINT64_C(1) << BTN_L;
            if (item) mask |= UINT64_C(1) << (direction > 0 ? BTN_A : BTN_Y);
            else mask |= UINT64_C(1) << (direction > 0 ? BTN_X : BTN_B);
            pulse_button_mask(mask, 75);
            if (item) atomic_fetch_add(&s_itemSteps, item > 0 ? -1 : 1);
            else atomic_fetch_add(&s_ammoSteps, ammo > 0 ? -1 : 1);
            atomic_store(&s_stepDueMs, now + 125);
        }
    }
    *buttons = touch_button_state(now);
    if (now < atomic_load_explicit(&s_centerCameraUntilMs, memory_order_relaxed))
        *buttons |= UINT64_C(1) << BTN_L;
    *lx = atomic_load_explicit(&s_lx, memory_order_relaxed);
    *ly = atomic_load_explicit(&s_ly, memory_order_relaxed);
    *rx = atomic_load_explicit(&s_rx, memory_order_relaxed);
    *ry = atomic_load_explicit(&s_ry, memory_order_relaxed);
    // Swipe turns the stick only while movement is being reported; avoid
    // a camera that keeps spinning after the last finger-motion event.
    if (now - atomic_load_explicit(&s_lastSwipeMs, memory_order_relaxed) < 65) {
        *rx += atomic_load_explicit(&s_swipeRx, memory_order_relaxed);
        *ry += atomic_load_explicit(&s_swipeRy, memory_order_relaxed);
    }
}

static void mhgu_touch_clear(void) {
    atomic_store_explicit(&s_buttons, 0, memory_order_relaxed);
    atomic_store(&s_itemSteps, 0);
    atomic_store(&s_ammoSteps, 0);
    atomic_store(&s_stepDueMs, 0);
    for (int i = 0; i < 16; i++) {
        atomic_store_explicit(&s_buttonRefs[i], 0, memory_order_relaxed);
        atomic_store_explicit(&s_pulseUntilMs[i], 0, memory_order_relaxed);
        atomic_store_explicit(&s_attackUntilMs[i], 0, memory_order_relaxed);
    }
    pthread_mutex_lock(&s_comboLock);
    for (size_t i = 0; i < TOUCH_COMBO_COUNT; i++) clear_combo_locked(i);
    pthread_mutex_unlock(&s_comboLock);
    atomic_store_explicit(&s_swipeRx, 0, memory_order_relaxed);
    atomic_store_explicit(&s_swipeRy, 0, memory_order_relaxed);
    atomic_store_explicit(&s_lastSwipeMs, 0, memory_order_relaxed);
    atomic_store_explicit(&s_centerCameraUntilMs, 0, memory_order_relaxed);
    atomic_store_explicit(&s_lx, 0, memory_order_relaxed);
    atomic_store_explicit(&s_ly, 0, memory_order_relaxed);
    atomic_store_explicit(&s_rx, 0, memory_order_relaxed);
    atomic_store_explicit(&s_ry, 0, memory_order_relaxed);
}

// Translucent gameplay controls and a higher contrast settings panel.
static NSString *const gearOpacityKey = @"mhgu_touch_gear_opacity_v45";
static NSString *const gearOverrideKey = @"mhgu_touch_override_gear_opacity";
static NSString *const gearControlKey = @"SETTINGS_GEAR";
static NSString *const newestAttackKey = @"mhgu_touch_newest_attack";
static NSString *const headingFontKey = @"mhgu_touch_heading_font";
static const CGFloat minimumGearHitSize = 44;

static NSString *comboPreference(NSUInteger slot) {
    return [NSString stringWithFormat:@"mhgu_touch_combo_%lu", (unsigned long)slot];
}
static NSString *defaultCombo(NSUInteger slot) { return slot ? @"R+X" : @"X+A"; }
static NSString *comboControlKey(NSUInteger slot) { return slot ? @"COMBO_2" : @"COMBO_1"; }
static NSString *savedCombo(NSUInteger slot) {
    return [[NSUserDefaults standardUserDefaults] stringForKey:comboPreference(slot)] ?: defaultCombo(slot);
}
static NSArray<NSString *> *comboNames(void) {
    return @[@"A", @"B", @"X", @"Y", @"L", @"R", @"ZL", @"ZR", @"PLUS", @"MINUS"];
}

static UIColor *hudGold(void) {
    return [UIColor colorWithRed:.91 green:.79 blue:.54 alpha:1.0];
}
static UIColor *hudCream(void) {
    return [UIColor colorWithRed:.98 green:.96 blue:.91 alpha:1.0];
}
static UIColor *hudBackground(void) {
    return [UIColor colorWithRed:.09 green:.10 blue:.12 alpha:.86];
}
static UIColor *hudPressed(void) {
    return [UIColor colorWithRed:.34 green:.26 blue:.15 alpha:.98];
}
static void mhgu_style_menu(UIButton *button) {
    button.backgroundColor = hudBackground();
    button.layer.cornerRadius = 10.0;
    button.layer.borderWidth = 1;
    button.layer.borderColor = [hudGold() colorWithAlphaComponent:.72].CGColor;
    button.titleLabel.font = [UIFont systemFontOfSize:13 weight:UIFontWeightSemibold];
    button.titleLabel.adjustsFontSizeToFitWidth = YES;
    button.titleLabel.minimumScaleFactor = .65;
    [button setTitleColor:hudCream() forState:UIControlStateNormal];
    [button setTitleColor:hudGold() forState:UIControlStateHighlighted];
    [button setTitleColor:[hudCream() colorWithAlphaComponent:.35] forState:UIControlStateDisabled];
}

static UILabel *touch_label(NSString *title, CGFloat size, UIFontWeight weight) {
    UILabel *label = [[[UILabel alloc] initWithFrame:CGRectZero] autorelease];
    label.text = title;
    label.textColor = hudCream();
    label.font = [UIFont systemFontOfSize:size weight:weight];
    label.adjustsFontSizeToFitWidth = YES;
    label.minimumScaleFactor = .75;
    label.userInteractionEnabled = NO;
    return label;
}

static NSURL *headingFontDirectory(void) {
    NSURL *support = [[[NSFileManager defaultManager] URLsForDirectory:NSApplicationSupportDirectory
                                                               inDomains:NSUserDomainMask] firstObject];
    return [support URLByAppendingPathComponent:@"TouchFonts" isDirectory:YES];
}

static NSString *registerHeadingFont(NSURL *url) {
    if (!url) return nil;
    CFArrayRef descriptors = CTFontManagerCreateFontDescriptorsFromURL((__bridge CFURLRef)url);
    if (!descriptors) return nil;
    CFStringRef name = CFArrayGetCount(descriptors) > 0 ?
        CTFontDescriptorCopyAttribute(CFArrayGetValueAtIndex(descriptors, 0), kCTFontNameAttribute) : NULL;
    CFRelease(descriptors);
    if (!name) return nil;
    NSString *postScriptName = [(NSString *)name autorelease];
    if (!CTFontManagerRegisterFontsForURL((__bridge CFURLRef)url, kCTFontManagerScopeProcess, NULL)) return nil;
    if ([UIFont fontWithName:postScriptName size:18]) return postScriptName;
    CTFontManagerUnregisterFontsForURL((__bridge CFURLRef)url, kCTFontManagerScopeProcess, NULL);
    return nil;
}

static UIFont *touchHeadingFont(NSString *importedName) {
    static NSString *bundledName;
    static dispatch_once_t once;
    dispatch_once(&once, ^{
        NSURL *url = [[NSBundle mainBundle] URLForResource:@"Cinzel" withExtension:@"ttf" subdirectory:@"Fonts"];
        bundledName = [registerHeadingFont(url) copy];
    });
    return [UIFont fontWithName:(importedName ?: bundledName ?: @"Cinzel-Regular") size:18] ?:
        [UIFont systemFontOfSize:18 weight:UIFontWeightSemibold];
}

static UIButton *touch_menu_button(NSString *title, id target, SEL action) {
    UIButton *button = [UIButton buttonWithType:UIButtonTypeCustom];
    mhgu_style_menu(button);
    [button setTitle:title forState:UIControlStateNormal];
    [button addTarget:target action:action forControlEvents:UIControlEventTouchUpInside];
    return button;
}

static CGRect gearHitRect(CGRect rect) {
    CGFloat dx = MAX(0, minimumGearHitSize - rect.size.width) / 2;
    CGFloat dy = MAX(0, minimumGearHitSize - rect.size.height) / 2;
    return CGRectInset(rect, -dx, -dy);
}

@interface MHGUGearButton : UIButton
@end
@implementation MHGUGearButton
- (BOOL)pointInside:(CGPoint)point withEvent:(UIEvent *)event {
    (void)event;
    return CGRectContainsPoint(gearHitRect(self.bounds), point);
}
- (void)layoutSubviews {
    [super layoutSubviews];
    CGFloat inset = MIN(self.bounds.size.width, self.bounds.size.height) * .2;
    self.imageView.frame = CGRectInset(self.bounds, inset, inset);
    self.imageView.contentMode = UIViewContentModeScaleAspectFit;
}
@end

@interface MHGUTouchButton : UIView {
    uint64_t _mask, _heldMask;
    uint64_t _pressStartMs;
    NSUInteger _comboSlot;
    NSMutableSet *_active;
    UIColor *_accentV44;  // MHGU_IOS_CONTROL_PROFILES_V44
    UILabel *_caption;
    BOOL _pill, _manualAttack;
}
- (id)initWithLabel:(NSString *)label mask:(uint64_t)mask;
- (void)setMask:(uint64_t)mask;
- (void)setComboSlot:(NSUInteger)slot;
- (void)setManualAttack;
- (void)setCaption:(NSString *)caption; // MHGU_IOS_TOUCH_CONTROLS_V43
- (void)setAccentV44:(UIColor *)accent;
- (void)resetInput;
@end

@implementation MHGUTouchButton
- (id)initWithLabel:(NSString *)label mask:(uint64_t)mask {
    if (!(self = [super initWithFrame:CGRectZero])) return nil;
    _mask = mask;
    _comboSlot = NSNotFound;
    _active = [[NSMutableSet alloc] init];
    self.multipleTouchEnabled = YES;
    self.exclusiveTouch = NO; // More than one virtual button at a time.
    self.opaque = NO;
    _pill = label.length > 1;
    _caption = [touch_label(label, 15, UIFontWeightSemibold) retain];
    _caption.textAlignment = NSTextAlignmentCenter;
    _caption.minimumScaleFactor = 0.6;
    [self addSubview:_caption];
    [self setPressedStyle:NO];
    return self;
}
- (void)layoutSubviews {
    [super layoutSubviews];
    CGFloat d = MIN(self.bounds.size.width, self.bounds.size.height);
    self.layer.cornerRadius = d * (_pill ? .32 : .5);
    _caption.frame = CGRectInset(self.bounds, d * .12, 0);
    CGFloat size = _caption.text.length > 2 ? MIN(15, d * .28) : MIN(23, d * .43);
    _caption.font = [UIFont systemFontOfSize:size weight:UIFontWeightBold];
}
- (void)setPressedStyle:(BOOL)pressed {
    self.backgroundColor = pressed ? hudPressed() : hudBackground();
    UIColor *accent = _accentV44 ?: hudGold();
    self.layer.borderColor = [accent colorWithAlphaComponent:(pressed ? 1.0 : .78)].CGColor;
    self.layer.borderWidth = pressed ? 1.8 : 1.0;
    _caption.textColor = pressed ? accent : hudCream();
}
- (void)touchesBegan:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    BOOL wasDown = _active.count > 0;
    [_active unionSet:touches];
    if (!wasDown) {
        _pressStartMs = mhgu_now_ms();
        _heldMask = _mask;
        if (_comboSlot != NSNotFound) arm_combo(_comboSlot, _heldMask, _pressStartMs);
        else set_button_mask(_heldMask, YES);
    }
    [self setPressedStyle:YES];
}
- (void)touchesMoved:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)touches; (void)event;
    // Button remains held even if the finger slides a little outside its visual area.
}
- (void)touchesEnded:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    BOOL wasDown = _active.count > 0;
    [_active minusSet:touches];
    if (wasDown && _active.count == 0) {
        uint64_t elapsed = mhgu_now_ms() - _pressStartMs;
        // A custom combo stays pending until the game samples the whole pair.
        if (_comboSlot == NSNotFound && elapsed < 75)
            pulse_mask(_manualAttack ? s_attackUntilMs : s_pulseUntilMs, _heldMask, 75 - elapsed);
        [self finishPress];
    }
}
- (void)touchesCancelled:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    BOOL wasDown = _active.count > 0;
    [_active minusSet:touches];
    if (wasDown && _active.count == 0) [self resetInput];
}
- (void)setMask:(uint64_t)mask {
    // Keep the active press on its original input through a draw or sheathe.
    _mask = mask;
}
- (void)setComboSlot:(NSUInteger)slot { _comboSlot = slot; }
- (void)setManualAttack { _manualAttack = YES; }
- (void)setCaption:(NSString *)caption {
    if ([_caption.text isEqualToString:caption]) return;
    _caption.text = caption;
    [self setNeedsLayout];
}
- (void)setAccentV44:(UIColor *)accent {
    if (accent != _accentV44) {
        [_accentV44 release];
        _accentV44 = [accent retain];
    }
    [self setPressedStyle:(_active.count != 0)];
}
- (void)finishPress {
    if (_heldMask) {
        if (_comboSlot != NSNotFound) finish_combo(_comboSlot, false);
        else set_button_mask(_heldMask, NO);
    }
    _heldMask = 0;
    [_active removeAllObjects];
    [self setPressedStyle:NO];
}
- (void)resetInput {
    if (_comboSlot != NSNotFound) finish_combo(_comboSlot, true);
    if (_manualAttack) clear_attack_pulse(_mask);
    [self finishPress];
}
- (void)dealloc {
    [self resetInput];
    [_active release];
    [_caption release];
    [_accentV44 release];
    [super dealloc];
}
@end

@interface MHGUTouchStick : UIView {
    BOOL _left;
    UITouch *_tracked;
    UIView *_knob;
    UILabel *_name;
}
- (id)initLeft:(BOOL)left;
- (void)setCaption:(NSString *)caption;
- (void)resetInput;
@end

@implementation MHGUTouchStick
- (id)initLeft:(BOOL)left {
    if (!(self = [super initWithFrame:CGRectZero])) return nil;
    _left = left;
    self.multipleTouchEnabled = YES; // MHGU_IOS_TOUCH_FPS_V42: allow button touches while moving.
    self.exclusiveTouch = NO;
    self.opaque = NO;
    self.backgroundColor = hudBackground();
    self.layer.borderWidth = 1.25;
    self.layer.borderColor = [hudGold() colorWithAlphaComponent:.78].CGColor;
    _knob = [[UIView alloc] initWithFrame:CGRectZero];
    _knob.userInteractionEnabled = NO;
    _knob.backgroundColor = [hudGold() colorWithAlphaComponent:.22];
    _knob.layer.borderColor = hudGold().CGColor;
    _knob.layer.borderWidth = 1.4;
    [self addSubview:_knob];
    _name = [[UILabel alloc] initWithFrame:CGRectZero];
    _name.text = left ? @"MOVE" : @"CAM";
    _name.textColor = [hudCream() colorWithAlphaComponent:.85];
    _name.textAlignment = NSTextAlignmentCenter;
    _name.font = [UIFont systemFontOfSize:10 weight:UIFontWeightSemibold];
    _name.userInteractionEnabled = NO;
    [self addSubview:_name];
    return self;
}
- (void)layoutSubviews {
    [super layoutSubviews];
    CGFloat d = MIN(self.bounds.size.width, self.bounds.size.height);
    self.layer.cornerRadius = d * 0.5;
    CGFloat kd = d * 0.43;
    _knob.bounds = CGRectMake(0, 0, kd, kd);
    _knob.layer.cornerRadius = kd * 0.5;
    if (!_tracked) _knob.center = CGPointMake(self.bounds.size.width / 2, self.bounds.size.height / 2);
    _name.frame = CGRectMake(0, d * 0.08, d, 13);
}
- (void)setCaption:(NSString *)caption { _name.text = caption; }
- (void)setPosition:(CGPoint)p {
    CGFloat cx = self.bounds.size.width / 2, cy = self.bounds.size.height / 2;
    CGFloat travel = MIN(self.bounds.size.width, self.bounds.size.height) * 0.29;
    if (travel <= 0) return;
    CGFloat x = (p.x - cx) / travel, y = (p.y - cy) / travel;
    CGFloat length = hypot(x, y);
    if (length > 1) { x /= length; y /= length; }
    if (length < 0.10) x = y = 0;
    _knob.center = CGPointMake(cx + x * travel, cy + y * travel);
    int ax = (int)lrint(x * 32767.0);
    int ay = (int)lrint(-y * 32767.0); // Switch stick Y is positive upward
    if (_left) {
        atomic_store_explicit(&s_lx, ax, memory_order_relaxed);
        atomic_store_explicit(&s_ly, ay, memory_order_relaxed);
    } else {
        if (length >= 0.10) mhgu_touch_camera_drag();
        atomic_store_explicit(&s_rx, ax, memory_order_relaxed);
        atomic_store_explicit(&s_ry, ay, memory_order_relaxed);
    }
}
- (void)touchesBegan:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (_tracked) return;
    UITouch *touch = [touches anyObject];
    if (!touch) return;
    _tracked = [touch retain];
    [self setPosition:[touch locationInView:self]];
}
- (void)touchesMoved:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (_tracked && [touches containsObject:_tracked])
        [self setPosition:[_tracked locationInView:self]];
}
- (void)touchesEnded:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (_tracked && [touches containsObject:_tracked]) [self resetInput];
}
- (void)touchesCancelled:(NSSet *)touches withEvent:(UIEvent *)event {
    [self touchesEnded:touches withEvent:event];
}
- (void)resetInput {
    if (_left && _tracked && _tracked.phase != UITouchPhaseEnded &&
        _tracked.phase != UITouchPhaseCancelled) {
        NSLog(@"[MHGU Touch] MOVE force-reset while finger is still active (phase=%ld)",
              (long)_tracked.phase);
    }
    [_tracked release];
    _tracked = nil;
    [self setPosition:CGPointMake(self.bounds.size.width / 2, self.bounds.size.height / 2)];
}
- (void)dealloc {
    [self resetInput];
    [_knob release];
    [_name release];
    [super dealloc];
}
@end

// The original Android port directly hooks the rendered item HUD. Here the
// gesture surface is a separate UIKit item strip; it sends native L+Y/A (items)
// and L+B/X (ammo) combinations rather than modifying the guest's HUD.
@interface MHGUTouchItemStrip : UIView {
    UITouch *_finger;
    CGPoint _first;
    CGPoint _last;
    BOOL _moved;
    UILabel *_label;
}
- (void)setCaption:(NSString *)caption;
- (void)resetInput;
@end
@implementation MHGUTouchItemStrip
- (id)initWithFrame:(CGRect)frame {
    if (!(self = [super initWithFrame:frame])) return nil;
    self.opaque = NO;
    self.multipleTouchEnabled = YES;
    self.exclusiveTouch = NO;
    self.backgroundColor = hudBackground();
    self.layer.borderColor = [hudGold() colorWithAlphaComponent:.9].CGColor;
    self.layer.borderWidth = 1.25;
    self.layer.cornerRadius = 11;
    _label = [touch_label(@"‹      ITEMS      ›", 13, UIFontWeightSemibold) retain];
    _label.frame = self.bounds;
    _label.autoresizingMask = UIViewAutoresizingFlexibleWidth | UIViewAutoresizingFlexibleHeight;
    _label.textAlignment = NSTextAlignmentCenter;
    [self addSubview:_label];
    return self;
}
- (void)touchesBegan:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (_finger) return;
    UITouch *t = [touches anyObject];
    if (!t) return;
    _finger = [t retain];
    _first = _last = [t locationInView:self];
    _moved = NO;
}
- (void)touchesMoved:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (!_finger || ![touches containsObject:_finger]) return;
    _last = [_finger locationInView:self];
    if (hypot(_last.x - _first.x, _last.y - _first.y) > 15) _moved = YES;
}
- (void)touchesEnded:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (!_finger || ![touches containsObject:_finger]) return;
    CGPoint p = [_finger locationInView:self];
    CGFloat dx = p.x - _first.x, dy = p.y - _first.y;
    [_finger release]; _finger = nil;
    if (hypot(dx, dy) > 19 || _moved) {
        // Vertical swipe switches ammo/coatings; horizontal swipe switches items.
        BOOL ammo = fabs(dy) > fabs(dx) * 1.25;
        CGFloat dist = ammo ? -dy : dx;
        int count = MIN(5, MAX(1, (int)lrint(fabs(dist) / 55.0)));
        if (fabs(dist) >= 19) queue_steps(ammo, (dist > 0 ? 1 : -1) * count);
    } else {
        // V4.3: direct tap zones; faster than repeated swipes. Center uses Y.
        CGFloat x = p.x / MAX(1.0, self.bounds.size.width);
        if (x < 0.33) queue_steps(NO, -1);
        else if (x > 0.67) queue_steps(NO, 1);
        else pulse_button_mask(UINT64_C(1) << BTN_Y, 95);
    }
}
- (void)touchesCancelled:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (_finger && [touches containsObject:_finger]) [self resetInput];
}
- (void)setCaption:(NSString *)caption { _label.text = caption; }
- (void)resetInput { [_finger release]; _finger = nil; _moved = NO; }
- (void)dealloc { [self resetInput]; [_label release]; [super dealloc]; }
@end

@interface MHGUTouchRoot : UIView <UITextFieldDelegate, UIDocumentPickerDelegate> {
    NSMutableArray *_controls;
    MHGUTouchStick *_left, *_right;
    MHGUTouchButton *_button[16];
    MHGUTouchItemStrip *_itemStrip;
    MHGUTouchButton *_fire, *_reload, *_aim, *_special, *_ammoUp, *_ammoDown;
    MHGUTouchButton *_arts[3], *_combo[TOUCH_COMBO_COUNT];
    UIButton *_itemPrevV44, *_itemNextV44, *_itemUseV44;
    int _weaponSetting, _weaponKind, _drawn, _bowType;
    BOOL _lockOn, _cameraSwipe, _artsType3, _newestAttack, _gearOverride;
    CGFloat _cameraSensitivity, _buttonOpacity, _gearOpacity;
    NSInteger _touchVisibility;
    BOOL _controlsHidden;
    UITouch *_cameraFinger;
    CGPoint _cameraPoint;
    NSMutableDictionary *_touchOwnersV441;

    // Keep the existing preference keys and saved layout format.
    NSInteger _profileV44;
    NSMutableDictionary *_namedControls, *_customLayout, *_stylesV44;
    NSMutableSet *_hiddenV44;
    NSArray *_editorNamesV44;

    UIView *_settingsBackdrop, *_settingsPanel, *_settingsContent;
    UIButton *_settingsButton, *_settingsBack, *_settingsDone;
    UILabel *_settingsTitle;
    UISegmentedControl *_settingsTabs;
    UIScrollView *_settingsScroll;
    BOOL _settingsOpen;
    NSString *_settingsControlKey;
    NSURL *_importedHeadingURL;
    NSString *_importedHeadingName;
    BOOL _headingImportFailed;
    CGPoint _buttonListOffset;

    UIView *_layoutToolbar, *_selectionOutline, *_selectedControl;
    UIButton *_layoutCancel, *_layoutReset, *_layoutDock, *_layoutSmaller, *_layoutLarger, *_layoutDone;
    UILabel *_layoutSelection;
    NSDictionary *_layoutBeforeEdit;
    UITouch *_editFinger;
    CGPoint _editPoint;
    BOOL _editing, _layoutDockBottom;

    BOOL _repeatHeldV44[2];
    uint64_t _repeatStartV44[2], _repeatLastV44[2];
    NSTimer *_repeatTimerV44[2];
    UILabel *_hudLabelV44;
    NSTimer *_hudTimerV44;
    BOOL _hudOnV44;
    uint64_t _hudPrevFrameV44, _hudPrevMsV44;
}
- (void)resetAll;
- (void)syncWeapon;
- (void)pollWeapon;
- (void)applyVisibilityV44;
- (void)applyStylesV44;
- (BOOL)applyComboSlot:(NSUInteger)slot text:(NSString *)value;
- (void)saveProfileV44;
- (NSString *)profileStorageKeyV44:(NSString *)kind;
- (void)reloadProfileV44;
- (void)setupSettings;
- (CGRect)safeControlRect;
- (void)snapSettingsGear;
- (void)showGearSettings;
- (void)applyOpacityForKey:(NSString *)key;
- (void)showSettingsPage;
- (void)setSettingsOpen:(BOOL)open;
- (void)layoutToolsInRect:(CGRect)safe;
- (void)updateSelection;
- (void)rememberSelectedPlacement;
- (void)stopItemRepeat:(UIButton *)button;
- (void)updateHudTimer;
@end

@implementation MHGUTouchRoot
- (UIView *)hitTest:(CGPoint)point withEvent:(UIEvent *)event {
    UIView *hit = [super hitTest:point withEvent:event];
    if (!hit || _settingsOpen) return hit;
    if (_editing) return [hit isDescendantOfView:_layoutToolbar] ? hit : self;

    // Deliver all gameplay touches to this view. Each finger keeps its
    // original control even when another finger touches the screen.
    if ([_controls containsObject:hit]) return self;
    if (hit == self)
        return (!_controlsHidden && _cameraSwipe && point.x > self.bounds.size.width * .25) ? self : nil;
    return hit;
}
- (void)addControl:(UIView *)view {
    [self addSubview:view];
    [_controls addObject:view];
}
- (void)named:(NSString *)name view:(UIView *)view {
    if (name && view) [_namedControls setObject:view forKey:name];
}
- (void)addButton:(int)bit text:(NSString *)text {
    MHGUTouchButton *b = [[MHGUTouchButton alloc] initWithLabel:text mask:(UINT64_C(1) << bit)];
    _button[bit] = b;
    if ((UINT64_C(1) << bit) & s_manualAttackMask) [b setManualAttack];
    [self addControl:b];
    [self named:text view:b];
    [b release];
}
- (MHGUTouchButton *)addMaskButton:(uint64_t)mask text:(NSString *)text {
    MHGUTouchButton *b = [[MHGUTouchButton alloc] initWithLabel:text mask:mask];
    [self addControl:b];
    [b release];
    return b;
}
- (id)initWithFrame:(CGRect)frame {
    if (!(self = [super initWithFrame:frame])) return nil;
    self.backgroundColor = [UIColor clearColor];
    self.opaque = NO;
    self.multipleTouchEnabled = YES;
    self.exclusiveTouch = NO;
    self.autoresizingMask = UIViewAutoresizingFlexibleWidth | UIViewAutoresizingFlexibleHeight;
    _controls = [[NSMutableArray alloc] init];
    _touchOwnersV441 = [[NSMutableDictionary alloc] init];
    _namedControls = [[NSMutableDictionary alloc] init];
    NSUserDefaults *profilePrefsV44 = [NSUserDefaults standardUserDefaults];
    _profileV44 = [profilePrefsV44 objectForKey:@"mhgu_touch_active_profile_v44"] ?
                  [profilePrefsV44 integerForKey:@"mhgu_touch_active_profile_v44"] : 2;
    if (_profileV44 < 0 || _profileV44 > 2) _profileV44 = 2;
    [self reloadProfileV44];
    _left = [[MHGUTouchStick alloc] initLeft:YES];
    [self addControl:_left];
    [self named:@"MOVE" view:_left];
    [_left release];
    _right = [[MHGUTouchStick alloc] initLeft:NO];
    [self addControl:_right];
    [self named:@"CAMERA_STICK" view:_right];
    [_right release];

    [self addButton:BTN_A text:@"A"];
    [self addButton:BTN_B text:@"B"];
    [self addButton:BTN_X text:@"X"];
    [self addButton:BTN_Y text:@"Y"];
    [self addButton:BTN_L text:@"L"];
    [self addButton:BTN_R text:@"R"];
    [self addButton:BTN_ZL text:@"ZL"];
    [self addButton:BTN_ZR text:@"ZR"];
    [self addButton:BTN_PLUS text:@"+"];
    [self addButton:BTN_MINUS text:@"−"];
    [self addButton:BTN_UP text:@"▲"];
    [self addButton:BTN_DOWN text:@"▼"];
    [self addButton:BTN_LEFT text:@"◀"];
    [self addButton:BTN_RIGHT text:@"▶"];
    [self addButton:BTN_LSTICK text:@"L3"];
    [self addButton:BTN_RSTICK text:@"R3"];

    // Following gu-native's hunting-first layout: item wheel shortcuts and
    // Hunter Arts have thumb-sized buttons, without game-memory hooks.
    _itemStrip = [[MHGUTouchItemStrip alloc] initWithFrame:CGRectZero];
    [self addControl:_itemStrip];
    [self named:@"ITEM_BAR" view:_itemStrip];
    [_itemStrip release];
    // Dedicated item controls (tap or hold the arrows; use is a single Y pulse).
    _itemPrevV44 = [UIButton buttonWithType:UIButtonTypeCustom];
    _itemNextV44 = [UIButton buttonWithType:UIButtonTypeCustom];
    _itemUseV44 = [UIButton buttonWithType:UIButtonTypeCustom];
    NSArray *itemButtonsV44 = @[_itemPrevV44, _itemUseV44, _itemNextV44];
    NSArray *itemNamesV44 = @[@"ITEM_PREV", @"ITEM_USE", @"ITEM_NEXT"];
    NSArray *itemCaptionsV44 = @[@"‹", @"Use", @"›"];
    for (NSUInteger i=0; i<3; i++) {
        UIButton *b = [itemButtonsV44 objectAtIndex:i];
        mhgu_style_menu(b);
        [b setTitle:[itemCaptionsV44 objectAtIndex:i] forState:UIControlStateNormal];
        [self addControl:b];
        [self named:[itemNamesV44 objectAtIndex:i] view:b];
        b.exclusiveTouch = NO;
    }
    [_itemPrevV44 addTarget:self action:@selector(itemPrevDownV44:)
           forControlEvents:UIControlEventTouchDown];
    [_itemNextV44 addTarget:self action:@selector(itemNextDownV44:)
           forControlEvents:UIControlEventTouchDown];
    [_itemUseV44 addTarget:self action:@selector(itemUseDownV44:)
           forControlEvents:UIControlEventTouchDown];
    UIControlEvents itemEndV44 = UIControlEventTouchUpInside | UIControlEventTouchUpOutside |
                                 UIControlEventTouchCancel | UIControlEventTouchDragExit;
    [_itemPrevV44 addTarget:self action:@selector(stopItemRepeat:) forControlEvents:itemEndV44];
    [_itemNextV44 addTarget:self action:@selector(stopItemRepeat:) forControlEvents:itemEndV44];
    _fire = [self addMaskButton:(UINT64_C(1) << BTN_A) text:@"FIRE"];
    _reload = [self addMaskButton:(UINT64_C(1) << BTN_X) text:@"RELOAD"];
    _aim = [self addMaskButton:(UINT64_C(1) << BTN_R) text:@"AIM"];
    _special = [self addMaskButton:(UINT64_C(1) << BTN_X) | (UINT64_C(1) << BTN_A) text:@"SPECIAL"];
    _ammoUp = [self addMaskButton:(UINT64_C(1) << BTN_L) | (UINT64_C(1) << BTN_X) text:@"AMMO+"];
    _ammoDown = [self addMaskButton:(UINT64_C(1) << BTN_L) | (UINT64_C(1) << BTN_B) text:@"AMMO−"];
    [self named:@"FIRE" view:_fire];
    [self named:@"RELOAD" view:_reload];
    [self named:@"AIM" view:_aim];
    [self named:@"SPECIAL" view:_special];
    [self named:@"AMMO_UP" view:_ammoUp];
    [self named:@"AMMO_DOWN" view:_ammoDown];
    _arts[0] = [self addMaskButton:(UINT64_C(1) << BTN_UP) text:@"ART1"];
    _arts[1] = [self addMaskButton:(UINT64_C(1) << BTN_RIGHT) text:@"ART2"];
    _arts[2] = [self addMaskButton:(UINT64_C(1) << BTN_DOWN) text:@"ART3"];
    for (int i=0; i<3; i++) [self named:[NSString stringWithFormat:@"ART%d",i+1] view:_arts[i]];

    // Two user-defined simultaneous button masks, independent of regular controls.
    for (NSUInteger slot = 0; slot < TOUCH_COMBO_COUNT; slot++) {
        _combo[slot] = [self addMaskButton:0 text:defaultCombo(slot)];
        [_combo[slot] setComboSlot:slot];
        [self named:comboControlKey(slot) view:_combo[slot]];
        if (![self applyComboSlot:slot text:savedCombo(slot)])
            [self applyComboSlot:slot text:defaultCombo(slot)];
    }

    NSUserDefaults *prefs = [NSUserDefaults standardUserDefaults];
    _cameraSwipe = [prefs objectForKey:@"mhgu_touch_camera_swipe"] ?
                   [prefs boolForKey:@"mhgu_touch_camera_swipe"] : YES;
    _artsType3 = [prefs boolForKey:@"mhgu_touch_arts_type3"];
    _newestAttack = [prefs boolForKey:newestAttackKey];
    _weaponSetting = (int)[prefs integerForKey:@"mhgu_touch_weapon_setting"];
    if (_weaponSetting < 0 || _weaponSetting > 3) _weaponSetting = 0;
    _touchVisibility = [prefs integerForKey:@"mhgu_touch_visibility_v45"];
    if (_touchVisibility < 0 || _touchVisibility > 2) _touchVisibility = 0;
    _drawn = -1;
    s_lastWeaponPollMs = 0;
    [self syncWeapon];
    [self updateArtsMapping];

    NSNumber *savedFPS = [prefs objectForKey:@"mhgu_touch_fps_v42"];
    if (savedFPS) config_set_live_fps(savedFPS.floatValue);
    static const CGFloat oldOpacity[] = {.38, .64, .88};
    NSInteger opacityStep = [prefs objectForKey:@"mhgu_touch_opacity_step"] ?
                            [prefs integerForKey:@"mhgu_touch_opacity_step"] : 1;
    if (opacityStep < 0 || opacityStep > 2) opacityStep = 1;
    CGFloat opacity = [prefs objectForKey:@"mhgu_touch_opacity_v43"] ?
                      [prefs doubleForKey:@"mhgu_touch_opacity_v43"] : oldOpacity[opacityStep];
    _buttonOpacity = fmax(.25, fmin(1, opacity));
    CGFloat sensitivity = [prefs objectForKey:@"mhgu_touch_camera_sensitivity_v43"] ?
                          [prefs doubleForKey:@"mhgu_touch_camera_sensitivity_v43"] : 1.65;
    _cameraSensitivity = fmax(.5, fmin(4, sensitivity));
    _hudOnV44 = [prefs boolForKey:@"mhgu_touch_hud_v44"];

    [self setupSettings];
    NSArray *order = @[gearControlKey, @"MOVE", @"CAMERA_STICK", @"A", @"B", @"X", @"Y", @"L", @"R", @"ZL", @"ZR",
                       @"+", @"−", @"▲", @"▼", @"◀", @"▶", @"L3", @"R3",
                       @"FIRE", @"AIM", @"RELOAD", @"SPECIAL", @"AMMO_UP", @"AMMO_DOWN",
                       @"ITEM_PREV", @"ITEM_USE", @"ITEM_NEXT", @"ITEM_BAR",
                       @"ART1", @"ART2", @"ART3", @"COMBO_1", @"COMBO_2"];
    NSMutableArray *names = [NSMutableArray arrayWithCapacity:_namedControls.count];
    for (NSString *key in order)
        if ([_namedControls objectForKey:key]) [names addObject:key];
    for (NSString *key in [[_namedControls allKeys] sortedArrayUsingSelector:@selector(compare:)])
        if (![names containsObject:key]) [names addObject:key];
    _editorNamesV44 = [names copy];

    _hudLabelV44 = [[UILabel alloc] initWithFrame:CGRectZero];
    _hudLabelV44.backgroundColor = [hudBackground() colorWithAlphaComponent:.88];
    _hudLabelV44.layer.cornerRadius = 7;
    _hudLabelV44.layer.masksToBounds = YES;
    _hudLabelV44.textColor = hudCream();
    _hudLabelV44.font = [UIFont monospacedDigitSystemFontOfSize:10 weight:UIFontWeightSemibold];
    _hudLabelV44.numberOfLines = 2;
    _hudLabelV44.userInteractionEnabled = NO;
    _hudLabelV44.text = @"  FPS —   •   BTN —\n  MOVE 0.0,0.0   CAM 0.0,0.0   F:0";
    _hudLabelV44.hidden = !_hudOnV44;
    [self addSubview:_hudLabelV44];
    [self updateHudTimer];
    [self bringSubviewToFront:_settingsBackdrop];
    [self bringSubviewToFront:_layoutToolbar];
    [self applyStylesV44];
    [self applyVisibilityV44];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(controllerChanged:)
                                                 name:GCControllerDidConnectNotification object:nil];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(controllerChanged:)
                                                 name:GCControllerDidDisconnectNotification object:nil];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(appLostFocus:)
                                                 name:UIApplicationWillResignActiveNotification object:nil];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(appBecameActive:)
                                                 name:UIApplicationDidBecomeActiveNotification object:nil];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(settingsKeyboardChanged:)
                                                 name:UIKeyboardWillChangeFrameNotification object:nil];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(settingsKeyboardChanged:)
                                                 name:UIKeyboardWillHideNotification object:nil];
    [self controllerChanged:nil];
    return self;
}
- (void)resetAll {
    [_touchOwnersV441 removeAllObjects];
    for (UIView *view in _controls) [self resetControl:view];
    [_editFinger release];
    _editFinger = nil;
    [self releaseCameraTouch];
    mhgu_touch_clear();
}
- (void)appLostFocus:(NSNotification *)notification {
    (void)notification;
    atomic_store_explicit(&s_iosForeground, 0, memory_order_release);
    [self resetAll];
    [self updateHudTimer];
}
- (void)appBecameActive:(NSNotification *)notification {
    (void)notification;
    atomic_store_explicit(&s_iosForeground, 1, memory_order_release);
    [self updateHudTimer];
}
- (void)didMoveToWindow {
    [super didMoveToWindow];
    [self updateHudTimer];
}
- (void)setupSettings {
    _settingsButton = [[[MHGUGearButton alloc] initWithFrame:CGRectZero] autorelease];
    mhgu_style_menu(_settingsButton);
    [_settingsButton addTarget:self action:@selector(openSettings:) forControlEvents:UIControlEventTouchUpInside];
    UIImage *gear = [UIImage systemImageNamed:@"gearshape"];
    [_settingsButton setImage:gear forState:UIControlStateNormal];
    _settingsButton.tintColor = hudCream();
    _settingsButton.accessibilityLabel = @"Touch controls";
    NSUserDefaults *prefs = [NSUserDefaults standardUserDefaults];
    NSNumber *savedOpacity = [prefs objectForKey:gearOpacityKey];
    NSNumber *override = [prefs objectForKey:gearOverrideKey];
    _gearOpacity = savedOpacity ? fmax(.25, fmin(1, savedOpacity.doubleValue)) : _buttonOpacity;
    _gearOverride = override ? override.boolValue : savedOpacity != nil;
    [self addSubview:_settingsButton];
    [self named:gearControlKey view:_settingsButton];
    NSString *fileName = [prefs stringForKey:headingFontKey];
    if (fileName.length && [fileName isEqualToString:fileName.lastPathComponent]) {
        NSURL *url = [headingFontDirectory() URLByAppendingPathComponent:fileName];
        _importedHeadingName = [registerHeadingFont(url) copy];
        if (_importedHeadingName) _importedHeadingURL = [url retain];
    }

    _settingsBackdrop = [[[UIView alloc] initWithFrame:CGRectZero] autorelease];
    _settingsBackdrop.backgroundColor = [UIColor colorWithWhite:0 alpha:.36];
    _settingsBackdrop.accessibilityViewIsModal = YES;
    _settingsBackdrop.hidden = YES;
    [self addSubview:_settingsBackdrop];
    _settingsPanel = [[[UIView alloc] initWithFrame:CGRectZero] autorelease];
    _settingsPanel.backgroundColor = [UIColor colorWithRed:.09 green:.10 blue:.12 alpha:.98];
    _settingsPanel.layer.cornerRadius = 16;
    _settingsPanel.layer.borderWidth = 1;
    _settingsPanel.layer.borderColor = [hudGold() colorWithAlphaComponent:.36].CGColor;
    _settingsPanel.clipsToBounds = YES;
    [_settingsBackdrop addSubview:_settingsPanel];

    _settingsTitle = touch_label(@"Touch controls", 19, UIFontWeightBold);
    [_settingsPanel addSubview:_settingsTitle];
    _settingsBack = touch_menu_button(@"‹ Buttons", self, @selector(backToButtonList:));
    _settingsBack.accessibilityLabel = @"Back to buttons";
    [_settingsPanel addSubview:_settingsBack];
    _settingsDone = touch_menu_button(@"Done", self, @selector(closeSettings:));
    [_settingsPanel addSubview:_settingsDone];
    _settingsTabs = [self settingsSegments:@[@"Play", @"Layout", @"Buttons"] selected:0 width:330
                                   action:@selector(settingsTabChanged:)];
    [_settingsPanel addSubview:_settingsTabs];

    _settingsScroll = [[[UIScrollView alloc] initWithFrame:CGRectZero] autorelease];
    _settingsScroll.indicatorStyle = UIScrollViewIndicatorStyleWhite;
    _settingsScroll.contentInsetAdjustmentBehavior = UIScrollViewContentInsetAdjustmentNever;
    _settingsScroll.keyboardDismissMode = UIScrollViewKeyboardDismissModeOnDrag;
    [_settingsPanel addSubview:_settingsScroll];
    _settingsContent = [[[UIView alloc] initWithFrame:CGRectZero] autorelease];
    [_settingsScroll addSubview:_settingsContent];

    _selectionOutline = [[[UIView alloc] initWithFrame:CGRectZero] autorelease];
    _selectionOutline.userInteractionEnabled = NO;
    _selectionOutline.hidden = YES;
    _selectionOutline.layer.cornerRadius = 11;
    _selectionOutline.layer.borderWidth = 2;
    _selectionOutline.layer.borderColor = hudGold().CGColor;
    [self addSubview:_selectionOutline];

    _layoutToolbar = [[[UIView alloc] initWithFrame:CGRectZero] autorelease];
    _layoutToolbar.backgroundColor = _settingsPanel.backgroundColor;
    _layoutToolbar.layer.cornerRadius = 12;
    _layoutToolbar.layer.borderWidth = 1;
    _layoutToolbar.layer.borderColor = _settingsPanel.layer.borderColor;
    _layoutToolbar.hidden = YES;
    [self addSubview:_layoutToolbar];

    _layoutSelection = touch_label(nil, 12, UIFontWeightSemibold);
    _layoutSelection.textAlignment = NSTextAlignmentCenter;
    [_layoutToolbar addSubview:_layoutSelection];
    _layoutCancel = touch_menu_button(@"Cancel", self, @selector(cancelLayout:));
    _layoutReset = touch_menu_button(@"Reset", self, @selector(resetLayout:));
    _layoutDock = touch_menu_button(@"⇅", self, @selector(moveLayoutToolbar:));
    _layoutDock.accessibilityLabel = @"Move layout toolbar";
    _layoutSmaller = touch_menu_button(@"−", self, @selector(shrinkSelected:));
    _layoutSmaller.accessibilityLabel = @"Smaller";
    _layoutLarger = touch_menu_button(@"+", self, @selector(growSelected:));
    _layoutLarger.accessibilityLabel = @"Larger";
    _layoutDone = touch_menu_button(@"Save", self, @selector(saveLayout:));
    _layoutDone.backgroundColor = hudPressed();
    for (UIButton *button in @[_layoutCancel, _layoutReset, _layoutDock, _layoutSmaller, _layoutLarger, _layoutDone])
        [_layoutToolbar addSubview:button];
}

- (UISegmentedControl *)settingsSegments:(NSArray<NSString *> *)labels selected:(NSInteger)index
                                   width:(CGFloat)width action:(SEL)action {
    UISegmentedControl *control = [[[UISegmentedControl alloc] initWithItems:labels] autorelease];
    control.bounds = CGRectMake(0, 0, width, 34);
    control.selectedSegmentIndex = index;
    control.backgroundColor = [UIColor colorWithWhite:1 alpha:.09];
    control.selectedSegmentTintColor = hudGold();
    [control setTitleTextAttributes:@{NSForegroundColorAttributeName:hudCream()} forState:UIControlStateNormal];
    [control setTitleTextAttributes:@{NSForegroundColorAttributeName:[UIColor blackColor]} forState:UIControlStateSelected];
    [control addTarget:self action:action forControlEvents:UIControlEventValueChanged];
    return control;
}

- (UISwitch *)settingsSwitch:(BOOL)on action:(SEL)action {
    UISwitch *control = [[[UISwitch alloc] initWithFrame:CGRectZero] autorelease];
    control.on = on;
    control.onTintColor = hudGold();
    [control sizeToFit];
    [control addTarget:self action:action forControlEvents:UIControlEventValueChanged];
    return control;
}

- (UIView *)appendSettingsRow:(NSString *)title accessory:(UIView *)accessory {
    CGFloat width = _settingsScroll.bounds.size.width;
    CGFloat y = _settingsScroll.contentSize.height;
    UIView *row = [[[UIView alloc] initWithFrame:CGRectMake(0, y, width, 48)] autorelease];
    row.autoresizingMask = UIViewAutoresizingFlexibleWidth;
    [_settingsContent addSubview:row];

    CGFloat accessoryWidth = accessory ? MIN(accessory.bounds.size.width, MAX(1, width - 16)) : 0;
    if (accessory) {
        accessory.frame = CGRectMake(width - accessoryWidth - 8, (48 - accessory.bounds.size.height)/2,
                                     accessoryWidth, accessory.bounds.size.height);
        accessory.autoresizingMask = UIViewAutoresizingFlexibleLeftMargin;
        if (title) accessory.accessibilityLabel = title;
        [row addSubview:accessory];
    }
    if (title) {
        UILabel *label = touch_label(title, 14, UIFontWeightMedium);
        label.frame = CGRectMake(8, 0, MAX(1, width - accessoryWidth - 23), 48);
        label.autoresizingMask = UIViewAutoresizingFlexibleWidth;
        [row addSubview:label];
    }
    UIView *line = [[[UIView alloc] initWithFrame:CGRectMake(8, 47, MAX(1, width - 16), 1)] autorelease];
    line.backgroundColor = [UIColor colorWithWhite:1 alpha:.08];
    line.userInteractionEnabled = NO;
    line.autoresizingMask = UIViewAutoresizingFlexibleWidth;
    [row addSubview:line];
    _settingsScroll.contentSize = CGSizeMake(width, y + 48);
    _settingsContent.frame = (CGRect){CGPointZero, _settingsScroll.contentSize};
    return row;
}

- (void)appendSettingsAction:(NSString *)title action:(SEL)action {
    UIView *row = [self appendSettingsRow:nil accessory:nil];
    UIButton *button = touch_menu_button(title, self, action);
    button.frame = CGRectInset(row.bounds, 8, 4);
    button.autoresizingMask = UIViewAutoresizingFlexibleWidth;
    [row addSubview:button];
}

- (void)showSliderValue:(UISlider *)slider percent:(BOOL)percent {
    UILabel *value = (UILabel *)[slider.superview viewWithTag:4501];
    value.text = percent ? [NSString stringWithFormat:@"%.0f%%", slider.value * 100] :
                           [NSString stringWithFormat:@"%.2f×", slider.value];
    slider.accessibilityValue = value.text;
}

- (void)appendSlider:(NSString *)title minimum:(float)minimum maximum:(float)maximum
               value:(float)value percent:(BOOL)percent action:(SEL)action {
    UIView *accessory = [[[UIView alloc] initWithFrame:CGRectMake(0, 0, 162, 42)] autorelease];
    UISlider *slider = [[[UISlider alloc] initWithFrame:CGRectMake(0, 0, 117, 42)] autorelease];
    slider.minimumValue = minimum;
    slider.maximumValue = maximum;
    slider.value = value;
    slider.minimumTrackTintColor = hudGold();
    slider.thumbTintColor = hudCream();
    slider.accessibilityLabel = title;
    slider.autoresizingMask = UIViewAutoresizingFlexibleWidth;
    [slider addTarget:self action:action forControlEvents:UIControlEventValueChanged];
    [accessory addSubview:slider];
    UILabel *number = touch_label(nil, 12, UIFontWeightSemibold);
    number.tag = 4501;
    number.frame = CGRectMake(118, 0, 44, 42);
    number.textAlignment = NSTextAlignmentRight;
    number.autoresizingMask = UIViewAutoresizingFlexibleLeftMargin;
    [accessory addSubview:number];
    [self appendSettingsRow:title accessory:accessory];
    [self showSliderValue:slider percent:percent];
}

- (UITextField *)appendTextField:(NSString *)title text:(NSString *)text action:(SEL)action {
    UITextField *field = [[[UITextField alloc] initWithFrame:CGRectMake(0, 0, 162, 38)] autorelease];
    field.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    field.borderStyle = UITextBorderStyleRoundedRect;
    field.backgroundColor = [UIColor colorWithWhite:1 alpha:.10];
    field.textColor = hudCream();
    field.font = [UIFont systemFontOfSize:15 weight:UIFontWeightMedium];
    field.text = text;
    field.clearButtonMode = UITextFieldViewModeWhileEditing;
    field.returnKeyType = UIReturnKeyDone;
    field.autocorrectionType = UITextAutocorrectionTypeNo;
    field.delegate = self;
    [field addTarget:self action:action forControlEvents:UIControlEventEditingDidEnd];
    [self appendSettingsRow:title accessory:field];
    return field;
}

- (BOOL)textFieldShouldReturn:(UITextField *)field {
    [field resignFirstResponder];
    return YES;
}

- (void)settingsKeyboardChanged:(NSNotification *)notification {
    if (!_settingsOpen || !_settingsControlKey || !self.window) return;

    CGFloat bottomInset = 0;
    NSValue *frame = [notification.userInfo objectForKey:UIKeyboardFrameEndUserInfoKey];
    if (frame && ![notification.name isEqualToString:UIKeyboardWillHideNotification]) {
        CGRect keyboard = [_settingsScroll convertRect:frame.CGRectValue
                                     fromCoordinateSpace:self.window.screen.coordinateSpace];
        CGRect overlap = CGRectIntersection(keyboard, _settingsScroll.bounds);
        if (!CGRectIsEmpty(overlap)) bottomInset = CGRectGetMaxY(_settingsScroll.bounds) - CGRectGetMinY(overlap);
    }
    UIEdgeInsets insets = UIEdgeInsetsMake(0, 0, bottomInset, 0);
    _settingsScroll.contentInset = insets;
    _settingsScroll.verticalScrollIndicatorInsets = insets;
    if (bottomInset <= 0) return;
    for (UIView *row in _settingsContent.subviews) {
        for (UIView *field in row.subviews) {
            if (!field.isFirstResponder) continue;
            CGRect textBox = [field convertRect:field.bounds toView:_settingsScroll];
            [_settingsScroll scrollRectToVisible:CGRectInset(textBox, 0, -5) animated:YES];
            return;
        }
    }
}

- (void)layoutToolsInRect:(CGRect)safe {
    CGFloat left = CGRectGetMinX(safe), top = CGRectGetMinY(safe);
    CGFloat width = MIN(382, MAX(1, safe.size.width - 16));
    CGFloat height = MIN(435, MAX(1, safe.size.height - 12));
    _settingsBackdrop.frame = self.bounds;
    _settingsPanel.frame = CGRectMake(left + 8, CGRectGetMidY(safe) - height/2, width, height);

    BOOL detail = _settingsControlKey != nil;
    CGFloat titleX = detail ? 78 : 16;
    _settingsTitle.frame = CGRectMake(titleX, 5, MAX(1, width - titleX - 73), 40);
    _settingsBack.frame = CGRectMake(8, 6, 64, 36);
    _settingsDone.frame = CGRectMake(width - 64, 6, 56, 36);
    _settingsTabs.frame = CGRectMake(8, 50, MAX(1, width - 16), 34);
    CGFloat bodyTop = detail ? 47 : 90;
    _settingsScroll.frame = CGRectMake(4, bodyTop, MAX(1, width - 8), MAX(1, height - bodyTop - 6));
    _settingsScroll.contentSize = CGSizeMake(_settingsScroll.bounds.size.width, _settingsScroll.contentSize.height);
    _settingsContent.frame = (CGRect){CGPointZero, _settingsScroll.contentSize};

    CGFloat toolbarWidth = MIN(safe.size.width - 12, 377);
    CGFloat dockY = _layoutDockBottom ? CGRectGetMaxY(safe) - 74 : top + 6;
    _layoutToolbar.frame = CGRectMake(CGRectGetMidX(safe) - toolbarWidth/2, dockY, toolbarWidth, 68);
    _layoutSelection.frame = CGRectMake(8, 1, toolbarWidth - 16, 20);
    NSArray *tools = @[_layoutCancel, _layoutReset, _layoutDock, _layoutSmaller, _layoutLarger, _layoutDone];
    CGFloat slot = (toolbarWidth - 10) / tools.count;
    for (NSUInteger i = 0; i < tools.count; i++) {
        UIButton *button = [tools objectAtIndex:i];
        button.frame = CGRectMake(5 + i * slot, 22, slot - 4, 40);
    }
    [self updateSelection];
}

- (void)setSettingsOpen:(BOOL)open {
    if (open) [self resetAll];
    else [self endEditing:YES];
    _settingsOpen = open;
    _settingsBackdrop.hidden = !open;
    _settingsButton.hidden = open;
    if (open) [self showSettingsPage];
    else {
        _settingsScroll.contentInset = UIEdgeInsetsZero;
        _settingsScroll.verticalScrollIndicatorInsets = UIEdgeInsetsZero;
    }
    [self updateHudTimer];
}

- (void)openSettings:(id)sender { (void)sender; [self setSettingsOpen:YES]; }
- (void)closeSettings:(id)sender { (void)sender; [self setSettingsOpen:NO]; }

- (void)settingsTabChanged:(UISegmentedControl *)sender {
    (void)sender;
    [self showSettingsPage];
}

- (void)refreshControlsVisibility {
    BOOL hidden = _touchVisibility == 2 || (_touchVisibility == 0 && [GCController controllers].count != 0);
    if (hidden == _controlsHidden) return;
    _controlsHidden = hidden;
    if (hidden) {
        [self resetAll];
        _lockOn = NO;
        mhgu_touch_lock_enable(0);
    }
    [self applyVisibilityV44];
    if (_settingsOpen && _settingsTabs.selectedSegmentIndex == 0) [self showSettingsPage];
}

- (void)touchVisibilityChanged:(UISegmentedControl *)sender {
    _touchVisibility = sender.selectedSegmentIndex;
    [[NSUserDefaults standardUserDefaults] setInteger:_touchVisibility forKey:@"mhgu_touch_visibility_v45"];
    [self refreshControlsVisibility];
}
- (void)cameraModeChanged:(UISegmentedControl *)sender {
    _cameraSwipe = sender.selectedSegmentIndex == 0;
    [[NSUserDefaults standardUserDefaults] setBool:_cameraSwipe forKey:@"mhgu_touch_camera_swipe"];
    [self applyVisibilityV44];
}
- (void)weaponModeChanged:(UISegmentedControl *)sender {
    _weaponSetting = (int)sender.selectedSegmentIndex;
    [[NSUserDefaults standardUserDefaults] setInteger:_weaponSetting forKey:@"mhgu_touch_weapon_setting"];
    s_lastWeaponPollMs = 0;
    [self syncWeapon];
}
- (void)artsModeChanged:(UISegmentedControl *)sender {
    _artsType3 = sender.selectedSegmentIndex == 1;
    [[NSUserDefaults standardUserDefaults] setBool:_artsType3 forKey:@"mhgu_touch_arts_type3"];
    [self updateArtsMapping];
}
- (void)newestAttackChanged:(UISwitch *)sender {
    [self resetAll];
    _newestAttack = sender.isOn;
    [[NSUserDefaults standardUserDefaults] setBool:_newestAttack forKey:newestAttackKey];
}
- (void)openForge:(id)sender {
    (void)sender;
    [self setSettingsOpen:NO];
    overlay_toggle_forge();
}
- (void)cameraSensitivityChanged:(UISlider *)sender {
    _cameraSensitivity = sender.value;
    [[NSUserDefaults standardUserDefaults] setFloat:sender.value forKey:@"mhgu_touch_camera_sensitivity_v43"];
    [self showSliderValue:sender percent:NO];
}
- (void)lockChanged:(UISwitch *)sender {
    _lockOn = mhgu_touch_lock_available() && sender.isOn;
    mhgu_touch_lock_enable(_lockOn);
    sender.on = _lockOn;
}
- (void)fpsTargetChanged:(UISegmentedControl *)sender {
    NSInteger index = sender.selectedSegmentIndex;
    if (index < 0 || index > 3) return;
    int fps = 30 * ((int)index + 1);
    config_set_live_fps((float)fps);
    [[NSUserDefaults standardUserDefaults] setInteger:fps forKey:@"mhgu_touch_fps_v42"];
}
- (void)hudChanged:(UISwitch *)sender {
    _hudOnV44 = sender.isOn;
    [[NSUserDefaults standardUserDefaults] setBool:_hudOnV44 forKey:@"mhgu_touch_hud_v44"];
    [self updateHudTimer];
}
- (void)globalOpacityChanged:(UISlider *)sender {
    _buttonOpacity = sender.value;
    [[NSUserDefaults standardUserDefaults] setFloat:sender.value forKey:@"mhgu_touch_opacity_v43"];
    [self updateOpacity];
    [self showSliderValue:sender percent:YES];
}
- (void)gearOpacityChanged:(UISlider *)sender {
    _gearOpacity = sender.value;
    [[NSUserDefaults standardUserDefaults] setFloat:sender.value forKey:gearOpacityKey];
    [self applyOpacityForKey:gearControlKey];
    [self showSliderValue:sender percent:YES];
}
- (void)gearFollowsOpacityChanged:(UISwitch *)sender {
    _gearOverride = !sender.isOn;
    [[NSUserDefaults standardUserDefaults] setBool:_gearOverride forKey:gearOverrideKey];
    [self applyOpacityForKey:gearControlKey];
    [self showSettingsPage];
}
- (void)openGearSettings:(id)sender {
    (void)sender;
    [_settingsControlKey release];
    _settingsControlKey = [gearControlKey copy];
    [self showSettingsPage];
}
- (void)resetGear:(id)sender {
    (void)sender;
    [_customLayout removeObjectForKey:gearControlKey];
    _gearOpacity = _buttonOpacity;
    _gearOverride = NO;
    NSUserDefaults *prefs = [NSUserDefaults standardUserDefaults];
    [prefs removeObjectForKey:gearOpacityKey];
    [prefs removeObjectForKey:gearOverrideKey];
    [self saveProfileV44];
    [self applyOpacityForKey:gearControlKey];
    [self setNeedsLayout];
    [self showSettingsPage];
}
- (void)showGearSettings {
    [self appendSettingsRow:@"Follow gameplay opacity" accessory:[self settingsSwitch:!_gearOverride
                                                                         action:@selector(gearFollowsOpacityChanged:)]];
    if (_gearOverride)
        [self appendSlider:@"Gear opacity" minimum:.25 maximum:1 value:_gearOpacity percent:YES
                    action:@selector(gearOpacityChanged:)];
    [self appendSettingsAction:@"Move & resize" action:@selector(moveSelectedControl:)];
    [self appendSettingsAction:@"Reset gear" action:@selector(resetGear:)];
}

- (void)pickHeadingFont:(id)sender {
    (void)sender;
    UIViewController *controller = self.window.rootViewController;
    if (!controller || controller.presentedViewController) return;
    UIDocumentPickerViewController *picker = [[[UIDocumentPickerViewController alloc]
        initForOpeningContentTypes:@[UTTypeFont] asCopy:YES] autorelease];
    picker.delegate = self;
    [controller presentViewController:picker animated:YES completion:nil];
}

- (BOOL)installHeadingFont:(NSURL *)source {
    NSString *extension = source.pathExtension.lowercaseString;
    if (![extension isEqualToString:@"ttf"] && ![extension isEqualToString:@"otf"]) return NO;
    NSURL *directory = headingFontDirectory();
    NSFileManager *files = [NSFileManager defaultManager];
    if (!directory || ![files createDirectoryAtURL:directory withIntermediateDirectories:YES attributes:nil error:NULL])
        return NO;
    NSString *fileName = [[[NSUUID UUID] UUIDString] stringByAppendingPathExtension:extension];
    NSURL *destination = [directory URLByAppendingPathComponent:fileName];
    BOOL accessed = [source startAccessingSecurityScopedResource];
    BOOL copied = [files copyItemAtURL:source toURL:destination error:NULL];
    if (accessed) [source stopAccessingSecurityScopedResource];
    if (!copied) {
        [files removeItemAtURL:destination error:NULL];
        return NO;
    }

    if (_importedHeadingURL)
        CTFontManagerUnregisterFontsForURL((__bridge CFURLRef)_importedHeadingURL, kCTFontManagerScopeProcess, NULL);
    NSString *name = registerHeadingFont(destination);
    if (!name) {
        if (_importedHeadingURL) registerHeadingFont(_importedHeadingURL);
        [files removeItemAtURL:destination error:NULL];
        return NO;
    }

    [[NSUserDefaults standardUserDefaults] setObject:fileName forKey:headingFontKey];
    if (_importedHeadingURL) [files removeItemAtURL:_importedHeadingURL error:NULL];
    [_importedHeadingURL release];
    [_importedHeadingName release];
    _importedHeadingURL = [destination retain];
    _importedHeadingName = [name copy];
    return YES;
}

- (void)documentPicker:(UIDocumentPickerViewController *)picker didPickDocumentsAtURLs:(NSArray<NSURL *> *)urls {
    (void)picker;
    _headingImportFailed = ![self installHeadingFont:urls.firstObject];
    [self showSettingsPage];
}

- (void)useCinzelHeadingFont:(id)sender {
    (void)sender;
    if (_importedHeadingURL) {
        CTFontManagerUnregisterFontsForURL((__bridge CFURLRef)_importedHeadingURL, kCTFontManagerScopeProcess, NULL);
        [[NSFileManager defaultManager] removeItemAtURL:_importedHeadingURL error:NULL];
    }
    [[NSUserDefaults standardUserDefaults] removeObjectForKey:headingFontKey];
    [_importedHeadingURL release];
    [_importedHeadingName release];
    _importedHeadingURL = nil;
    _importedHeadingName = nil;
    _headingImportFailed = NO;
    [self showSettingsPage];
}

- (void)showPlaySettings {
    [self appendSettingsRow:@"Touch controls" accessory:
        [self settingsSegments:@[@"Auto", @"On", @"Off"] selected:_touchVisibility width:152
                         action:@selector(touchVisibilityChanged:)]];
    [self appendSettingsRow:@"Newest A/X/Y wins" accessory:[self settingsSwitch:_newestAttack
                                                                       action:@selector(newestAttackChanged:)]];
    [self appendSettingsRow:@"Camera" accessory:
        [self settingsSegments:@[@"Swipe", @"Stick"] selected:_cameraSwipe ? 0 : 1 width:141
                         action:@selector(cameraModeChanged:)]];
    [self appendSlider:@"Camera sensitivity" minimum:.5 maximum:4 value:_cameraSensitivity percent:NO
                action:@selector(cameraSensitivityChanged:)];
    [self appendSettingsRow:@"Weapon buttons" accessory:
        [self settingsSegments:@[@"Auto", @"Gun", @"Bow", @"Melee"] selected:_weaponSetting width:177
                         action:@selector(weaponModeChanged:)]];
    [self appendSettingsRow:@"Hunter Arts" accessory:
        [self settingsSegments:@[@"Type 1", @"Type 3"] selected:_artsType3 ? 1 : 0 width:141
                         action:@selector(artsModeChanged:)]];
    UISwitch *lock = [self settingsSwitch:_lockOn action:@selector(lockChanged:)];
    lock.enabled = mhgu_touch_lock_available() != 0;
    [self appendSettingsRow:(lock.enabled ? @"Camera lock-on" : @"Lock-on unavailable") accessory:lock];
    int target = (int)lroundf(config_live_fps());
    NSInteger fpsIndex = target >= 30 && target <= 120 && target % 30 == 0 ? target/30 - 1 : -1;
    [self appendSettingsRow:@"FPS target" accessory:
        [self settingsSegments:@[@"30", @"60", @"90", @"120"] selected:fpsIndex width:162
                         action:@selector(fpsTargetChanged:)]];
    [self appendSettingsRow:@"FPS and input HUD" accessory:[self settingsSwitch:_hudOnV44 action:@selector(hudChanged:)]];
    if (overlay_enabled()) [self appendSettingsAction:@"Forge menu" action:@selector(openForge:)];
}
- (void)showLayoutSettings {
    [self appendSettingsRow:@"Profile" accessory:
        [self settingsSegments:@[@"Melee", @"Ranged", @"Custom"] selected:_profileV44 width:196
                         action:@selector(profileChanged:)]];
    [self appendSlider:@"Gameplay opacity" minimum:.25 maximum:1 value:_buttonOpacity percent:YES
                action:@selector(globalOpacityChanged:)];
    [self appendSettingsAction:@"Edit layout" action:@selector(openLayoutEditor:)];
    [self appendSettingsAction:@"Settings gear" action:@selector(openGearSettings:)];
    [self appendSettingsAction:@"Import heading font" action:@selector(pickHeadingFont:)];
    if (_headingImportFailed) [self appendSettingsRow:@"Couldn’t load the selected .ttf or .otf." accessory:nil];
    if (_importedHeadingName) [self appendSettingsAction:@"Use Cinzel headings" action:@selector(useCinzelHeadingFont:)];
}

- (void)showSettingsPage {
    BOOL detail = _settingsControlKey != nil;
    _settingsBack.hidden = !detail;
    _settingsTabs.hidden = detail;
    _settingsTitle.text = detail ? [self controlTitle:_settingsControlKey] : @"Touch controls";
    _settingsTitle.font = touchHeadingFont(_importedHeadingName);
    [self layoutToolsInRect:[self safeControlRect]];
    for (UIView *view in [[_settingsContent.subviews copy] autorelease]) [view removeFromSuperview];
    _settingsScroll.contentInset = UIEdgeInsetsZero;
    _settingsScroll.verticalScrollIndicatorInsets = UIEdgeInsetsZero;
    _settingsScroll.contentSize = CGSizeZero;

    if ([_settingsControlKey isEqualToString:gearControlKey]) [self showGearSettings];
    else if (detail) [self showButtonSettings];
    else if (_settingsTabs.selectedSegmentIndex == 1) [self showLayoutSettings];
    else if (_settingsTabs.selectedSegmentIndex == 2) [self showButtonList];
    else [self showPlaySettings];

    CGPoint offset = CGPointZero;
    if (!detail && _settingsTabs.selectedSegmentIndex == 2) {
        CGFloat maxY = MAX(0, _settingsScroll.contentSize.height - _settingsScroll.bounds.size.height);
        offset.y = MAX(0, MIN(_buttonListOffset.y, maxY));
    }
    [_settingsScroll setContentOffset:offset animated:NO];
}

- (uint64_t)comboBit:(NSString *)part {
    static const int bits[] = {BTN_A, BTN_B, BTN_X, BTN_Y, BTN_L, BTN_R, BTN_ZL, BTN_ZR,
                               BTN_PLUS, BTN_MINUS};
    NSArray *names = comboNames();
    for (NSUInteger i=0; i<names.count; i++)
        if ([part isEqualToString:[names objectAtIndex:i]]) return UINT64_C(1) << bits[i];
    return 0;
}
- (BOOL)applyComboSlot:(NSUInteger)slot text:(NSString *)value {
    if (slot >= TOUCH_COMBO_COUNT || !value) return NO;
    NSString *clean = [[[value uppercaseString] stringByReplacingOccurrencesOfString:@" " withString:@""]
                       stringByReplacingOccurrencesOfString:@"＋" withString:@"+"];
    NSArray *parts = [clean componentsSeparatedByString:@"+"];
    if (parts.count != 2) return NO;
    NSCharacterSet *spaces = [NSCharacterSet whitespaceAndNewlineCharacterSet];
    NSString *left = [[parts objectAtIndex:0] stringByTrimmingCharactersInSet:spaces];
    NSString *right = [[parts objectAtIndex:1] stringByTrimmingCharactersInSet:spaces];
    uint64_t a = [self comboBit:left], b = [self comboBit:right];
    if (!a || !b || a == b) return NO;
    NSString *display = [NSString stringWithFormat:@"%@+%@", left, right];
    [_combo[slot] setMask:a | b];
    [_combo[slot] setCaption:display];
    [[NSUserDefaults standardUserDefaults] setObject:display forKey:comboPreference(slot)];
    return YES;
}
- (void)updateArtsMapping {
    uint64_t masks[3];
    if (_artsType3) {
        masks[0] = (UINT64_C(1) << BTN_ZL) | (UINT64_C(1) << BTN_X);
        masks[1] = (UINT64_C(1) << BTN_ZL) | (UINT64_C(1) << BTN_A);
        masks[2] = (UINT64_C(1) << BTN_ZL) | (UINT64_C(1) << BTN_B);
    } else {
        masks[0] = UINT64_C(1) << BTN_UP;
        masks[1] = UINT64_C(1) << BTN_RIGHT;
        masks[2] = UINT64_C(1) << BTN_DOWN;
    }
    for (int i = 0; i < 3; i++) [_arts[i] setMask:masks[i]];
}
- (void)prioritizeAttack:(UIView *)target {
    if (target != _button[BTN_A] && target != _button[BTN_X] && target != _button[BTN_Y]) return;
    const int attackBits[] = {BTN_A, BTN_X, BTN_Y};
    for (NSUInteger i = 0; i < sizeof attackBits / sizeof attackBits[0]; i++) {
        MHGUTouchButton *button = _button[attackBits[i]];
        // Keep UIKit's ownership until release, but require a new down event to press again.
        if (button != target) [button resetInput];
    }
}
- (void)touchesBegan:(NSSet *)touches withEvent:(UIEvent *)event {
    if (_editing) {
        if (_editFinger) return;
        UITouch *touch = [touches anyObject];
        if (!touch) return;
        CGPoint point = [touch locationInView:self];
        UIView *selected = _selectedControl;
        CGRect gearArea = gearHitRect(_settingsButton.frame);
        if (!selected || !CGRectContainsPoint(selected == _settingsButton ? gearArea : selected.frame, point)) {
            selected = nil;
            if (CGRectContainsPoint(gearArea, point)) selected = _settingsButton;
            else for (UIView *view in [_controls reverseObjectEnumerator]) {
                if (view.hidden || !CGRectContainsPoint(view.frame, point)) continue;
                selected = view;
                break;
            }
        }
        _selectedControl = selected;
        [self applyVisibilityV44];
        [self updateSelection];
        if (selected) {
            _editFinger = [touch retain];
            _editPoint = point;
        }
        return;
    }
    if (_settingsOpen || _controlsHidden) return;

    BOOL prioritize = _newestAttack && !overlay_menu_open();
    id<NSFastEnumeration> orderedTouches = touches;
    if (prioritize && touches.count > 1) {
        orderedTouches = [touches.allObjects sortedArrayUsingComparator:^NSComparisonResult(UITouch *a, UITouch *b) {
            if (a.timestamp < b.timestamp) return NSOrderedAscending;
            return a.timestamp > b.timestamp ? NSOrderedDescending : NSOrderedSame;
        }];
    }
    UITouch *cameraTouch = nil;
    for (UITouch *finger in orderedTouches) {
        CGPoint point = [finger locationInView:self];
        UIView *target = [super hitTest:point withEvent:event];
        if (target && [_controls containsObject:target]) {
            if (prioritize) [self prioritizeAttack:target];
            BOOL item = [target isKindOfClass:[UIButton class]];
            BOOL alreadyHeld = item && [_touchOwnersV441 allKeysForObject:target].count != 0;
            [_touchOwnersV441 setObject:target forKey:[NSValue valueWithNonretainedObject:finger]];
            if (!item) [target touchesBegan:[NSSet setWithObject:finger] withEvent:event];
            else if (!alreadyHeld) {
                UIButton *button = (UIButton *)target;
                button.highlighted = YES;
                [button sendActionsForControlEvents:UIControlEventTouchDown];
            }
        } else if (target == self && !cameraTouch && point.x > self.bounds.size.width * .25) {
            cameraTouch = finger;
        }
    }
    if (!_cameraSwipe || _cameraFinger || !cameraTouch) return;
    if (cameraTouch.tapCount >= 2) {
        atomic_store_explicit(&s_centerCameraUntilMs, mhgu_now_ms() + 100, memory_order_relaxed);
        return;
    }
    _cameraFinger = [cameraTouch retain];
    _cameraPoint = [cameraTouch locationInView:self];
}

- (void)touchesMoved:(NSSet *)touches withEvent:(UIEvent *)event {
    (void)event;
    if (_editing) {
        if (_editFinger && [touches containsObject:_editFinger] && _selectedControl) {
            CGPoint p = [_editFinger locationInView:self];
            CGPoint center = _selectedControl.center;
            center.x += p.x - _editPoint.x;
            center.y += p.y - _editPoint.y;
            [self placeView:_selectedControl center:center size:_selectedControl.bounds.size
                     inRect:[self safeControlRect]];
            [self rememberSelectedPlacement];
            [self updateSelection];
            _editPoint = p;
        }
        return;
    }
    for (UITouch *finger in touches) {
        UIView *target = [_touchOwnersV441 objectForKey:[NSValue valueWithNonretainedObject:finger]];
        if (target && ![target isKindOfClass:[UIButton class]])
            [target touchesMoved:[NSSet setWithObject:finger] withEvent:event];
    }
    if (!_cameraFinger || ![touches containsObject:_cameraFinger]) return;
    CGPoint p = [_cameraFinger locationInView:self];
    mhgu_touch_camera_drag();
    CGFloat dx = p.x - _cameraPoint.x, dy = p.y - _cameraPoint.y;
    _cameraPoint = p;
    // Game's right-stick camera has a ~40% dead zone. Lift small swipes
    // above that dead zone while still scaling from slow to quick drags.
    CGFloat vx = fmin(1.0, fabs(dx) * _cameraSensitivity / 12.0);
    CGFloat vy = fmin(1.0, fabs(dy) * _cameraSensitivity / 12.0);
    int ax = fabs(dx) < 0.4 / _cameraSensitivity ? 0 : (int)lrint(copysign(32767.0 * (0.43 + 0.57 * vx), dx));
    int ay = fabs(dy) < 0.4 / _cameraSensitivity ? 0 : (int)lrint(copysign(32767.0 * (0.43 + 0.57 * vy), -dy));
    atomic_store_explicit(&s_swipeRx, ax, memory_order_relaxed);
    atomic_store_explicit(&s_swipeRy, ay, memory_order_relaxed);
    atomic_store_explicit(&s_lastSwipeMs, mhgu_now_ms(), memory_order_relaxed);
}
- (void)releaseCameraTouch {
    [_cameraFinger release];
    _cameraFinger = nil;
    atomic_store_explicit(&s_lastSwipeMs, 0, memory_order_relaxed);
    atomic_store_explicit(&s_swipeRx, 0, memory_order_relaxed);
    atomic_store_explicit(&s_swipeRy, 0, memory_order_relaxed);
}

- (void)finishTouches:(NSSet *)touches withEvent:(UIEvent *)event cancelled:(BOOL)cancelled {
    if (_editing) {
        if (_editFinger && [touches containsObject:_editFinger]) {
            if (!cancelled && _selectedControl == _settingsButton) [self snapSettingsGear];
            [self rememberSelectedPlacement];
            [self updateSelection];
            [_editFinger release];
            _editFinger = nil;
        }
        return;
    }
    for (UITouch *finger in touches) {
        NSValue *key = [NSValue valueWithNonretainedObject:finger];
        UIView *target = [_touchOwnersV441 objectForKey:key];
        if (!target) continue;
        // The view hierarchy retains the target after removing its owner.
        [_touchOwnersV441 removeObjectForKey:key];
        if ([target isKindOfClass:[UIButton class]]) {
            if ([_touchOwnersV441 allKeysForObject:target].count == 0) {
                UIButton *button = (UIButton *)target;
                button.highlighted = NO;
                UIControlEvents action = cancelled ? UIControlEventTouchCancel : UIControlEventTouchUpInside;
                [button sendActionsForControlEvents:action];
            }
        } else if (cancelled) {
            [target touchesCancelled:[NSSet setWithObject:finger] withEvent:event];
        } else {
            [target touchesEnded:[NSSet setWithObject:finger] withEvent:event];
        }
    }
    if (_cameraFinger && [touches containsObject:_cameraFinger]) [self releaseCameraTouch];
}
- (void)touchesEnded:(NSSet *)touches withEvent:(UIEvent *)event {
    [self finishTouches:touches withEvent:event cancelled:NO];
}
- (void)touchesCancelled:(NSSet *)touches withEvent:(UIEvent *)event {
    [self finishTouches:touches withEvent:event cancelled:YES];
}
- (void)controllerChanged:(NSNotification *)notification {
    (void)notification;
    if (![NSThread isMainThread]) {
        dispatch_async(dispatch_get_main_queue(), ^{ [self refreshControlsVisibility]; });
        return;
    }
    [self refreshControlsVisibility];
}

- (CGRect)safeControlRect {
    CGRect safe = UIEdgeInsetsInsetRect(self.bounds, self.safeAreaInsets);
    return CGRectIsEmpty(safe) ? self.bounds : safe;
}

- (void)placeView:(UIView *)view center:(CGPoint)center size:(CGSize)size inRect:(CGRect)safe {
    if (size.width <= 0 || size.height <= 0 || CGRectIsEmpty(safe)) return;
    CGFloat fit = MIN(1, MIN(safe.size.width / size.width, safe.size.height / size.height));
    size.width *= fit;
    size.height *= fit;
    CGFloat halfW = size.width / 2, halfH = size.height / 2;
    if (view == _settingsButton) {
        halfW = MIN(safe.size.width, MAX(minimumGearHitSize, size.width)) / 2;
        halfH = MIN(safe.size.height, MAX(minimumGearHitSize, size.height)) / 2;
    }
    center.x = MAX(CGRectGetMinX(safe) + halfW, MIN(CGRectGetMaxX(safe) - halfW, center.x));
    center.y = MAX(CGRectGetMinY(safe) + halfH, MIN(CGRectGetMaxY(safe) - halfH, center.y));
    view.bounds = (CGRect){CGPointZero, size};
    view.center = center;
}

- (void)snapSettingsGear {
    CGRect safe = [self safeControlRect];
    CGRect hit = gearHitRect(_settingsButton.frame);
    CGFloat xMargin = hit.size.width / 2 + 4, yMargin = hit.size.height / 2 + 4;
    if (xMargin * 2 > safe.size.width || yMargin * 2 > safe.size.height) return;
    CGPoint center = _settingsButton.center;
    CGPoint corner = CGPointMake(center.x < CGRectGetMidX(safe) ? CGRectGetMinX(safe) + xMargin : CGRectGetMaxX(safe) - xMargin,
                                 center.y < CGRectGetMidY(safe) ? CGRectGetMinY(safe) + yMargin : CGRectGetMaxY(safe) - yMargin);
    CGFloat dx = corner.x - center.x, dy = corner.y - center.y;
    if (hypot(dx, dy) > 36) return;
    CGRect snappedHit = CGRectOffset(hit, dx, dy);
    for (UIView *control in _controls)
        if (!control.hidden && CGRectIntersectsRect(snappedHit, control.frame)) return;
    [self placeView:_settingsButton center:corner size:_settingsButton.bounds.size inRect:safe];
}

- (void)safeAreaInsetsDidChange {
    [super safeAreaInsetsDidChange];
    [self setNeedsLayout];
}

- (void)layoutGameplayInRect:(CGRect)safe {
    // Place grouped controls in points so the middle of the game stays clear.
    CGFloat scale = MIN(1.35, MIN(safe.size.width / 650.0, safe.size.height / 338.0));
    CGFloat x = CGRectGetMinX(safe), y = CGRectGetMinY(safe);
    CGFloat right = safe.size.width / scale;
    CGFloat bottom = safe.size.height / scale;
    CGFloat mid = right / 2;
    CGFloat aimX = _profileV44 == 1 ? right - 124 : right - 115;
    struct { UIView *view; CGFloat x, y, w, h; } positions[] = {
        {_settingsButton, 27, 28, 32, 32},
        {_button[BTN_L], 80, 28, 46, 42}, {_button[BTN_ZL], 132, 28, 46, 42},
        {_button[BTN_R], right - 29, 28, 46, 42}, {_button[BTN_ZR], right - 81, 28, 46, 42},
        {_button[BTN_MINUS], mid - 27, 28, 43, 42}, {_button[BTN_PLUS], mid + 27, 28, 43, 42},

        {_left, 60, bottom - 60, 100, 100},
        {_right, right - 200, bottom - 64, 94, 94},
        {_button[BTN_UP], 169, bottom - 101, 38, 38},
        {_button[BTN_DOWN], 169, bottom - 25, 38, 38},
        {_button[BTN_LEFT], 131, bottom - 63, 38, 38},
        {_button[BTN_RIGHT], 207, bottom - 63, 38, 38},
        {_button[BTN_LSTICK], 61, bottom - 134, 40, 38},
        {_button[BTN_RSTICK], right - 214, bottom - 138, 40, 38},

        {_button[BTN_A], right - 34, bottom - 94, 52, 52},
        {_button[BTN_B], right - 54, bottom - 38, 50, 50},
        {_button[BTN_X], right - 89, bottom - 137, 48, 48},
        {_button[BTN_Y], right - 113, bottom - 86, 44, 44},
        {_fire, right - 34, bottom - 94, 56, 54},
        {_aim, aimX, bottom - 90, 48, 44},
        {_reload, right - 89, bottom - 140, 47, 43},
        {_special, right - 141, bottom - 143, 47, 40},
        {_ammoDown, mid + 55, 84, 45, 38}, {_ammoUp, mid + 106, 84, 45, 38},

        {_combo[0], mid - 72, 84, 44, 38}, {_combo[1], mid - 23, 84, 44, 38},
        {_arts[0], right - 131, 84, 43, 38}, {_arts[1], right - 82, 84, 43, 38},
        {_arts[2], right - 33, 84, 43, 38},
        {_itemPrevV44, mid - 52, bottom - 27, 43, 39},
        {_itemUseV44, mid, bottom - 27, 54, 39},
        {_itemNextV44, mid + 52, bottom - 27, 43, 39},
        {_itemStrip, mid, bottom - 72, 148, 34},
    };
    for (NSUInteger i = 0; i < sizeof positions / sizeof positions[0]; i++) {
        CGPoint center = CGPointMake(x + positions[i].x * scale, y + positions[i].y * scale);
        CGSize size = CGSizeMake(positions[i].w * scale, positions[i].h * scale);
        [self placeView:positions[i].view center:center size:size inRect:safe];
    }
    _hudLabelV44.font = [UIFont monospacedDigitSystemFontOfSize:9.2 * scale weight:UIFontWeightSemibold];
    _hudLabelV44.frame = CGRectMake(x + 8 * scale, y + 61 * scale, 220 * scale, 42 * scale);
}
- (void)layoutSubviews {
    [super layoutSubviews];
    CGRect safe = [self safeControlRect];
    if (safe.size.width < 100 || safe.size.height < 100) return;
    [self layoutGameplayInRect:safe];
    [self applyCustomLayout];
    if (_settingsOpen || _editing) [self layoutToolsInRect:safe];
}
- (void)pollWeapon {
    if (!_controlsHidden && !_settingsOpen && !_editing && mhgu_ios_is_foreground() && !overlay_menu_open())
        [self syncWeapon];
}
- (void)syncWeapon {
    uint64_t now = mhgu_now_ms();
    if (s_lastWeaponPollMs && now - s_lastWeaponPollMs < 160) return;
    s_lastWeaponPollMs = now;
    int detectedDrawn = -1, detectedBowType = 0;
    int detected = _weaponSetting == 3 ? 0 : mhgu_touch_detect_weapon(&detectedDrawn, &detectedBowType);
    int kind = _weaponSetting == 0 ? detected : (_weaponSetting == 1 ? 2 : _weaponSetting == 2 ? 1 : 0);
    if (kind == _weaponKind && detectedDrawn == _drawn && detectedBowType == _bowType) return;
    BOOL rangedChanged = (kind != 0) != (_weaponKind != 0);
    _weaponKind = kind; _drawn = detectedDrawn; _bowType = detectedBowType;
    // MHGU 1.4.0: bowgun A fires, X reloads, R aims; bow X charges
    // (Bow Controls Type 2 reverses R and X); sheathed X draws the weapon.
    uint64_t fire = UINT64_C(1) << ((_drawn == 0) ? BTN_X :
                     _weaponKind == 1 ? (_bowType ? BTN_R : BTN_X) : BTN_A);
    uint64_t aim = UINT64_C(1) << ((_weaponKind == 1 && _bowType) ? BTN_X : BTN_R);
    [_fire setMask:fire];
    [_reload setMask:UINT64_C(1) << ((_weaponKind == 1 || _drawn == 0) ? BTN_A : BTN_X)];
    [_aim setMask:aim];
    if (rangedChanged) [self applyVisibilityV44];
}
- (void)applyCustomLayout {
    CGFloat width = self.bounds.size.width, height = self.bounds.size.height;
    if (width <= 0 || height <= 0) return;
    CGRect safe = [self safeControlRect];
    for (NSString *key in _customLayout) {
        UIView *view = [_namedControls objectForKey:key];
        NSArray *saved = [_customLayout objectForKey:key];
        if (!view || ![saved isKindOfClass:[NSArray class]] || saved.count != 4) continue;
        BOOL valid = YES;
        for (id value in saved) {
            if ([value isKindOfClass:[NSNumber class]] && isfinite([value doubleValue])) continue;
            valid = NO;
            break;
        }
        if (!valid || [[saved objectAtIndex:3] boolValue] != (width >= height)) continue;
        CGSize initialSize = view.bounds.size;
        if (initialSize.height <= 0) continue;
        CGFloat size = MAX(26, MIN(safe.size.height * .42, [[saved objectAtIndex:2] doubleValue] * height));
        CGPoint center = CGPointMake([[saved objectAtIndex:0] doubleValue] * width,
                                     [[saved objectAtIndex:1] doubleValue] * height);
        [self placeView:view center:center size:CGSizeMake(size * initialSize.width/initialSize.height, size)
                 inRect:safe];
    }
}

- (void)rememberSelectedPlacement {
    if (!_selectedControl) return;
    NSString *key = [[_namedControls allKeysForObject:_selectedControl] firstObject];
    CGFloat width = self.bounds.size.width, height = self.bounds.size.height;
    if (!key || width <= 0 || height <= 0) return;
    [_customLayout setObject:@[@(_selectedControl.center.x/width), @(_selectedControl.center.y/height),
        @(_selectedControl.bounds.size.height/height), @(width >= height)] forKey:key];
}

- (void)updateSelection {
    NSString *key = _selectedControl ? [[_namedControls allKeysForObject:_selectedControl] firstObject] : nil;
    _selectionOutline.hidden = !_editing || !key;
    _layoutSmaller.enabled = _editing && key != nil;
    _layoutLarger.enabled = _layoutSmaller.enabled;
    if (key) {
        _selectionOutline.frame = CGRectInset(_selectedControl.frame, -3, -3);
        _layoutSelection.text = [NSString stringWithFormat:@"%@  ·  %.0f pt", [self controlTitle:key],
                                 _selectedControl.bounds.size.height];
    } else {
        _layoutSelection.text = @"Drag a control to move it";
    }
}

- (void)beginLayoutForControl:(NSString *)key {
    if (_editing) return;
    _editing = YES;
    [self setSettingsOpen:NO];
    [self resetAll];
    _layoutBeforeEdit = [_customLayout copy];
    _layoutToolbar.hidden = NO;
    _settingsButton.userInteractionEnabled = NO;
    for (UIView *view in _controls) view.userInteractionEnabled = NO;
    _selectedControl = key ? [_namedControls objectForKey:key] : nil;
    [self applyVisibilityV44];
    [self updateOpacity];
    [self setNeedsLayout];
    [self layoutIfNeeded];
}

- (void)openLayoutEditor:(id)sender { (void)sender; [self beginLayoutForControl:nil]; }
- (void)moveSelectedControl:(id)sender { (void)sender; [self beginLayoutForControl:_settingsControlKey]; }

- (void)finishLayoutSaving:(BOOL)save {
    if (!_editing) return;
    if (save) [self saveProfileV44];
    else [_customLayout setDictionary:_layoutBeforeEdit];
    [_layoutBeforeEdit release];
    _layoutBeforeEdit = nil;
    [_editFinger release];
    _editFinger = nil;
    _selectedControl = nil;
    _editing = NO;
    _layoutToolbar.hidden = YES;
    [self updateSelection];
    _settingsButton.userInteractionEnabled = YES;
    for (UIView *view in _controls) view.userInteractionEnabled = YES;
    [self applyVisibilityV44];
    [self updateOpacity];
    [self setNeedsLayout];
    [self layoutIfNeeded];
    [self setSettingsOpen:YES];
}

- (void)saveLayout:(id)sender { (void)sender; [self finishLayoutSaving:YES]; }
- (void)cancelLayout:(id)sender { (void)sender; [self finishLayoutSaving:NO]; }
- (void)resetLayout:(id)sender {
    (void)sender;
    [_customLayout removeAllObjects];
    [_editFinger release];
    _editFinger = nil;
    [self setNeedsLayout];
    [self layoutIfNeeded];
}
- (void)moveLayoutToolbar:(id)sender {
    (void)sender;
    _layoutDockBottom = !_layoutDockBottom;
    [self layoutToolsInRect:[self safeControlRect]];
}
- (void)resizeSelectedBy:(CGFloat)factor {
    if (!_editing || !_selectedControl) return;
    CGSize current = _selectedControl.bounds.size;
    if (current.height <= 0) return;
    CGRect safe = [self safeControlRect];
    CGFloat height = MAX(26, MIN(safe.size.height * .42, current.height * factor));
    [self placeView:_selectedControl center:_selectedControl.center
               size:CGSizeMake(current.width/current.height * height, height) inRect:safe];
    [self rememberSelectedPlacement];
    [self updateSelection];
}
- (void)shrinkSelected:(id)sender { (void)sender; [self resizeSelectedBy:.9]; }
- (void)growSelected:(id)sender { (void)sender; [self resizeSelectedBy:1.1]; }

- (NSString *)profileStorageKeyV44:(NSString *)kind {
    return [NSString stringWithFormat:@"mhgu_touch_%@_profile_v44_%ld", kind, (long)_profileV44];
}
- (void)saveProfileV44 {
    NSUserDefaults *preferences = [NSUserDefaults standardUserDefaults];
    [preferences setObject:_customLayout forKey:[self profileStorageKeyV44:@"layout"]];
    [preferences setObject:[[_hiddenV44 allObjects] sortedArrayUsingSelector:@selector(compare:)]
                    forKey:[self profileStorageKeyV44:@"hidden"]];
    [preferences setObject:_stylesV44 forKey:[self profileStorageKeyV44:@"styles"]];
    if (_profileV44 == 2) [preferences setObject:_customLayout forKey:@"mhgu_touch_layout_v3"];
}
- (void)reloadProfileV44 {
    NSUserDefaults *preferences = [NSUserDefaults standardUserDefaults];
    NSDictionary *layout = [preferences dictionaryForKey:[self profileStorageKeyV44:@"layout"]];
    if (!layout && _profileV44 == 2) layout = [preferences dictionaryForKey:@"mhgu_touch_layout_v3"];
    NSArray *hidden = [preferences arrayForKey:[self profileStorageKeyV44:@"hidden"]];
    NSDictionary *styles = [preferences dictionaryForKey:[self profileStorageKeyV44:@"styles"]];
    [_customLayout release];
    [_hiddenV44 release];
    [_stylesV44 release];
    _customLayout = [[NSMutableDictionary alloc] initWithDictionary:layout ?: @{}];
    _hiddenV44 = [[NSMutableSet alloc] initWithArray:hidden ?: @[@"ITEM_BAR", @"L3", @"R3", @"COMBO_2"]];
    _stylesV44 = [[NSMutableDictionary alloc] initWithDictionary:styles ?: @{}];
}
- (void)profileChanged:(UISegmentedControl *)sender {
    NSInteger profile = sender.selectedSegmentIndex;
    if (profile < 0 || profile > 2 || profile == _profileV44) return;
    [self resetAll];
    _profileV44 = profile;
    [[NSUserDefaults standardUserDefaults] setInteger:profile forKey:@"mhgu_touch_active_profile_v44"];
    [self reloadProfileV44];
    [self applyStylesV44];
    [self applyVisibilityV44];
    [self setNeedsLayout];
}

- (void)resetControl:(UIView *)view {
    for (NSValue *owner in [_touchOwnersV441 allKeysForObject:view])
        [_touchOwnersV441 removeObjectForKey:owner];
    if ([view isKindOfClass:[MHGUTouchButton class]]) [(MHGUTouchButton *)view resetInput];
    else if ([view isKindOfClass:[MHGUTouchStick class]]) [(MHGUTouchStick *)view resetInput];
    else if ([view isKindOfClass:[MHGUTouchItemStrip class]]) [(MHGUTouchItemStrip *)view resetInput];
    else if ([view isKindOfClass:[UIButton class]]) {
        UIButton *button = (UIButton *)view;
        button.highlighted = NO;
        if (button == _itemPrevV44 || button == _itemNextV44) [self stopItemRepeat:button];
    }
}
- (void)applyVisibilityV44 {
    BOOL ranged = _weaponKind != 0;
    for (NSString *key in _namedControls) {
        UIView *view = [_namedControls objectForKey:key];
        if (view == _settingsButton) continue;
        BOOL modeHidden = NO;
        if (view == _right) modeHidden = _cameraSwipe;
        else if (view == _fire || view == _reload || view == _aim || view == _special ||
                 view == _ammoUp || view == _ammoDown) modeHidden = !ranged;
        else if (view == _button[BTN_A] || view == _button[BTN_X] || view == _button[BTN_Y])
            modeHidden = ranged;
        // The editor shows the active controls and any button opened from its detail page.
        // Evade (B) is available for melee, bow and bowgun.
        BOOL available = !modeHidden && ![_hiddenV44 containsObject:key];
        BOOL hidden = _editing ? !available && view != _selectedControl : _controlsHidden || !available;
        if (view.hidden == hidden) continue;
        if (hidden) [self resetControl:view];
        view.hidden = hidden;
    }
}

- (UIColor *)accentForColorV44:(NSInteger)index {
    switch (index) {
    case 1: return [UIColor colorWithRed:.85 green:.33 blue:.27 alpha:1];
    case 2: return [UIColor colorWithRed:.27 green:.72 blue:.76 alpha:1];
    case 3: return [UIColor colorWithRed:.56 green:.76 blue:.40 alpha:1];
    case 4: return [UIColor colorWithRed:.77 green:.64 blue:.93 alpha:1];
    case 5: return [UIColor colorWithRed:.93 green:.90 blue:.79 alpha:1];
    default: return hudGold();
    }
}

- (NSString *)controlTitle:(NSString *)key {
    if ([key isEqualToString:gearControlKey]) return @"Settings gear";
    NSDictionary *names = @{
        @"MOVE":@"Movement stick", @"CAMERA_STICK":@"Camera stick",
        @"B":@"B · Evade", @"+":@"+ · Start", @"−":@"− · Select",
        @"▲":@"D-pad up", @"▼":@"D-pad down", @"◀":@"D-pad left", @"▶":@"D-pad right",
        @"L3":@"Left stick click", @"R3":@"Right stick click",
        @"FIRE":@"Fire / charge", @"RELOAD":@"Reload", @"AIM":@"Aim", @"SPECIAL":@"Special shot",
        @"AMMO_UP":@"Next ammo", @"AMMO_DOWN":@"Previous ammo",
        @"ITEM_PREV":@"Previous item", @"ITEM_USE":@"Use item", @"ITEM_NEXT":@"Next item", @"ITEM_BAR":@"Item swipe bar",
        @"ART1":@"Hunter Art 1", @"ART2":@"Hunter Art 2", @"ART3":@"Hunter Art 3",
        @"COMBO_1":@"Combo 1", @"COMBO_2":@"Combo 2",
    };
    return [names objectForKey:key] ?: key;
}

- (NSUInteger)comboSlotForKey:(NSString *)key {
    if ([key isEqualToString:@"COMBO_1"]) return 0;
    if ([key isEqualToString:@"COMBO_2"]) return 1;
    return NSNotFound;
}

- (NSString *)defaultCaptionV44:(NSString *)key {
    NSUInteger slot = [self comboSlotForKey:key];
    if (slot != NSNotFound) return savedCombo(slot);
    NSDictionary *labels = @{@"CAMERA_STICK":@"CAM", @"FIRE":@"FIRE", @"RELOAD":@"LOAD",
        @"AMMO_UP":@"AMMO+", @"AMMO_DOWN":@"AMMO−", @"ITEM_PREV":@"‹", @"ITEM_USE":@"Use",
        @"ITEM_NEXT":@"›", @"ITEM_BAR":@"‹      ITEMS      ›"};
    return [labels objectForKey:key] ?: key;
}

- (NSDictionary *)styleForKey:(NSString *)key {
    id style = [_stylesV44 objectForKey:key];
    return [style isKindOfClass:[NSDictionary class]] ? style : nil;
}

- (void)applyOpacityForKey:(NSString *)key {
    UIView *view = [_namedControls objectForKey:key];
    CGFloat alpha = _buttonOpacity;
    if (view == _settingsButton) {
        if (_gearOverride) alpha = _gearOpacity;
    } else {
        NSNumber *opacity = [[self styleForKey:key] objectForKey:@"alpha"];
        if (opacity) alpha *= fmax(.25, fmin(1, [opacity doubleValue]));
    }
    view.alpha = _editing ? MAX(.55, alpha) : alpha;
}

- (void)updateOpacity {
    for (NSString *key in _namedControls) [self applyOpacityForKey:key];
}

- (void)applyStyleForKey:(NSString *)key {
    UIView *view = [_namedControls objectForKey:key];
    if (view == _settingsButton) {
        [self applyOpacityForKey:key];
        return;
    }
    NSDictionary *style = [self styleForKey:key];
    NSString *caption = [style objectForKey:@"caption"] ?: [self defaultCaptionV44:key];
    UIColor *accent = [self accentForColorV44:[[style objectForKey:@"color"] integerValue]];
    if ([view isKindOfClass:[MHGUTouchButton class]]) {
        MHGUTouchButton *button = (MHGUTouchButton *)view;
        [button setCaption:caption];
        [button setAccentV44:accent];
    } else {
        if ([view isKindOfClass:[MHGUTouchStick class]]) [(MHGUTouchStick *)view setCaption:caption];
        else if ([view isKindOfClass:[MHGUTouchItemStrip class]]) [(MHGUTouchItemStrip *)view setCaption:caption];
        else if ([view isKindOfClass:[UIButton class]]) [(UIButton *)view setTitle:caption forState:UIControlStateNormal];
        view.layer.borderColor = [accent colorWithAlphaComponent:.78].CGColor;
    }
    [self applyOpacityForKey:key];
}
- (void)applyStylesV44 {
    for (NSString *key in _namedControls) [self applyStyleForKey:key];
}

- (void)showButtonList {
    for (NSUInteger i = 0; i < _editorNamesV44.count; i++) {
        NSString *key = [_editorNamesV44 objectAtIndex:i];
        NSString *title = [self controlTitle:key];
        NSUInteger slot = [self comboSlotForKey:key];
        if (slot != NSNotFound) title = [NSString stringWithFormat:@"%@  ·  %@", title, savedCombo(slot)];
        UISwitch *visible = nil;
        if (![key isEqualToString:gearControlKey]) {
            visible = [self settingsSwitch:![_hiddenV44 containsObject:key] action:@selector(buttonVisibilityChanged:)];
            visible.tag = (NSInteger)i;
            visible.accessibilityLabel = [NSString stringWithFormat:@"Show %@", title];
        }
        UIView *row = [self appendSettingsRow:nil accessory:visible];
        UIButton *button = touch_menu_button([title stringByAppendingString:@"  ›"], self, @selector(openButtonSettings:));
        button.accessibilityLabel = title;
        button.accessibilityHint = @"Edit this button";
        button.frame = CGRectMake(8, 1, MAX(1, row.bounds.size.width - (visible ? 80 : 16)), 46);
        button.autoresizingMask = UIViewAutoresizingFlexibleWidth;
        button.backgroundColor = [UIColor clearColor];
        button.layer.borderWidth = 0;
        button.contentHorizontalAlignment = UIControlContentHorizontalAlignmentLeft;
        button.tag = (NSInteger)i;
        [row addSubview:button];
    }
}

- (void)openButtonSettings:(UIButton *)sender {
    if ((NSUInteger)sender.tag >= _editorNamesV44.count) return;
    _buttonListOffset = _settingsScroll.contentOffset;
    [_settingsControlKey release];
    _settingsControlKey = [[_editorNamesV44 objectAtIndex:sender.tag] copy];
    [self showSettingsPage];
}
- (void)backToButtonList:(id)sender {
    (void)sender;
    [self endEditing:YES];
    [_settingsControlKey release];
    _settingsControlKey = nil;
    [self showSettingsPage];
}
- (void)buttonVisibilityChanged:(UISwitch *)sender {
    if ((NSUInteger)sender.tag >= _editorNamesV44.count) return;
    NSString *key = [_editorNamesV44 objectAtIndex:sender.tag];
    if (sender.isOn) [_hiddenV44 removeObject:key];
    else [_hiddenV44 addObject:key];
    [self applyVisibilityV44];
    [self saveProfileV44];
}
- (void)setAppearanceValue:(id)value field:(NSString *)field key:(NSString *)key {
    if (!key) return;
    NSMutableDictionary *style = [NSMutableDictionary dictionaryWithDictionary:[self styleForKey:key] ?: @{}];
    if (value) [style setObject:value forKey:field];
    else [style removeObjectForKey:field];
    if (style.count) [_stylesV44 setObject:style forKey:key];
    else [_stylesV44 removeObjectForKey:key];
    [self applyStyleForKey:key];
    [self saveProfileV44];
}
- (void)buttonLabelChanged:(UITextField *)sender {
    NSString *text = [sender.text stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceAndNewlineCharacterSet]];
    if (text.length > 14) {
        NSRange cluster = [text rangeOfComposedCharacterSequenceAtIndex:13];
        text = [text substringToIndex:NSMaxRange(cluster) > 14 ? cluster.location : 14];
    }
    [self setAppearanceValue:(text.length ? text : nil) field:@"caption" key:_settingsControlKey];
    sender.text = text.length ? text : nil;
}
- (void)buttonAccentChanged:(UISegmentedControl *)sender {
    [self setAppearanceValue:@(sender.selectedSegmentIndex) field:@"color" key:_settingsControlKey];
}
- (void)buttonOpacityChanged:(UISlider *)sender {
    [self setAppearanceValue:@(sender.value) field:@"alpha" key:_settingsControlKey];
    [self showSliderValue:sender percent:YES];
}
- (void)resetButtonAppearance:(id)sender {
    (void)sender;
    [self endEditing:YES];
    [_stylesV44 removeObjectForKey:_settingsControlKey];
    [self applyStyleForKey:_settingsControlKey];
    [self saveProfileV44];
    [self showSettingsPage];
}
- (void)chooseComboInput:(NSString *)name index:(NSUInteger)index slot:(NSUInteger)slot {
    [self endEditing:YES];
    NSMutableArray *pair = [NSMutableArray arrayWithArray:[savedCombo(slot) componentsSeparatedByString:@"+"]];
    NSUInteger other = 1 - index;
    if ([name isEqualToString:[pair objectAtIndex:other]])
        [pair replaceObjectAtIndex:other withObject:[pair objectAtIndex:index]];
    [pair replaceObjectAtIndex:index withObject:name];
    if ([self applyComboSlot:slot text:[pair componentsJoinedByString:@"+"]]) {
        [self applyStyleForKey:comboControlKey(slot)];
        [self showSettingsPage];
    }
}
- (UIButton *)comboPickerForSlot:(NSUInteger)slot index:(NSUInteger)index {
    NSString *selected = [[savedCombo(slot) componentsSeparatedByString:@"+"] objectAtIndex:index];
    UIButton *picker = [UIButton buttonWithType:UIButtonTypeCustom];
    mhgu_style_menu(picker);
    picker.bounds = CGRectMake(0, 0, 126, 38);
    [picker setTitle:[selected stringByAppendingString:@"  ▾"] forState:UIControlStateNormal];
    picker.accessibilityValue = selected;
    NSMutableArray *choices = [NSMutableArray arrayWithCapacity:comboNames().count];
    __block MHGUTouchRoot *root = self;  // MRC: the menu is owned by this overlay.
    for (NSString *name in comboNames()) {
        UIAction *choice = [UIAction actionWithTitle:name image:nil identifier:nil handler:^(UIAction *action) {
            (void)action;
            [root chooseComboInput:name index:index slot:slot];
        }];
        choice.state = [name isEqualToString:selected] ? UIMenuElementStateOn : UIMenuElementStateOff;
        [choices addObject:choice];
    }
    picker.menu = [UIMenu menuWithTitle:@"" children:choices];
    picker.showsMenuAsPrimaryAction = YES;
    return picker;
}

- (void)showButtonSettings {
    NSString *key = _settingsControlKey;
    NSDictionary *style = [self styleForKey:key];
    NSUInteger slot = [self comboSlotForKey:key];
    if (slot != NSNotFound) {
        [self appendSettingsRow:@"First input" accessory:[self comboPickerForSlot:slot index:0]];
        [self appendSettingsRow:@"Second input" accessory:[self comboPickerForSlot:slot index:1]];
    }
    UISwitch *visible = [self settingsSwitch:![_hiddenV44 containsObject:key]
                                       action:@selector(buttonVisibilityChanged:)];
    visible.tag = (NSInteger)[_editorNamesV44 indexOfObject:key];
    [self appendSettingsRow:@"Show when available" accessory:visible];
    UITextField *label = [self appendTextField:@"Custom label" text:[style objectForKey:@"caption"]
                                      action:@selector(buttonLabelChanged:)];
    label.placeholder = [self defaultCaptionV44:key];
    NSInteger color = [[style objectForKey:@"color"] integerValue];
    UISegmentedControl *colors = [self settingsSegments:@[@"Gold", @"Red", @"Teal", @"Green", @"Violet", @"Ivory"]
        selected:MAX(0, MIN(5, color)) width:320 action:@selector(buttonAccentChanged:)];
    colors.accessibilityLabel = @"Accent color";
    [self appendSettingsRow:nil accessory:colors];
    NSNumber *alpha = [style objectForKey:@"alpha"];
    [self appendSlider:@"Button opacity" minimum:.25 maximum:1 value:(alpha ? alpha.floatValue : 1)
                percent:YES action:@selector(buttonOpacityChanged:)];

    [self appendSettingsAction:@"Move & resize" action:@selector(moveSelectedControl:)];
    [self appendSettingsAction:@"Reset appearance" action:@selector(resetButtonAppearance:)];
}

// Taps advance immediately. Holding repeats at a controlled rate; timers are
// cancelled on touch end, backgrounding, hiding controls, or profile switching.
- (void)startItemRepeatV44:(NSInteger)index {
    if (index < 0 || index > 1 || _repeatHeldV44[index]) return;
    _repeatHeldV44[index] = YES;
    _repeatStartV44[index] = _repeatLastV44[index] = mhgu_now_ms();
    queue_steps(NO, index == 0 ? -1 : 1);
    _repeatTimerV44[index] = [[NSTimer scheduledTimerWithTimeInterval:.05 target:self
                          selector:@selector(repeatItemsV44:) userInfo:@(index) repeats:YES] retain];
}
- (void)itemPrevDownV44:(id)sender { (void)sender; [self startItemRepeatV44:0]; }
- (void)itemNextDownV44:(id)sender { (void)sender; [self startItemRepeatV44:1]; }
- (void)itemUseDownV44:(id)sender { (void)sender; pulse_button_mask(UINT64_C(1) << BTN_Y, 110); }
- (void)repeatItemsV44:(NSTimer *)timer {
    NSInteger index = [[timer userInfo] integerValue];
    if (index < 0 || index > 1 || !_repeatHeldV44[index]) return;
    uint64_t now = mhgu_now_ms();
    if (now - _repeatStartV44[index] >= 380 && now - _repeatLastV44[index] >= 155) {
        queue_steps(NO, index == 0 ? -1 : 1);
        _repeatLastV44[index] = now;
    }
}
- (void)stopItemRepeat:(UIButton *)sender {
    NSInteger index = sender == _itemPrevV44 ? 0 : 1;
    _repeatHeldV44[index] = NO;
    [_repeatTimerV44[index] invalidate];
    [_repeatTimerV44[index] release];
    _repeatTimerV44[index] = nil;
}
- (void)updateHudTimer {
    BOOL show = _hudOnV44 && self.window && !_settingsOpen && !_editing && mhgu_ios_is_foreground();
    _hudLabelV44.hidden = !show;
    atomic_store_explicit(&s_traceCombos, show, memory_order_relaxed);
    if (show && !_hudTimerV44) {
        _hudPrevMsV44 = 0;
        _hudTimerV44 = [[NSTimer scheduledTimerWithTimeInterval:.35 target:self
                  selector:@selector(updateHudV44:) userInfo:nil repeats:YES] retain];
        [self updateHudV44:_hudTimerV44];
    } else if (!show && _hudTimerV44) {
        [_hudTimerV44 invalidate];
        [_hudTimerV44 release];
        _hudTimerV44 = nil;
    }
}
- (void)updateHudV44:(NSTimer *)timer {
    (void)timer;
    if (_hudLabelV44.hidden) return;
    extern volatile uint64_t g_present_count;
    uint64_t now = mhgu_now_ms();
    uint64_t frame = __atomic_load_n(&g_present_count, __ATOMIC_RELAXED);
    double fps = 0;
    if (_hudPrevMsV44 && now > _hudPrevMsV44 && frame >= _hudPrevFrameV44)
        fps = (double)(frame - _hudPrevFrameV44) * 1000.0 / (double)(now - _hudPrevMsV44);
    _hudPrevMsV44 = now;
    _hudPrevFrameV44 = frame;
    uint64_t buttons = touch_button_state(now);
    static const int bits[] = {BTN_A, BTN_B, BTN_X, BTN_Y, BTN_L, BTN_R, BTN_ZL, BTN_ZR,
                               BTN_PLUS, BTN_MINUS, BTN_UP, BTN_DOWN};
    NSArray *names = @[@"A", @"B", @"X", @"Y", @"L", @"R", @"ZL", @"ZR", @"+", @"−", @"▲", @"▼"];
    NSMutableArray *held = [NSMutableArray array];
    for (NSUInteger i=0; i<sizeof(bits)/sizeof(bits[0]); i++)
        if (buttons & (UINT64_C(1) << bits[i])) [held addObject:[names objectAtIndex:i]];
    NSString *pressed = held.count ? [held componentsJoinedByString:@" "] : @"—";
    if (pressed.length > 21) pressed = [[pressed substringToIndex:21] stringByAppendingString:@"…"];
    float mx = atomic_load_explicit(&s_lx, memory_order_relaxed) / 32767.0f;
    float my = atomic_load_explicit(&s_ly, memory_order_relaxed) / 32767.0f;
    float cx = atomic_load_explicit(&s_rx, memory_order_relaxed) / 32767.0f;
    float cy = atomic_load_explicit(&s_ry, memory_order_relaxed) / 32767.0f;
    if (now - atomic_load_explicit(&s_lastSwipeMs, memory_order_relaxed) < 65) {
        cx += atomic_load_explicit(&s_swipeRx, memory_order_relaxed) / 32767.0f;
        cy += atomic_load_explicit(&s_swipeRy, memory_order_relaxed) / 32767.0f;
    }
    _hudLabelV44.text = [NSString stringWithFormat:
        @"  %.1f/%d FPS · %@\n  MOVE %.1f %.1f  CAM %.1f %.1f  F:%lu",
        fps, (int)lroundf(config_live_fps()), pressed, mx, my, cx, cy,
        (unsigned long)_touchOwnersV441.count + (_cameraFinger ? 1u : 0u)];
}
- (void)dealloc {
    [[NSNotificationCenter defaultCenter] removeObserver:self];
    [self resetAll];
    [_namedControls release];
    [_touchOwnersV441 release];
    [_customLayout release];
    [_controls release];
    [_hiddenV44 release];
    [_stylesV44 release];
    [_editorNamesV44 release];
    [_settingsControlKey release];
    [_importedHeadingURL release];
    [_importedHeadingName release];
    [_layoutBeforeEdit release];
    [_hudTimerV44 invalidate];
    [_hudTimerV44 release];
    [_hudLabelV44 release];
    [super dealloc];
}
@end

static void poll_overlay_weapon(void) { [s_overlay pollWeapon]; }

void mhgu_touch_cancel_inputs(void) { [s_overlay resetAll]; }

void mhgu_touch_install(SDL_Window *window) {
    if (!window) return;
    // UIKit work must run on the UI thread. ui_init() is called there in this port.
    if (![NSThread isMainThread]) {
        // Never block the host thread: dispatch asynchronously to avoid a deadlock.
        dispatch_async(dispatch_get_main_queue(), ^{ mhgu_touch_install(window); });
        return;
    }
    if (s_overlay) return;
    SDL_PropertiesID props = SDL_GetWindowProperties(window);
    UIWindow *uiWindow = (__bridge UIWindow *)SDL_GetPointerProperty(
        props, SDL_PROP_WINDOW_UIKIT_WINDOW_POINTER, NULL);
    if (!uiWindow) {
        NSLog(@"[MHGU Touch] SDL UIKit window unavailable; overlay not installed");
        return;
    }
    uiWindow.multipleTouchEnabled = YES;
    uiWindow.exclusiveTouch = NO;
    s_overlay = [[MHGUTouchRoot alloc] initWithFrame:uiWindow.bounds];
    [uiWindow addSubview:s_overlay];
    [s_overlay setNeedsLayout];
    [s_overlay layoutIfNeeded];
    NSLog(@"[MHGU Touch] Cerroverb touchscreen port installed");
}
