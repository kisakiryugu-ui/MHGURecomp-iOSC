// Experimental MHGU v1.4.0 (Switch) camera-follow hook for the iOS recompilation.
// Independent adaptation of the ideas/offsets documented in gu-native's
// runtime/hle/mousecam.c and runtime/hle/weapon.c. No game assets included.
// Always validate guest mappings before dereferencing pointers.
#include <math.h>
#include <stdatomic.h>
#include <stdint.h>
#include "../hle.h"
#include "../touch_overlay.h"

#define FN_QUEST_CAMERA_STICK 0x2255ccu
#define PTR_ENEMIES   0x1a51fe0u
#define PTR_PLAYERS   0x1a85b58u
#define PTR_CONTROL   0x1a8ca48u
#define PL_ZONE       0x1054u
#define MAX_DIST2     (6000.0f * 6000.0f)

static atomic_bool g_lock_enabled;
static atomic_bool g_runtime_ready;
static atomic_bool g_lock_hook_ready;
static atomic_uint_fast64_t g_pause_camera_until_ns;
static uint32_t g_locked_enemy;
static uint64_t g_last_frame_ns;

static int mapped(uint32_t addr, uint32_t sz) {
    return addr && sz && (uint64_t)addr + sz <= UINT32_MAX && kernel_mapped(addr, sz);
}
static uint32_t read32(uint32_t addr) { return mapped(addr, 4) ? LD32(addr) : 0; }
static uint16_t read16(uint32_t addr) { return mapped(addr, 2) ? LD16(addr) : 0; }
static uint8_t read8(uint32_t addr) { return mapped(addr, 1) ? LD8(addr) : 0; }
static float readf(uint32_t addr) { return mapped(addr, 4) ? LDF(addr) : NAN; }
static int sane_object(uint32_t ptr, uint32_t length) {
    return ptr >= 0x08000000u && ptr < 0xf0000000u && !(ptr & 3u) && mapped(ptr, length);
}
// Fails closed until the player's object and vtable agree with the known
// MHGU v1.4.0 layout. API returns 0 (normal), 1 (bow), 2 (bowgun).
static uint32_t hunter(void) {
    uint32_t gc = read32(PTR_CONTROL), sp = read32(PTR_PLAYERS);
    if (!sane_object(gc, 0x70) || !sane_object(sp, 0x2c)) return 0;
    uint32_t slot = read32(gc + 0x30);
    if (slot >= 4) return 0;
    uint32_t pl = read32(sp + 0x1c + 4u * slot);
    if (!sane_object(pl, 4)) return 0;
    uint32_t options[] = {pl, read32(pl + 0x15b0), read32(pl + 0x3010)};
    for (int i = 0; i < 3; i++) {
        uint32_t p = options[i];
        if (!sane_object(p, 4)) continue;
        uint32_t vt = read32(p);
        if (vt >= 0x00200000u && vt < 0x02347000u &&
            read32(vt + 94u * 4u) == 0x4a2444u)
            return p;
    }
    return 0;
}
int mhgu_touch_detect_weapon(int *drawn, int *bow_type) {
    // SDL/UIKit window is created before the game's kernel address map exists.
    if (!atomic_load(&g_runtime_ready)) {
        if (drawn) *drawn = -1;
        if (bow_type) *bow_type = 0;
        return 0;
    }
    uint32_t h = hunter(), gc = read32(PTR_CONTROL);
    if (drawn) *drawn = h && mapped(h + 0x2749, 1) ? (read8(h + 0x2749) & 1) : -1;
    if (bow_type) *bow_type = sane_object(gc, 0x70) ? (read8(gc + 0x6c) == 1) : 0;
    uint32_t vt = h ? read32(h) : 0;
    if (vt == 0x194e9e0u) return 1;
    if (vt == 0x194bdc4u || vt == 0x194c694u) return 2;
    return 0;
}
void mhgu_touch_lock_enable(int on) {
    atomic_store(&g_lock_enabled, on != 0);
    // Hook thread owns the target selection. It clears it on the next frame.
}
int mhgu_touch_lock_available(void) { return atomic_load(&g_lock_hook_ready); }
void mhgu_touch_camera_drag(void) {
    atomic_store(&g_pause_camera_until_ns, plat_now_ns() + 450000000ull);
}
static int target_monster(float cx, float cz, float xyz[3]) {
    uint32_t pool = read32(PTR_ENEMIES), h = hunter();
    if (!sane_object(pool, 0x50) || !h) return 0;
    float best = MAX_DIST2, old = MAX_DIST2, prev[3] = {0};
    uint32_t nearest = 0;
    for (int i = 0; i < 10; i++) {
        uint32_t en = read32(pool + 0x1c + (uint32_t)i * 4u);
        if (!sane_object(en, 0x142c) || read8(en + PL_ZONE) != read8(h + PL_ZONE)) continue;
        uint32_t info = read32(en + 0x1428);
        if (!sane_object(info, 0x1b8)) continue;
        uint16_t id = read16(info + 0x1b6);
        if (id == 0xffffu || id >= 10000u) continue;
        float x = readf(info + 0x40), y = readf(info + 0x44), z = readf(info + 0x48);
        if (!isfinite(x) || !isfinite(y) || !isfinite(z)) continue;
        float d = (x - cx) * (x - cx) + (z - cz) * (z - cz);
        if (en == g_locked_enemy && d < MAX_DIST2) {
            old = d; prev[0] = x; prev[1] = y; prev[2] = z;
        }
        if (d < best) {
            best = d; nearest = en; xyz[0] = x; xyz[1] = y; xyz[2] = z;
        }
    }
    // Resist changing between two similarly distant monsters.
    if (old < MAX_DIST2 && nearest != g_locked_enemy && best >= old * .49f) {
        xyz[0] = prev[0]; xyz[1] = prev[1]; xyz[2] = prev[2];
        return 1;
    }
    g_locked_enemy = nearest;
    return nearest != 0;
}
static void touch_camera_hook(Cpu *c) {
    uint32_t cam = c->r[0];
    fnhook_call_next(c, FN_QUEST_CAMERA_STICK);
    if (!atomic_load_explicit(&g_lock_enabled, memory_order_relaxed)) {
        g_locked_enemy = 0;
        g_last_frame_ns = 0;
        return;
    }
    uint64_t now = plat_now_ns();
    uint64_t prev = g_last_frame_ns;
    g_last_frame_ns = now;
    if (now < atomic_load(&g_pause_camera_until_ns) ||
        !prev || now - prev > 180000000ull || !sane_object(cam, 0x9f0)) {
        g_locked_enemy = 0;
        return;
    }
    float hx = readf(cam + 0x60), hz = readf(cam + 0x68), target[3];
    if (!isfinite(hx) || !isfinite(hz) || !target_monster(hx, hz, target)) return;
    float dx = target[0] - hx, dz = target[2] - hz;
    float distance = sqrtf(dx * dx + dz * dz);
    if (distance <= 120.0f) return;
    float proximity = fminf(1.0f, fmaxf(0.0f, (distance - 120.0f) / 260.0f));
    float dt = fminf(0.10f, (float)(now - prev) * 1e-9f);
    float gain = (1.0f - expf(-dt / .12f)) * proximity;
    const float units = 65536.0f / (2.0f * 3.14159265358979323846f);
    int desired = (int)lrintf(atan2f(-dx, -dz) * units);
    int yaw = (int)(read32(cam + 0x9ec) & 0xffffu);
    int delta = (int16_t)(uint16_t)(desired - yaw);
    int step = (int)lrintf((float)delta * gain);
    if (step) {
        ST32(cam + 0x9ec, (uint32_t)(yaw + step) & 0xffffu);
        ST32(cam + 0x9e4, (read32(cam + 0x9e4) + (uint32_t)step) & 0xffffu);
    }
    float hy = readf(cam + 0x64);
    if (isfinite(hy)) {
        int desiredPitch = (int)lrintf(atan2f(target[1] + 90.0f - hy, distance) * units);
        if (desiredPitch > 0xc00) desiredPitch = 0xc00;
        if (desiredPitch < -0xe00) desiredPitch = -0xe00;
        int oldPitch = (int16_t)read32(cam + 0x9e8);
        int pitchStep = (int)lrintf((desiredPitch - oldPitch) * gain * .6f);
        if (pitchStep) {
            ST32(cam + 0x9e8, (uint32_t)(oldPitch + pitchStep) & 0xffffu);
            ST32(cam + 0x9e0, (read32(cam + 0x9e0) + (uint32_t)pitchStep) & 0xffffu);
        }
    }
}
void mhgu_touch_runtime_init(void) {
    // Wrap the existing mouse-camera hook without replacing it.
    if (!fnhook_set_outer(FN_QUEST_CAMERA_STICK,
                          hle_register("mhgu_touch:quest_camera", touch_camera_hook))) {
        LOG("[touch] warning: quest camera hook could not be installed\n");
    } else {
        atomic_store(&g_lock_hook_ready, true);
    }
    atomic_store(&g_runtime_ready, true);
}
