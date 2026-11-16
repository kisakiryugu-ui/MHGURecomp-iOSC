// Experimental iOS / iPadOS touchscreen controller for MHGURecomp.
#pragma once
#include <stdint.h>
struct SDL_Window;
#ifdef __cplusplus
extern "C" {
#endif
void mhgu_touch_install(struct SDL_Window *window);
void mhgu_touch_cancel_inputs(void);
void mhgu_touch_snapshot(uint64_t *buttons, int *lx, int *ly, int *rx, int *ry);
void mhgu_touch_combo_sampled(uint64_t buttons);
// Runtime side: independent of UIKit; MHGU Switch v1.4.0 offsets only.
void mhgu_touch_runtime_init(void);
int mhgu_touch_detect_weapon(int *drawn, int *bow_type);
void mhgu_touch_lock_enable(int on);
int mhgu_touch_lock_available(void);
void mhgu_touch_camera_drag(void);
#ifdef __cplusplus
}
#endif
