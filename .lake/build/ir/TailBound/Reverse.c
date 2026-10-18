// Lean compiler output
// Module: TailBound.Reverse
// Imports: public import Init public import TailBound.JumpFlow public import TailBound.Generators public import TalagrandConvConjecture.PowerCoupling
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_JumpFlow(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_Generators(uint8_t builtin);
lean_object* initialize_TalagrandConvConjecture_TalagrandConvConjecture_PowerCoupling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TailBoundAudit_TailBound_Reverse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_JumpFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_Generators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TalagrandConvConjecture_TalagrandConvConjecture_PowerCoupling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
