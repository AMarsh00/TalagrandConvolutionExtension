// Lean compiler output
// Module: TailBound
// Imports: public import Init public import TailBound.Core public import TailBound.HeatRatio public import TailBound.LevelOne public import TailBound.Flux public import TailBound.Generators public import TailBound.SmallThreshold public import TailBound.BridgeEnergy public import TailBound.BridgeChi public import TailBound.BridgeHorizontal public import TailBound.PositiveKernel public import TailBound.MainStatement public import TailBound.TimeGrid public import TailBound.DoobCalculus public import TailBound.FlowIntegration public import TailBound.InverseDensity public import TailBound.LayerDiscrepancy public import TailBound.MainTheorem
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
lean_object* initialize_TailBoundAudit_TailBound_Core(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_HeatRatio(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_LevelOne(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_Flux(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_Generators(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_SmallThreshold(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_BridgeEnergy(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_BridgeChi(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_BridgeHorizontal(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_PositiveKernel(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_MainStatement(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_TimeGrid(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_DoobCalculus(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_FlowIntegration(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_InverseDensity(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_LayerDiscrepancy(uint8_t builtin);
lean_object* initialize_TailBoundAudit_TailBound_MainTheorem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TailBoundAudit_TailBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_HeatRatio(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_LevelOne(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_Flux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_Generators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_SmallThreshold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_BridgeEnergy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_BridgeChi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_BridgeHorizontal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_PositiveKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_MainStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_TimeGrid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_DoobCalculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_FlowIntegration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_InverseDensity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_LayerDiscrepancy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TailBoundAudit_TailBound_MainTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
