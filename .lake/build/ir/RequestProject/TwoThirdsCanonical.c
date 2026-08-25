// Lean compiler output
// Module: RequestProject.TwoThirdsCanonical
// Imports: public import Init public import Mathlib public import RequestProject.Selling public import RequestProject.SmallN public import RequestProject.TPSApprox public import RequestProject.TwoThirdsMatching
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
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_biUnion___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_cash___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_cash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_cash(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Option_toFinset___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_cash___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec_ref(x_1);
lean_inc(x_2);
x_5 = lean_apply_1(x_3, x_2);
x_6 = lean_apply_1(x_4, x_2);
x_7 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_cash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_RequestProject_FairSelling_Canonical_cash___redArg(x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_cash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_RequestProject_FairSelling_Canonical_cash(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lp_mathlib_Option_toFinset___redArg(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_Canonical_sold___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lp_mathlib_Finset_biUnion___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_RequestProject_FairSelling_Canonical_sold___redArg(x_2, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_Canonical_sold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_RequestProject_FairSelling_Canonical_sold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_Selling(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_SmallN(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_TPSApprox(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_TwoThirdsMatching(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_TwoThirdsCanonical(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_Selling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_SmallN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_TPSApprox(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_TwoThirdsMatching(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
