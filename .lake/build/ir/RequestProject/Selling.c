// Lean compiler output
// Module: RequestProject.Selling
// Imports: public import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_sum___at___00FairSelling_util_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_sum___at___00Finset_sum___at___00BoundingSieve_multSum_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbarSum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbarSum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_sum___at___00FairSelling_util_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbarSum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_sum___at___00FairSelling_util_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_mathlib_Multiset_map___redArg(x_2, x_1);
x_4 = lp_mathlib_Multiset_sum___at___00Finset_sum___at___00BoundingSieve_multSum_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_util___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_3);
x_7 = lean_apply_1(x_4, x_3);
x_8 = lp_RequestProject_Finset_sum___at___00FairSelling_util_spec__0___redArg(x_7, x_6);
x_9 = lean_apply_1(x_5, x_3);
x_10 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject_FairSelling_util___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_util___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject_FairSelling_util(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_sum___at___00FairSelling_util_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_Finset_sum___at___00FairSelling_util_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_FairSelling_vbar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbarSum___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_FairSelling_vbar___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbarSum___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_vbarSum___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lp_RequestProject_Finset_sum___at___00FairSelling_util_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_vbarSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_FairSelling_vbarSum___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_Selling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
