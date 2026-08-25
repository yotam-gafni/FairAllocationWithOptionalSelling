// Lean compiler output
// Module: RequestProject.ThreeAgentCashComposition
// Imports: public import Init public import Mathlib public import RequestProject.ThreeAgentCash
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
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_dropCashOutcome___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_dropCashOutcome(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_biUnion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_dropCashOutcome___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_ThreeAgentCashComposition_0__FairSelling_optionGoods_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_RequestProject_FairSelling_optionGoods___redArg___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_ThreeAgentCashComposition_0__FairSelling_optionGoods_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_FairSelling_optionGoods___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_FairSelling_optionGoods___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_optionGoods___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_RequestProject_FairSelling_optionGoods___redArg___closed__0;
x_4 = lp_mathlib_Finset_biUnion___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_optionGoods(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_FairSelling_optionGoods___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_ThreeAgentCashComposition_0__FairSelling_optionGoods_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_ThreeAgentCashComposition_0__FairSelling_optionGoods_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject___private_RequestProject_ThreeAgentCashComposition_0__FairSelling_optionGoods_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_dropCashOutcome___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lp_RequestProject_FairSelling_optionGoods___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_dropCashOutcome___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_dropCashOutcome___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lp_RequestProject_FairSelling_optionGoods___redArg(x_1, x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_dropCashOutcome___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
x_12 = lp_RequestProject_FairSelling_optionGoods___redArg(x_1, x_8);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_dropCashOutcome(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_FairSelling_dropCashOutcome___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ThreeAgentCash(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ThreeAgentCashComposition(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ThreeAgentCash(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_FairSelling_optionGoods___redArg___closed__0 = _init_lp_RequestProject_FairSelling_optionGoods___redArg___closed__0();
lean_mark_persistent(lp_RequestProject_FairSelling_optionGoods___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
