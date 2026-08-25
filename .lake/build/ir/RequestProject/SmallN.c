// Lean compiler output
// Module: RequestProject.SmallN
// Imports: public import Init public import Mathlib public import RequestProject.Selling
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
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_decidableEqNone___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_FairSelling_outcomeOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_FairSelling_outcomeOf___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_FairSelling_outcomeOf___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = l_Option_decidableEqNone___redArg(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_RequestProject_FairSelling_outcomeOf___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_FairSelling_outcomeOf___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = l_Option_instDecidableEq___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_RequestProject_FairSelling_outcomeOf___redArg___lam__1(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_outcomeOf___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
x_6 = lp_mathlib_Multiset_filter___redArg(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_3);
x_5 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_outcomeOf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_outcomeOf___redArg___lam__2), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_1);
x_7 = lp_mathlib_Multiset_filter___redArg(x_5, x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_outcomeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject_FairSelling_outcomeOf___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_Selling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_SmallN(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
