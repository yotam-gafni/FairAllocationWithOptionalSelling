// Lean compiler output
// Module: RequestProject.TwoAgents
// Imports: public import Init public import Mathlib public import RequestProject.SmallN
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
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00MultilinearMap_alternatization___at___00Matrix_detRowAlternating___at___00Matrix_det___at___00Matrix_cramerMap___at___00Matrix_cramer___at___00Matrix_adjugate___at___00Matrix_SpecialLinearGroup_toGL___at___00Matrix_SpecialLinearGroup_mapGL___at___00CongruenceSubgroup_conjGL_spec__0_spec__0_spec__4_spec__10_spec__16_spec__21_spec__27_spec__32_spec__35_spec__37_spec__42_spec__49(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_mod(x_4, x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_mod(x_6, x_1);
x_8 = lp_mathlib_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00MultilinearMap_alternatization___at___00Matrix_detRowAlternating___at___00Matrix_det___at___00Matrix_cramerMap___at___00Matrix_cramer___at___00Matrix_adjugate___at___00Matrix_SpecialLinearGroup_toGL___at___00Matrix_SpecialLinearGroup_mapGL___at___00CongruenceSubgroup_conjGL_spec__0_spec__0_spec__4_spec__10_spec__16_spec__21_spec__27_spec__32_spec__35_spec__37_spec__42_spec__49(x_5, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_1(x_9, x_3);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_FairSelling_swapOutcome___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_mod(x_4, x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_mod(x_6, x_1);
x_8 = lp_mathlib_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00MultilinearMap_alternatization___at___00Matrix_detRowAlternating___at___00Matrix_det___at___00Matrix_cramerMap___at___00Matrix_cramer___at___00Matrix_adjugate___at___00Matrix_SpecialLinearGroup_toGL___at___00Matrix_SpecialLinearGroup_mapGL___at___00CongruenceSubgroup_conjGL_spec__0_spec__0_spec__4_spec__10_spec__16_spec__21_spec__27_spec__32_spec__35_spec__37_spec__42_spec__49(x_5, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_1(x_9, x_3);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RequestProject_FairSelling_swapOutcome___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_swapOutcome___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_swapOutcome___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_swapOutcome___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
x_13 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_swapOutcome___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_swapOutcome(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_FairSelling_swapOutcome___redArg(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_SmallN(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_TwoAgents(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_SmallN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
