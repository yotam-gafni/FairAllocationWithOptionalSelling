// Lean compiler output
// Module: RequestProject.TPSSefxCharge
// Imports: public import Init public import Mathlib public import RequestProject.Selling public import RequestProject.EpsEnvy public import RequestProject.LemmaEleven public import RequestProject.TPSApprox public import RequestProject.TPSCompute public import RequestProject.TPSSefxGeneral
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
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__1___boxed(lean_object*);
static lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__1;
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__0___boxed(lean_object*);
lean_object* lp_RequestProject_FairSelling_trunc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_saleLoss___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_biUnion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_pool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_soldSet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_soldSet___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__0;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
static lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__2;
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_saleLoss(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_pool___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_saleLoss___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_2);
x_5 = lp_RequestProject_FairSelling_trunc___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_saleLoss(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject_FairSelling_ChargeTPS_saleLoss___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_soldSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_List_finRange(x_2);
x_6 = lp_mathlib_Finset_biUnion___redArg(x_1, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_soldSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_FairSelling_ChargeTPS_CStage_soldSet___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_pool___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = lp_RequestProject_FairSelling_ChargeTPS_CStage_soldSet___redArg(x_2, x_3, x_4);
x_7 = l_List_finRange(x_3);
lean_inc_ref(x_2);
x_8 = lp_mathlib_Finset_biUnion___redArg(x_2, x_7, x_5);
lean_inc_ref(x_2);
x_9 = lp_mathlib_Multiset_ndunion___redArg(x_2, x_6, x_8);
x_10 = lp_mathlib_Multiset_sub___redArg(x_2, x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_pool(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RequestProject_FairSelling_ChargeTPS_CStage_pool___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lp_mathlib_Real_instAddCommMonoid;
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_8);
lean_inc(x_2);
x_11 = lp_RequestProject_FairSelling_ChargeTPS_CStage_soldSet___redArg(x_1, x_2, x_3);
x_12 = l_List_finRange(x_2);
x_13 = lp_mathlib_Finset_sum___redArg(x_4, x_12, x_10);
x_14 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_7);
lean_ctor_set(x_15, 4, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RequestProject_FairSelling_ChargeTPS_CStage_toStage___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___lam__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_2 = lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__1;
x_3 = lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__0;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_2);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__2;
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RequestProject_FairSelling_ChargeTPS_emptyCStage(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_Selling(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_EpsEnvy(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_LemmaEleven(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_TPSApprox(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_TPSCompute(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_TPSSefxGeneral(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_TPSSefxCharge(uint8_t builtin) {
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
res = initialize_RequestProject_RequestProject_EpsEnvy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_LemmaEleven(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_TPSApprox(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_TPSCompute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_TPSSefxGeneral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__0 = _init_lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__0();
lean_mark_persistent(lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__0);
lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__1 = _init_lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__1();
lean_mark_persistent(lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__1);
lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__2 = _init_lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__2();
lean_mark_persistent(lp_RequestProject_FairSelling_ChargeTPS_emptyCStage___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
