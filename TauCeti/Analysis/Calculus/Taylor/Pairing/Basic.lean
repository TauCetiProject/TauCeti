/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.InnerProductSpace.ProdInner
import TauCeti.Data.List.OfFn
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Taylor-monomial integral pairings

Over `[RCLike 𝕜]`, integrating iterated directional derivatives of shifted polynomial kernels
`(∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z` against a locally integrable function `v` on a set `s` expands
via powersets into `∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * c (t \ u)`, yielding `C^m` smoothness,
factor-by-factor spatial differentiation, and high-order directional vanishing.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Set
open scoped ContDiff InnerProductSpace

section Pointwise

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Any powerset combination `x ↦ ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * c (t \ u)` is `C^m`. -/
theorem contDiff_sum_powerset_prod_inner_mul {α : Type*} [DecidableEq α] {m : ℕ∞ω}
    (t : Finset α) (a : α → E) (c : Finset α → 𝕜) :
    ContDiff 𝕜 m (fun x => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * c (t \ u)) :=
  ContDiff.sum fun _ _ => (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff).mul contDiff_const

/-- Spatial Fréchet derivative of `x' ↦ ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x'⟫_𝕜) * c (t \ u)`. -/
theorem fderiv_sum_powerset_prod_inner_mul {α : Type*} [DecidableEq α]
    (t : Finset α) (a : α → E) (c : Finset α → 𝕜) (x h : E) :
    fderiv 𝕜 (fun x' => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x'⟫_𝕜) * c (t \ u)) x h =
      ∑ p ∈ t, ⟪a p, h⟫_𝕜 *
        ∑ v ∈ (t.erase p).powerset, (∏ l ∈ v, ⟪a l, x⟫_𝕜) * c (t.erase p \ v) := by
  have hsum := HasFDerivAt.fun_sum (x := x) fun u (_ : u ∈ t.powerset) =>
    ((HasFDerivAt.finsetProd (u := u) (g := fun l x' => ⟪a l, x'⟫_𝕜) (x := x)
      fun l _ => (innerSL 𝕜 (a l)).hasFDerivAt).mul_const (c (t \ u)))
  rw [hsum.fderiv, FunLike.coe_sum, Finset.sum_apply]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply, smul_eq_mul]
  have hrew : ∑ u ∈ t.powerset, c (t \ u) * (∑ p ∈ u, (∏ l ∈ u.erase p, ⟪a l, x⟫_𝕜) * ⟪a p, h⟫_𝕜) =
      ∑ p ∈ t, ∑ u ∈ t.powerset with p ∈ u,
        ⟪a p, h⟫_𝕜 * ((∏ l ∈ u.erase p, ⟪a l, x⟫_𝕜) * c (t \ u)) := by
    calc _ = ∑ u ∈ t.powerset, ∑ p ∈ t,
            if p ∈ u then ⟪a p, h⟫_𝕜 * ((∏ l ∈ u.erase p, ⟪a l, x⟫_𝕜) * c (t \ u)) else 0 :=
          Finset.sum_congr rfl fun u hu => by
            rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
              Finset.inter_eq_right.2 (Finset.mem_powerset.1 hu)]
            exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
  rw [hrew]; refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (·.erase p) (insert p ·)
    (fun u hu => Finset.mem_powerset.2 (Finset.erase_subset_erase p
      (Finset.mem_powerset.1 (Finset.mem_filter.1 hu).1)))
    (fun v hv => Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hp
      ((Finset.mem_powerset.1 hv).trans (Finset.erase_subset p t))), Finset.mem_insert_self p v⟩)
    (fun u hu => Finset.insert_erase (Finset.mem_filter.1 hu).2)
    (fun v hv => Finset.erase_insert fun hpv =>
      (Finset.mem_erase.1 (Finset.mem_powerset.1 hv hpv)).1 rfl) fun u hu => ?_
  have hsdiff : t \ u = t.erase p \ u.erase p := by
    ext q; by_cases hqp : q = p <;> simp [hqp, (Finset.mem_filter.1 hu).2]
  rw [hsdiff]

/-- Differentiating `x' ↦ ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x'⟫_𝕜) * c (t \ u)` along strictly
more than `t.card` directions vanishes identically. -/
theorem iteratedFDerivAlong_sum_powerset_prod_inner_mul_eq_zero {α : Type*} [DecidableEq α]
    (t : Finset α) (a : α → E) (c : Finset α → 𝕜) (vs : List E) (ht : t.card < vs.length) (x : E) :
    iteratedFDerivAlong 𝕜 vs (fun x' => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x'⟫_𝕜) * c (t \ u)) x =
      0 := by
  have hswap : (fun x' => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x'⟫_𝕜) * c (t \ u)) =
      fun x' => ∑ u ∈ t.powerset, c (t \ u) * ∏ l ∈ u, (innerSL 𝕜 (a l)) x' :=
    funext fun _ => Finset.sum_congr rfl fun _ _ => by simp [mul_comm]
  rw [hswap, iteratedFDerivAlong_fun_sum (n := ∞) t.powerset
    (fun _ _ => contDiff_const.mul (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff)) vs
    (by simp)]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [congrFun (iteratedFDerivAlong_const_mul
      (contDiff_prod (n := ∞) fun l _ => (innerSL 𝕜 (a l)).contDiff) _ vs (by simp)) x,
    congrFun (iteratedFDerivAlong_prod_clm_eq_zero (fun l => innerSL 𝕜 (a l)) u vs
      ((Finset.card_le_card (Finset.mem_powerset.1 hu)).trans_lt ht)) x, Pi.zero_apply, mul_zero]

/-- Evaluating `iteratedFDeriv` of a Taylor-monomial kernel on `a : Fin j → E` agrees with
`iteratedFDerivAlong` along `List.ofFn a`. -/
theorem iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong {j : ℕ} (a : Fin j → E)
    {φ : E → 𝕜} (hφ : ContDiff 𝕜 j φ) (x y : E) :
    iteratedFDeriv 𝕜 j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y a =
      iteratedFDerivAlong 𝕜 (List.ofFn a) (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y :=
  (iteratedFDerivAlong_ofFn_eq_iteratedFDeriv (((contDiff_prod fun l _ =>
    (innerSL 𝕜 (a l)).contDiff.comp (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ) _ _
    ).symm

/-- Inserting `v` at index `p` of `a` and dropping the `p`-th kernel factor pulls out `fderiv`. -/
theorem iteratedFDerivAlong_insertNth_prod_inner_sub_erase_mul {j : ℕ} (p : Fin (j + 1)) (v : E)
    (a : Fin j → E) {φ : E → 𝕜} (hφ : ContDiff 𝕜 (j + 1) φ) (x y : E) :
    iteratedFDerivAlong 𝕜 (List.ofFn (p.insertNth v a))
        (fun z => (∏ l ∈ Finset.univ.erase p,
          ⟪p.insertNth (α := fun _ => E) v a l, x - z⟫_𝕜) * φ z) y =
      fderiv 𝕜 (iteratedFDerivAlong 𝕜 (List.ofFn a)
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z)) y v := by
  have hqg : ContDiff 𝕜 (j + 1) (fun z => ∏ l : Fin j, ⟪a l, x - z⟫_𝕜) :=
    (contDiff_prod fun l _ =>
      (innerSL 𝕜 (a l)).contDiff.comp (contDiff_const.sub contDiff_id)).of_le le_top
  have herase : (fun z => (∏ l ∈ Finset.univ.erase p,
        ⟪p.insertNth (α := fun _ => E) v a l, x - z⟫_𝕜) * φ z) =
      fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z := funext fun _ => by
    have he : (Finset.univ : Finset (Fin (j + 1))).erase p = Finset.univ.map p.succAboveEmb := by
      rw [Fin.univ_succAbove j p, Finset.erase_cons]
    simp [he, Fin.insertNth_apply_succAbove]
  rw [herase, congrFun ((List.ofFn_insertNth_perm p v a).iteratedFDerivAlong_eq (hqg.mul hφ)
    (by simp)) y, iteratedFDerivAlong_cons_apply]

end Pointwise

section Pairing

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [MeasurableSpace E]

/-- Powerset expansion of a zero-order shifted inner-product integral against `w`. -/
theorem setIntegral_prod_inner_sub_right_mul_eq_sum {α : Type*} [DecidableEq α]
    {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {w : E → 𝕜}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_𝕜) * w y) s μ) (x : E) :
    ∫ y in s, (∏ l ∈ t, ⟪a l, x - y⟫_𝕜) * w y ∂μ =
      ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * ∫ y in s, (∏ l ∈ t \ u, -⟪a l, y⟫_𝕜) * w y ∂μ := by
  have hint : ∀ u ∈ t.powerset,
      IntegrableOn (fun y => (∏ l ∈ u, ⟪a l, x⟫_𝕜) * ((∏ l ∈ t \ u, -⟪a l, y⟫_𝕜) * w y)) s μ :=
    fun u _ => by
      have hneg : IntegrableOn (fun y => (∏ l ∈ t \ u, -⟪a l, y⟫_𝕜) * w y) s μ := by
        simpa only [IntegrableOn, Finset.prod_neg, mul_assoc] using
          (hw (t \ u) Finset.sdiff_subset).const_mul ((-1 : 𝕜) ^ (t \ u).card)
      exact hneg.const_mul _
  have hpt : ∀ y, (∏ l ∈ t, ⟪a l, x - y⟫_𝕜) * w y =
      ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * ((∏ l ∈ t \ u, -⟪a l, y⟫_𝕜) * w y) := fun y => by
    simp_rw [prod_inner_sub_right_eq_sum_powerset t a x y, Finset.sum_mul, mul_assoc]
  simp_rw [hpt]; rw [integral_finsetSum _ hint]
  exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _

/-- Every zero-order shifted inner-product pairing with integrable moments on `s` is `C^m`. -/
theorem contDiff_setIntegral_prod_inner_sub_right_mul {α : Type*} {μ : Measure E} {s : Set E}
    {m : ℕ∞ω} (t : Finset α) (a : α → E) {w : E → 𝕜}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_𝕜) * w y) s μ) :
    ContDiff 𝕜 m (fun x => ∫ y in s, (∏ l ∈ t, ⟪a l, x - y⟫_𝕜) * w y ∂μ) := by
  classical
  rw [funext (setIntegral_prod_inner_sub_right_mul_eq_sum t a hw)]
  exact contDiff_sum_powerset_prod_inner_mul (𝕜 := 𝕜) t a
    fun r => ∫ y in s, (∏ l ∈ r, -⟪a l, y⟫_𝕜) * w y ∂μ

/-- Spatial Fréchet derivative of a zero-order shifted inner-product integral on `s`. -/
theorem fderiv_setIntegral_prod_inner_sub_right_mul {α : Type*} [DecidableEq α] {μ : Measure E}
    {s : Set E} (t : Finset α) (a : α → E) {w : E → 𝕜}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_𝕜) * w y) s μ) (x h : E) :
    fderiv 𝕜 (fun x' => ∫ y in s, (∏ l ∈ t, ⟪a l, x' - y⟫_𝕜) * w y ∂μ) x h =
      ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ∫ y in s, (∏ l ∈ t.erase p, ⟪a l, x - y⟫_𝕜) * w y ∂μ := by
  rw [funext (setIntegral_prod_inner_sub_right_mul_eq_sum t a hw),
    fderiv_sum_powerset_prod_inner_mul (𝕜 := 𝕜) t a
      (fun r => ∫ y in s, (∏ l ∈ r, -⟪a l, y⟫_𝕜) * w y ∂μ) x h]
  exact Finset.sum_congr rfl fun p _ => congrArg (⟪a p, h⟫_𝕜 * ·)
    (setIntegral_prod_inner_sub_right_mul_eq_sum (t.erase p) a
      (fun v hv => hw v (hv.trans (Finset.erase_subset p t))) x).symm

/-- Set-integral conversion between `iteratedFDeriv` and `iteratedFDerivAlong` on Taylor kernels. -/
theorem setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong {μ : Measure E}
    {s : Set E} {j : ℕ} (a : Fin j → E) {φ : E → 𝕜} (hφ : ContDiff 𝕜 j φ) (v : E → 𝕜) (x : E) :
    ∫ y in s, iteratedFDeriv 𝕜 j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y a * v y ∂μ =
      ∫ y in s, iteratedFDerivAlong 𝕜 (List.ofFn a)
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ :=
  integral_congr_ae (.of_forall fun y => by
    dsimp only; rw [iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ x y])

variable [OpensMeasurableSpace E]

/-- Powerset expansion of a Taylor-monomial pairing (`iteratedFDerivAlong` form). -/
theorem setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum {α : Type*} [DecidableEq α]
    {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) (x : E) :
    ∫ y in s, iteratedFDerivAlong 𝕜 vs (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ =
      ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * ∫ y in s,
        iteratedFDerivAlong 𝕜 vs (fun z => (∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ := by
  let ψ : Finset α → E → 𝕜 := fun r z => (∏ l ∈ r, -⟪a l, z⟫_𝕜) * φ z
  have hψ : ∀ r, ContDiff 𝕜 n (ψ r) := fun _ =>
    ((contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff.neg).of_le le_top).mul hφ
  have hint : ∀ u, IntegrableOn (fun y => iteratedFDerivAlong 𝕜 vs (ψ (t \ u)) y * v y) s μ :=
    fun u => (hv.integrable_smul_left_of_hasCompactSupport
      ((hψ (t \ u)).iteratedFDerivAlong (m := 0) vs (by simpa using hvs)).continuous.continuousOn
      (hφc.mul_left.iteratedFDerivAlong 𝕜 vs)
      (((tsupport_iteratedFDerivAlong_subset 𝕜 vs _).trans tsupport_mul_subset_right).trans
        hφs)).integrableOn
  have hexp : (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) =
      fun z => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * ψ (t \ u) z :=
    funext fun z => by
      simp_rw [ψ, prod_inner_sub_right_eq_sum_powerset t a x z, Finset.sum_mul, mul_assoc]
  have hstep : ∀ y, iteratedFDerivAlong 𝕜 vs (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) y * v y =
      ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * (iteratedFDerivAlong 𝕜 vs (ψ (t \ u)) y * v y) :=
    fun y => by
      rw [hexp, iteratedFDerivAlong_fun_sum _ (fun u _ => contDiff_const.mul (hψ (t \ u))) vs hvs,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by
        rw [congrFun (iteratedFDerivAlong_const_mul (hψ (t \ u)) _ vs hvs) y, mul_assoc]
  simp_rw [hstep]; rw [integral_finsetSum _ fun u _ => (hint u).const_mul _]
  exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _

/-- Every Taylor-monomial pairing (`iteratedFDerivAlong` form) on `s` is `C^m` for every `m`. -/
theorem contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul {α : Type*} {μ : Measure E}
    {s : Set E} {m : ℕ∞ω} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜} (hφ : ContDiff 𝕜 n φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) (vs : List E) (hvs : vs.length ≤ n)
    {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) :
    ContDiff 𝕜 m (fun x => ∫ y in s, iteratedFDerivAlong 𝕜 vs
      (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ) := by
  classical
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs vs hvs hv)]
  exact contDiff_sum_powerset_prod_inner_mul (𝕜 := 𝕜) t a
    fun r => ∫ y in s, iteratedFDerivAlong 𝕜 vs (fun z => (∏ l ∈ r, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ

/-- `iteratedFDeriv` form of
`TauCeti.contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul`. -/
theorem contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul {μ : Measure E} {s : Set E}
    {m : ℕ∞ω} {j : ℕ} (a : Fin j → E) {φ : E → 𝕜} (hφ : ContDiff 𝕜 j φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) :
    ContDiff 𝕜 m (fun x => ∫ y in s, iteratedFDeriv 𝕜 j
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y a * v y ∂μ) := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ v]
  exact contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul Finset.univ a hφ hφc hφs
    (List.ofFn a) (by simp) hv

/-- Spatial Fréchet derivative of a Taylor-monomial pairing (`iteratedFDerivAlong` form). -/
theorem fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul {α : Type*} [DecidableEq α]
    {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) (vs : List E)
    (hvs : vs.length ≤ n) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) (x h : E) :
    fderiv 𝕜 (fun x' => ∫ y in s, iteratedFDerivAlong 𝕜 vs
        (fun z => (∏ l ∈ t, ⟪a l, x' - z⟫_𝕜) * φ z) y * v y ∂μ) x h =
      ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ∫ y in s, iteratedFDerivAlong 𝕜 vs
        (fun z => (∏ l ∈ t.erase p, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ := by
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs vs hvs hv),
    fderiv_sum_powerset_prod_inner_mul (𝕜 := 𝕜) t a (fun r => ∫ y in s,
      iteratedFDerivAlong 𝕜 vs (fun z => (∏ l ∈ r, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ) x h]
  exact Finset.sum_congr rfl fun p _ => congrArg (⟪a p, h⟫_𝕜 * ·)
    (setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum (t.erase p) a hφ hφc hφs vs hvs hv
      x).symm

/-- Differentiating a Taylor-monomial pairing of degree `t.card` along strictly more than `t.card`
directions vanishes identically. -/
theorem iteratedFDerivAlong_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_zero
    {α : Type*} {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (ws : List E) (hws : ws.length ≤ n) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ)
    (vs : List E) (ht : t.card < vs.length) (x : E) :
    iteratedFDerivAlong 𝕜 vs (fun x' => ∫ y in s, iteratedFDerivAlong 𝕜 ws
      (fun z => (∏ l ∈ t, ⟪a l, x' - z⟫_𝕜) * φ z) y * v y ∂μ) x = 0 := by
  classical
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs ws hws hv)]
  exact iteratedFDerivAlong_sum_powerset_prod_inner_mul_eq_zero (𝕜 := 𝕜) t a
    (fun r => ∫ y in s, iteratedFDerivAlong 𝕜 ws (fun z => (∏ l ∈ r, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ)
    vs ht x

/-- `iteratedFDeriv` form of
`TauCeti.iteratedFDerivAlong_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_zero`. -/
theorem iteratedFDerivAlong_setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_zero
    {μ : Measure E} {s : Set E} {r : ℕ} (a : Fin r → E) {φ : E → 𝕜} (hφ : ContDiff 𝕜 r φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ)
    (vs : List E) (hr : r < vs.length) (x : E) :
    iteratedFDerivAlong 𝕜 vs (fun x' => ∫ y in s, iteratedFDeriv 𝕜 r
      (fun z => (∏ l : Fin r, ⟪a l, x' - z⟫_𝕜) * φ z) y a * v y ∂μ) x = 0 := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ v]
  exact iteratedFDerivAlong_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_zero
    Finset.univ a hφ hφc hφs (List.ofFn a) (by simp) hv vs (by simpa using hr) x

end Pairing

end TauCeti
