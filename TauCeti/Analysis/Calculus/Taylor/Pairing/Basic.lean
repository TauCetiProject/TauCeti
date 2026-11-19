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

Integrating iterated directional derivatives of shifted polynomial kernels
`(∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z` against a locally integrable function `v` on a set `s` produces
polynomials in `x` whose coefficients are integrals independent of `x`.

This file develops the pure calculus and integration infrastructure for such pairings over `ℝ` or
`ℂ` (`[RCLike 𝕜]`), without assuming openness of `s`, finite dimensionality of `E`, translation
invariance of `μ`, or any Sobolev or `MvPolynomial` structure:

* Pointwise kernel identities comparing the product rule and powerset expansion for the derivative
  in `x`, converting `iteratedFDeriv` to `iteratedFDerivAlong`, and inserting a direction via
  `Fin.insertNth`.
* Zero-order shifted inner-product pairings against arbitrary weights with integrable monomial
  moments (`TauCeti.setIntegral_prod_inner_sub_right_mul_eq_sum`,
  `TauCeti.contDiff_setIntegral_prod_inner_sub_right_mul`,
  `TauCeti.fderiv_setIntegral_prod_inner_sub_right_mul`).
* Powerset expansion of the integral pairing in `x`, isolating all `x`-dependence outside the
  integral (`TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum`,
  `TauCeti.setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_sum`).
* `C^m` smoothness for every `m : ℕ∞ω`
  (`TauCeti.contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul`,
  `TauCeti.contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul`).
* Spatial Fréchet differentiation under the integral and `iteratedFDerivAlong`
  (`TauCeti.fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul`).
* Vanishing of directional derivatives of order strictly greater than the monomial degree
  (`TauCeti.iteratedFDerivAlong_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_zero`,
  `TauCeti.iteratedFDerivAlong_setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_zero`).

## Main declarations

* `TauCeti.sum_erase_prod_inner_sub_right_eq_sum_powerset_fderiv`: product-rule vs powerset
  derivative identity for `x' ↦ ∏ l ∈ t, ⟪a l, x' - z⟫_𝕜`.
* `TauCeti.iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong`: converts `iteratedFDeriv`
  of a Taylor-monomial kernel to `iteratedFDerivAlong`.
* `TauCeti.iteratedFDerivAlong_insertNth_prod_inner_sub_erase_mul`: permutation-invariance step
  pulling out the `p`-th inserted direction into an outer `fderiv`.
* `TauCeti.setIntegral_prod_inner_sub_right_mul_eq_sum`,
  `TauCeti.contDiff_setIntegral_prod_inner_sub_right_mul`, and
  `TauCeti.fderiv_setIntegral_prod_inner_sub_right_mul`: zero-order powerset expansion, `C^m`
  smoothness, and spatial derivative against an arbitrary weight with integrable monomial moments.
* `TauCeti.setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong`: set-integral
  conversion between `iteratedFDeriv` and `iteratedFDerivAlong`.
* `TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum` and
  `TauCeti.setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_sum`: powerset expansions factoring
  `x` out of the integral.
* `TauCeti.contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul` and
  `TauCeti.contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul`: `C^m` smoothness for every
  `m : ℕ∞ω`.
* `TauCeti.fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul`: differentiating a
  Taylor-monomial pairing in `x` along `h` drops one factor at a time.
* `TauCeti.iteratedFDerivAlong_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_zero` and
  `TauCeti.iteratedFDerivAlong_setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_zero`: higher-order
  directional derivatives strictly above the degree vanish identically.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Set
open scoped ContDiff InnerProductSpace

section Pointwise

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Comparing the product-rule and powerset derivatives of `x' ↦ ∏ l ∈ t, ⟪a l, x' - z⟫_𝕜` with
respect to `x'` gives a pointwise identity in `z`. -/
theorem sum_erase_prod_inner_sub_right_eq_sum_powerset_fderiv {α : Type*} [DecidableEq α]
    (t : Finset α) (a : α → E) (x h z : E) :
    ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ∏ l ∈ t.erase p, ⟪a l, x - z⟫_𝕜 =
      ∑ u ∈ t.powerset,
        fderiv 𝕜 (fun x' => ∏ l ∈ u, ⟪a l, x'⟫_𝕜) x h * ∏ l ∈ t \ u, -⟪a l, z⟫_𝕜 := by
  let c : Finset α → E → 𝕜 := fun u x' => ∏ l ∈ u, ⟪a l, x'⟫_𝕜
  let ψ : Finset α → 𝕜 := fun u => ∏ l ∈ t \ u, -⟪a l, z⟫_𝕜
  have hc : ∀ u, Differentiable 𝕜 (c u) := fun u =>
    (contDiff_prod (n := 1) fun l _ => (innerSL 𝕜 (a l)).contDiff).differentiable one_ne_zero
  have hfun : (fun x' => ∏ l ∈ t, ⟪a l, x' - z⟫_𝕜) =
      fun x' => ∑ u ∈ t.powerset, c u x' * ψ u :=
    funext fun x' => prod_inner_sub_right_eq_sum_powerset t a x' z
  have hp : HasFDerivAt (fun x' => ∏ l ∈ t, ⟪a l, x' - z⟫_𝕜)
      (∑ p ∈ t, (∏ l ∈ t.erase p, ⟪a l, x - z⟫_𝕜) • innerSL 𝕜 (a p)) x :=
    HasFDerivAt.finsetProd fun l _ => by
      have h1 : HasFDerivAt (fun x' => ⟪a l, x'⟫_𝕜 - ⟪a l, z⟫_𝕜) (innerSL 𝕜 (a l)) x :=
        (innerSL 𝕜 (a l)).hasFDerivAt.sub_const _
      simpa [inner_sub_right] using h1
  have hd2 : HasFDerivAt (fun x' => ∑ u ∈ t.powerset, c u x' * ψ u)
      (∑ u ∈ t.powerset, ψ u • fderiv 𝕜 (c u) x) x :=
    HasFDerivAt.fun_sum fun u _ => ((hc u x).hasFDerivAt).mul_const (ψ u)
  have heq := congrArg (fun L : E →L[𝕜] 𝕜 => L h) (hp.unique (hfun ▸ hd2))
  simp only [c, ψ, smul_apply, FunLike.coe_sum, Finset.sum_apply,
    innerSL_apply_apply, smul_eq_mul] at heq ⊢
  exact (Finset.sum_congr rfl fun p _ => mul_comm _ _).trans
    (heq.trans (Finset.sum_congr rfl fun u _ => mul_comm _ _))

/-- Evaluating `iteratedFDeriv` of a Taylor-monomial kernel on `a : Fin j → E` agrees with
`iteratedFDerivAlong` along `List.ofFn a`. -/
theorem iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong {j : ℕ} (a : Fin j → E)
    {φ : E → 𝕜} (hφ : ContDiff 𝕜 j φ) (x y : E) :
    iteratedFDeriv 𝕜 j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y a =
      iteratedFDerivAlong 𝕜 (List.ofFn a) (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y := by
  have hc : ContDiff 𝕜 j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) :=
    ((contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ
  rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hc]

/-- Inserting a direction `v` at index `p` of `a : Fin j → E` and dropping the `p`-th factor of
the shifted inner-product kernel pulls out the derivative along `v` as an outer `fderiv`. -/
theorem iteratedFDerivAlong_insertNth_prod_inner_sub_erase_mul {j : ℕ} (p : Fin (j + 1)) (v : E)
    (a : Fin j → E) {φ : E → 𝕜} (hφ : ContDiff 𝕜 (j + 1) φ) (x y : E) :
    iteratedFDerivAlong 𝕜 (List.ofFn (p.insertNth v a))
        (fun z => (∏ l ∈ Finset.univ.erase p,
          ⟪p.insertNth (α := fun _ => E) v a l, x - z⟫_𝕜) * φ z) y =
      fderiv 𝕜 (iteratedFDerivAlong 𝕜 (List.ofFn a)
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z)) y v := by
  have hqg : ContDiff 𝕜 (j + 1) (fun z => ∏ l : Fin j, ⟪a l, x - z⟫_𝕜) :=
    (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top
  have herase : (fun z => (∏ l ∈ Finset.univ.erase p,
        ⟪p.insertNth (α := fun _ => E) v a l, x - z⟫_𝕜) * φ z) =
      fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z := by
    funext z
    have he : (Finset.univ : Finset (Fin (j + 1))).erase p = Finset.univ.map p.succAboveEmb := by
      rw [Fin.univ_succAbove j p, Finset.erase_cons]
    simp [he, Fin.insertNth_apply_succAbove]
  rw [herase, congrFun ((List.ofFn_insertNth_perm p v a).iteratedFDerivAlong_eq (hqg.mul hφ)
    (by simp)) y, iteratedFDerivAlong_cons_apply]

end Pointwise

section Pairing

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [MeasurableSpace E]

/-- Powerset expansion of a zero-order shifted inner-product integral against an arbitrary weight
`w` whose monomial moments `y ↦ (∏ l ∈ v, ⟪a l, y⟫_𝕜) * w y` are integrable on `s` for `v ⊆ t`. -/
theorem setIntegral_prod_inner_sub_right_mul_eq_sum {α : Type*} [DecidableEq α]
    {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {w : E → 𝕜}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_𝕜) * w y) s μ) (x : E) :
    ∫ y in s, (∏ l ∈ t, ⟪a l, x - y⟫_𝕜) * w y ∂μ =
      ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) *
        ∫ y in s, (∏ l ∈ t \ u, -⟪a l, y⟫_𝕜) * w y ∂μ := by
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
  simp_rw [hpt]
  rw [integral_finsetSum _ hint]
  exact Finset.sum_congr rfl fun u _ => integral_const_mul _ _

/-- Every zero-order shifted inner-product pairing against a weight `w` with integrable monomial
moments on `s` is `C^m` for every `m : ℕ∞ω`. -/
theorem contDiff_setIntegral_prod_inner_sub_right_mul {α : Type*}
    {μ : Measure E} {s : Set E} {m : ℕ∞ω} (t : Finset α) (a : α → E) {w : E → 𝕜}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_𝕜) * w y) s μ) :
    ContDiff 𝕜 m (fun x => ∫ y in s, (∏ l ∈ t, ⟪a l, x - y⟫_𝕜) * w y ∂μ) := by
  classical
  rw [funext (setIntegral_prod_inner_sub_right_mul_eq_sum t a hw)]
  exact ContDiff.sum fun u _ =>
    (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff).mul contDiff_const

/-- Spatial Fréchet derivative of a zero-order shifted inner-product integral against an arbitrary
weight `w` with integrable monomial moments on `s`. -/
theorem fderiv_setIntegral_prod_inner_sub_right_mul {α : Type*} [DecidableEq α]
    {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {w : E → 𝕜}
    (hw : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, ⟪a l, y⟫_𝕜) * w y) s μ) (x h : E) :
    fderiv 𝕜 (fun x' => ∫ y in s, (∏ l ∈ t, ⟪a l, x' - y⟫_𝕜) * w y ∂μ) x h =
      ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ∫ y in s, (∏ l ∈ t.erase p, ⟪a l, x - y⟫_𝕜) * w y ∂μ := by
  let c : Finset α → E → 𝕜 := fun u x' => ∏ l ∈ u, ⟪a l, x'⟫_𝕜
  have hc : ∀ u, Differentiable 𝕜 (c u) := fun u =>
    (contDiff_prod (n := 1) fun l _ => (innerSL 𝕜 (a l)).contDiff).differentiable one_ne_zero
  have hneg : ∀ v ⊆ t, IntegrableOn (fun y => (∏ l ∈ v, -⟪a l, y⟫_𝕜) * w y) s μ := fun v hv => by
    simpa only [IntegrableOn, Finset.prod_neg, mul_assoc] using
      (hw v hv).const_mul ((-1 : 𝕜) ^ v.card)
  have hsub : ∀ p ∈ t, IntegrableOn (fun y => (∏ l ∈ t.erase p, ⟪a l, x - y⟫_𝕜) * w y) s μ :=
    fun p _ => by
      have hpt : ∀ y, (∏ l ∈ t.erase p, ⟪a l, x - y⟫_𝕜) * w y =
          ∑ u ∈ (t.erase p).powerset,
            (∏ l ∈ u, ⟪a l, x⟫_𝕜) * ((∏ l ∈ (t.erase p) \ u, -⟪a l, y⟫_𝕜) * w y) := fun y => by
        simp_rw [prod_inner_sub_right_eq_sum_powerset (t.erase p) a x y, Finset.sum_mul, mul_assoc]
      simp_rw [hpt]
      exact integrable_finsetSum _ fun u _ =>
        (hneg _ (Finset.sdiff_subset.trans (Finset.erase_subset _ _))).const_mul _
  rw [funext (setIntegral_prod_inner_sub_right_mul_eq_sum t a hw),
    (HasFDerivAt.fun_sum fun u _ => ((hc u x).hasFDerivAt).mul_const _).fderiv,
    FunLike.coe_sum, Finset.sum_apply]
  simp only [smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun u _ => (mul_comm _ _).trans (integral_const_mul _ _).symm,
    ← integral_finsetSum _ fun u _ => (hneg _ Finset.sdiff_subset).const_mul _]
  calc ∫ y in s, ∑ u ∈ t.powerset,
          fderiv 𝕜 (c u) x h * ((∏ l ∈ t \ u, -⟪a l, y⟫_𝕜) * w y) ∂μ
      = ∫ y in s, ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ((∏ l ∈ t.erase p, ⟪a l, x - y⟫_𝕜) * w y) ∂μ :=
        integral_congr_ae (.of_forall fun y => by
          dsimp only
          have hmul := congrArg (· * w y)
            (sum_erase_prod_inner_sub_right_eq_sum_powerset_fderiv t a x h y)
          simpa only [c, Finset.sum_mul, mul_assoc] using hmul.symm)
    _ = ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ∫ y in s, (∏ l ∈ t.erase p, ⟪a l, x - y⟫_𝕜) * w y ∂μ := by
        rw [integral_finsetSum _ fun p hp => (hsub p hp).const_mul _]
        exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _

/-- Set-integral conversion between `iteratedFDeriv` and `iteratedFDerivAlong` for Taylor-monomial
kernels against an arbitrary function `v` on any set `s`. -/
theorem setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong
    {μ : Measure E} {s : Set E} {j : ℕ} (a : Fin j → E) {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 j φ) (v : E → 𝕜) (x : E) :
    ∫ y in s, iteratedFDeriv 𝕜 j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y a * v y ∂μ =
      ∫ y in s, iteratedFDerivAlong 𝕜 (List.ofFn a)
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ :=
  integral_congr_ae (.of_forall fun y => by
    dsimp only
    rw [iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ x y])

variable [OpensMeasurableSpace E]

/-- Powerset expansion of a Taylor-monomial pairing (`iteratedFDerivAlong` form): all
`x`-dependence factors out of both `iteratedFDerivAlong` and the set integral over `s`. -/
theorem setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum {α : Type*} [DecidableEq α]
    {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) (x : E) :
    ∫ y in s, iteratedFDerivAlong 𝕜 vs
        (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ =
      ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) *
        ∫ y in s, iteratedFDerivAlong 𝕜 vs
          (fun z => (∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ := by
  let ψ : Finset α → E → 𝕜 := fun u z => (∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) * φ z
  have hg : ∀ u : Finset α, ContDiff 𝕜 n (fun z => ∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) :=
    fun u => (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff.neg).of_le le_top
  have hψ : ∀ u, ContDiff 𝕜 n (ψ u) := fun u => (hg u).mul hφ
  have hint : ∀ u, IntegrableOn (fun y => iteratedFDerivAlong 𝕜 vs (ψ u) y * v y) s μ := fun u =>
    (hv.integrable_smul_left_of_hasCompactSupport
      ((hψ u).iteratedFDerivAlong (m := 0) vs (by simpa using hvs)).continuous
      (hφc.mul_left.iteratedFDerivAlong 𝕜 vs)
      (((tsupport_iteratedFDerivAlong_subset 𝕜 vs _).trans tsupport_mul_subset_right).trans
        hφs)).integrableOn
  have hexp : (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) =
      fun z => ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * ψ u z := by
    funext z
    simp_rw [ψ, prod_inner_sub_right_eq_sum_powerset t a x z, Finset.sum_mul, mul_assoc]
  have hstep : ∀ y, iteratedFDerivAlong 𝕜 vs (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) y * v y =
      ∑ u ∈ t.powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) * (iteratedFDerivAlong 𝕜 vs (ψ u) y * v y) :=
    fun y => by
      rw [hexp, iteratedFDerivAlong_fun_sum _ (fun u _ => contDiff_const.mul (hψ u)) vs hvs,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by
        rw [congrFun (iteratedFDerivAlong_const_mul (hψ u) _ vs hvs) y, mul_assoc]
  simp_rw [hstep]
  rw [integral_finsetSum _ fun u _ => (hint u).const_mul _]
  exact Finset.sum_congr rfl fun u _ => integral_const_mul _ _

/-- Powerset expansion of a Taylor-monomial pairing (`iteratedFDeriv` form). -/
theorem setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_sum
    {μ : Measure E} {s : Set E} {j : ℕ} (a : Fin j → E) {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) (x : E) :
    ∫ y in s, iteratedFDeriv 𝕜 j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y a * v y ∂μ =
      ∑ u ∈ (Finset.univ : Finset (Fin j)).powerset, (∏ l ∈ u, ⟪a l, x⟫_𝕜) *
        ∫ y in s, iteratedFDerivAlong 𝕜 (List.ofFn a)
          (fun z => (∏ l ∈ Finset.univ \ u, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ := by
  rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ v x,
    setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum Finset.univ a hφ hφc hφs
      (List.ofFn a) (by simp) hv x]

/-- Every Taylor-monomial pairing (`iteratedFDerivAlong` form) against a locally integrable
function on an arbitrary set `s` is `C^m` for every `m : ℕ∞ω`. -/
theorem contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul {α : Type*}
    {μ : Measure E} {s : Set E} {m : ℕ∞ω} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) :
    ContDiff 𝕜 m (fun x => ∫ y in s, iteratedFDerivAlong 𝕜 vs
      (fun z => (∏ l ∈ t, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ) := by
  classical
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs vs hvs hv)]
  exact ContDiff.sum fun u _ =>
    (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff).mul contDiff_const

/-- Every Taylor-monomial pairing (`iteratedFDeriv` form) against a locally integrable function on
an arbitrary set `s` is `C^m` for every `m : ℕ∞ω`. -/
theorem contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {μ : Measure E} {s : Set E} {m : ℕ∞ω} {j : ℕ} (a : Fin j → E) {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) :
    ContDiff 𝕜 m (fun x => ∫ y in s, iteratedFDeriv 𝕜 j
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_𝕜) * φ z) y a * v y ∂μ) := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ v]
  exact contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul Finset.univ a hφ hφc hφs
    (List.ofFn a) (by simp) hv

/-- Spatial Fréchet derivative of a single Taylor-monomial pairing: differentiating in `x` along
`h` differentiates the polynomial factor `∏ l ∈ t, ⟪a l, x - z⟫_𝕜` factor by factor under the
integral and `iteratedFDerivAlong`. -/
theorem fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul {α : Type*} [DecidableEq α]
    {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) (x h : E) :
    fderiv 𝕜 (fun x' => ∫ y in s, iteratedFDerivAlong 𝕜 vs
        (fun z => (∏ l ∈ t, ⟪a l, x' - z⟫_𝕜) * φ z) y * v y ∂μ) x h =
      ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ∫ y in s, iteratedFDerivAlong 𝕜 vs
        (fun z => (∏ l ∈ t.erase p, ⟪a l, x - z⟫_𝕜) * φ z) y * v y ∂μ := by
  let ψ : Finset α → E → 𝕜 := fun u z => (∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) * φ z
  let gp : α → E → 𝕜 := fun p z => (∏ l ∈ t.erase p, ⟪a l, x - z⟫_𝕜) * φ z
  let c : Finset α → E → 𝕜 := fun u x' => ∏ l ∈ u, ⟪a l, x'⟫_𝕜
  have hc : ∀ u, Differentiable 𝕜 (c u) := fun u =>
    (contDiff_prod (n := 1) fun l _ => (innerSL 𝕜 (a l)).contDiff).differentiable one_ne_zero
  have hint_of : ∀ {g : E → 𝕜}, ContDiff 𝕜 n g →
      IntegrableOn (fun y => iteratedFDerivAlong 𝕜 vs (fun z => g z * φ z) y * v y) s μ :=
    fun hg => (hv.integrable_smul_left_of_hasCompactSupport
      ((hg.mul hφ).iteratedFDerivAlong (m := 0) vs (by simpa using hvs)).continuous
      (hφc.mul_left.iteratedFDerivAlong 𝕜 vs)
      (((tsupport_iteratedFDerivAlong_subset 𝕜 vs _).trans tsupport_mul_subset_right).trans
        hφs)).integrableOn
  have hgψ : ∀ u : Finset α, ContDiff 𝕜 n (fun z => ∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) := fun _ =>
    (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff.neg).of_le le_top
  have hggp : ∀ p : α, ContDiff 𝕜 n (fun z => ∏ l ∈ t.erase p, ⟪a l, x - z⟫_𝕜) := fun _ =>
    (contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top
  have hpt_eq : (fun z => ∑ p ∈ t, ⟪a p, h⟫_𝕜 * gp p z) =
      fun z => ∑ u ∈ t.powerset, fderiv 𝕜 (c u) x h * ψ u z := funext fun z => by
    have hmul := congrArg (· * φ z)
      (sum_erase_prod_inner_sub_right_eq_sum_powerset_fderiv t a x h z)
    simpa only [Finset.sum_mul, mul_assoc, c, ψ, gp] using hmul
  -- Expand via powersets, differentiate in `x`, and regroup inside the integral.
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs vs hvs hv),
    (HasFDerivAt.fun_sum fun u _ => ((hc u x).hasFDerivAt).mul_const _).fderiv,
    FunLike.coe_sum, Finset.sum_apply]
  simp only [smul_apply, smul_eq_mul]
  calc ∑ u ∈ t.powerset, (∫ y in s, iteratedFDerivAlong 𝕜 vs (ψ u) y * v y ∂μ) * fderiv 𝕜 (c u) x h
      = ∫ y in s, (∑ u ∈ t.powerset,
          iteratedFDerivAlong 𝕜 vs (fun z => fderiv 𝕜 (c u) x h * ψ u z) y) * v y ∂μ := by
        rw [Finset.sum_congr rfl fun u _ => (mul_comm _ _).trans (integral_const_mul _ _).symm,
          ← integral_finsetSum _ fun u _ => (hint_of (hgψ u)).const_mul _]
        refine integral_congr_ae (.of_forall fun y => by
          dsimp only; rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun u _ => by
            rw [congrFun (iteratedFDerivAlong_const_mul ((hgψ u).mul hφ) _ vs hvs) y, mul_assoc])
    _ = ∫ y in s, (∑ p ∈ t,
          iteratedFDerivAlong 𝕜 vs (fun z => ⟪a p, h⟫_𝕜 * gp p z) y) * v y ∂μ :=
        integral_congr_ae (.of_forall fun y => by
          dsimp only
          rw [← iteratedFDerivAlong_fun_sum _ (fun u _ => contDiff_const.mul ((hgψ u).mul hφ))
                vs hvs, ← hpt_eq,
            iteratedFDerivAlong_fun_sum _ (fun p _ => contDiff_const.mul ((hggp p).mul hφ))
              vs hvs])
    _ = ∑ p ∈ t, ⟪a p, h⟫_𝕜 * ∫ y in s, iteratedFDerivAlong 𝕜 vs (gp p) y * v y ∂μ := by
        simp_rw [congrFun (iteratedFDerivAlong_const_mul (f := gp _) ((hggp _).mul hφ) _ vs hvs),
          Finset.sum_mul, mul_assoc]
        rw [integral_finsetSum _ fun p _ => (hint_of (hggp p)).const_mul _]
        exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _

/-- Differentiating a Taylor-monomial pairing (`iteratedFDerivAlong` form) of degree `t.card`
along strictly more than `t.card` directions vanishes identically. -/
theorem iteratedFDerivAlong_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_zero
    {α : Type*} {μ : Measure E} {s : Set E} (t : Finset α) (a : α → E) {n : ℕ∞ω} {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (ws : List E) (hws : ws.length ≤ n) {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ)
    (vs : List E) (ht : t.card < vs.length) (x : E) :
    iteratedFDerivAlong 𝕜 vs (fun x' => ∫ y in s, iteratedFDerivAlong 𝕜 ws
      (fun z => (∏ l ∈ t, ⟪a l, x' - z⟫_𝕜) * φ z) y * v y ∂μ) x = 0 := by
  classical
  have hexp : (fun x' => ∫ y in s, iteratedFDerivAlong 𝕜 ws
        (fun z => (∏ l ∈ t, ⟪a l, x' - z⟫_𝕜) * φ z) y * v y ∂μ) =
      fun x' => ∑ u ∈ t.powerset,
        (∫ y in s, iteratedFDerivAlong 𝕜 ws
          (fun z => (∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ) * ∏ l ∈ u, ⟪a l, x'⟫_𝕜 := by
    funext x'
    rw [setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum t a hφ hφc hφs ws hws hv x']
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hexp, iteratedFDerivAlong_fun_sum (n := ∞) t.powerset
    (f := fun u x' => (∫ y in s, iteratedFDerivAlong 𝕜 ws
      (fun z => (∏ l ∈ t \ u, -⟪a l, z⟫_𝕜) * φ z) y * v y ∂μ) * ∏ l ∈ u, ⟪a l, x'⟫_𝕜)
    (fun _ _ => contDiff_const.mul (contDiff_prod fun _ _ => (innerSL 𝕜 _).contDiff)) vs (by simp)]
  refine Finset.sum_eq_zero fun u hu => ?_
  have hprod : ContDiff 𝕜 ∞ (fun x' => ∏ l ∈ u, ⟪a l, x'⟫_𝕜) :=
    contDiff_prod fun l _ => (innerSL 𝕜 (a l)).contDiff
  rw [congrFun (iteratedFDerivAlong_const_mul hprod _ vs (by simp)) x]
  simp_rw [← innerSL_apply_apply 𝕜]
  have hcu : u.card < vs.length :=
    (Finset.card_le_card (Finset.mem_powerset.1 hu)).trans_lt ht
  rw [congrFun (iteratedFDerivAlong_prod_clm_eq_zero (𝕜 := 𝕜) (fun l => innerSL 𝕜 (a l)) u vs hcu)
    x, Pi.zero_apply, mul_zero]

/-- Differentiating a Taylor-monomial pairing (`iteratedFDeriv` form) of degree `r` along strictly
more than `r` directions vanishes identically. -/
theorem iteratedFDerivAlong_setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_zero
    {μ : Measure E} {s : Set E} {r : ℕ} (a : Fin r → E) {φ : E → 𝕜}
    (hφ : ContDiff 𝕜 r φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    {v : E → 𝕜} (hv : LocallyIntegrableOn v s μ) (vs : List E) (hr : r < vs.length) (x : E) :
    iteratedFDerivAlong 𝕜 vs (fun x' => ∫ y in s, iteratedFDeriv 𝕜 r
      (fun z => (∏ l : Fin r, ⟪a l, x' - z⟫_𝕜) * φ z) y a * v y ∂μ) x = 0 := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ v]
  exact iteratedFDerivAlong_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_zero
    Finset.univ a hφ hφc hφs (List.ofFn a) (by simp) hv vs (by simpa using hr) x

end Pairing

end TauCeti
