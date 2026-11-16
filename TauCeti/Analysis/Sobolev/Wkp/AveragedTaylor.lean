/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.IntegrationByParts
import TauCeti.Analysis.Sobolev.Wkp.IntegrationByParts
import TauCeti.Data.List.OfFn
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Integral.ClosedBall
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Averaged Taylor pairings, weak-derivative commutation, and diameter bounds on `W^{k,p}`

Integrating Taylor-monomial kernels `(∏ l, ⟪a l, x - z⟫_ℝ) * φ z` or shifted full contractions
`fullContractL k (x - y) (iteratedGradient k u y) * φ y` against a compactly supported weight `φ`
on an open set `Ω` produces smooth polynomial approximations to `u ∈ W^{m,p}(Ω)` (`1 ≤ p ≤ ∞`),
as in Brenner–Scott (§§4.1–4.3).

This file develops four ingredients for averaged Taylor polynomials without assuming finite
Sobolev exponent (`p = ∞` included) or smooth-function density:

1. **Smoothness and single-step weak-derivative commutation (`section TaylorExpansion`):**
   factoring `(x - z)` via powersets makes every Taylor-monomial pairing against a locally
   integrable function `C^m` for all `m : ℕ∞ω`
   (`TauCeti.contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul`,
   `TauCeti.contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul`), and differentiating the
   orthonormal-basis sum along `h` transfers one weak directional derivative onto `u` without
   translation invariance
   (`TauCeti.HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul`).
2. **Higher-order commutation on `W^{k,p}` (`section WkpCommutation`):**
   contracting the order-`j` classical `iteratedGradientChain` of the degree-`m` averaged Taylor
   sum of `u ∈ W^{j+1,p}(Ω)` yields the degree-`(m - j - 1)` averaged Taylor sum of the `j`-th
   contracted weak derivative
   (`TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`),
   and differentiating shifted full contractions in `x` commutes with `TauCeti.Wkp.lineDerivL` for
   arbitrary continuous compactly supported weights `φ`
   (`TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq`,
   `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq`).
3. **Membership in `TauCeti.polynomialsDegLE` (`section Polynomiality`):**
   on `EuclideanSpace ℝ ι`, both individual Taylor-monomial pairings and contracted field integrals
   belong to `TauCeti.polynomialsDegLE ι m`
   (`TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE`,
   `TauCeti.setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE`).
4. **`Lᵖ(Ω) → L^∞` diameter and chunkiness bounds (`section Bounds`):**
   for bounded `Ω` with `diam Ω ≤ γ * ρ` and `φ` supported in `closedBall x₀ ρ` satisfying
   `‖φ y‖ ≤ M * ρ ^ (-finrank ℝ E)` on `Ω`, contracted integrals at `x ∈ closure Ω` obey explicit
   `diam Ω` and chunkiness scaling (`TauCeti.norm_setIntegral_fullContractL_sub_mul_le`,
   `TauCeti.Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le`).

## Main declarations

* `TauCeti.contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul` and
  `TauCeti.contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul`: `C^m` smoothness of
  Taylor-monomial pairings against locally integrable functions.
* `TauCeti.HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul`:
  single-step spatial derivative commutation against a weak directional derivative.
* `TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`:
  Brenner–Scott Prop. 4.1.17 commutation for all `j, m : ℕ` on `W^{j+1,p}(Ω)`.
* `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq` and
  `TauCeti.Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq`: coordinate-free spatial derivative
  commutation for continuous compactly supported weights.
* `TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE`,
  `TauCeti.setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE`,
  `TauCeti.sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE`,
  `TauCeti.setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE`, and
  `TauCeti.Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE`:
  membership in `TauCeti.polynomialsDegLE ι m`.
* `TauCeti.norm_setIntegral_fullContractL_sub_mul_le`,
  `TauCeti.Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall`, and
  `TauCeti.Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le`: explicit diameter and
  chunkiness bounds for `1 ≤ p ≤ ∞`.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Proposition 4.1.17 and Lemma 4.3.1.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

private theorem iteratedFDerivAlong_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f : E → ℝ} (hf : ContDiff ℝ n f) (c : ℝ) (vs : List E) (hvs : vs.length ≤ n)
    (y : E) :
    iteratedFDerivAlong ℝ vs (fun z => c * f z) y = c * iteratedFDerivAlong ℝ vs f y := by
  simpa only [Pi.smul_def, smul_eq_mul] using
    congrFun (iteratedFDerivAlong_const_smul hf c vs hvs) y

/-! ### Smoothness and single-step commutation of Taylor-monomial pairings -/

section TaylorExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem prod_inner_sub_eq_sum_powerset {j : ℕ} (a : Fin j → E) (x z : E) :
    (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
        (∏ l ∈ s, ⟪a l, x⟫_ℝ) * ∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ := by
  simp_rw [inner_sub_right, sub_eq_add_neg]
  exact Finset.prod_add _ _ _

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong {j : ℕ} (a : Fin j → E)
    {φ : E → ℝ} (hφ : ContDiff ℝ j φ) (x y : E) :
    iteratedFDeriv ℝ j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a =
      iteratedFDerivAlong ℝ (List.ofFn a) (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y := by
  have hc : ContDiff ℝ j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) :=
    ((contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ
  rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hc]

private theorem setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_along
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {φ : E → ℝ}
    (hφ : ContDiff ℝ j φ) (v : E → ℝ) (x : E) :
    ∫ y in Ω, iteratedFDeriv ℝ j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a * v y ∂μ =
      ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn a)
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ :=
  setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => by
    rw [iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong a hφ x y]

/-- Iterated directional derivatives of `z ↦ g z * φ z` remain supported in `tsupport φ` and
define an integrable pairing against any `v` locally integrable on `Ω`. -/
private theorem hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul
    {μ : Measure E} {Ω : Opens E} {n : ℕ∞ω} {g φ : E → ℝ}
    (hg : ContDiff ℝ n g) (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    tsupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) ⊆ tsupport φ ∧
      HasCompactSupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) ∧
      IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (fun z => g z * φ z) y * v y) Ω μ := by
  have hsub : tsupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) ⊆ tsupport φ :=
    closure_minimal (Function.support_subset_iff'.2 fun y hy =>
      iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero
        (Filter.eventually_of_mem ((isClosed_tsupport φ).isOpen_compl.mem_nhds (Set.mem_compl hy))
          fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]) vs)
      (isClosed_tsupport φ)
  have hcs : HasCompactSupport (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) :=
    hφc.isCompact.of_isClosed_subset (isClosed_tsupport _) hsub
  have hcont : Continuous (iteratedFDerivAlong ℝ vs (fun z => g z * φ z)) :=
    ((hg.mul hφ).iteratedFDerivAlong (m := 0) vs (by simpa using hvs)).continuous
  exact ⟨hsub, hcs,
    (hv.integrable_smul_left_of_hasCompactSupport hcont hcs (hsub.trans hφs)).integrableOn⟩

/-- Powerset expansion of a Taylor-monomial pairing in `x`: all `x`-dependence factors out of both
`iteratedFDerivAlong` and the integral over `Ω`. -/
private theorem setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {n : ℕ∞ω} {φ : E → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) (x : E) :
    ∫ y in Ω, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, (∏ l ∈ s, ⟪a l, x⟫_ℝ) *
        ∫ y in Ω, iteratedFDerivAlong ℝ vs
          (fun z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z) y * v y ∂μ := by
  let ψ : Finset (Fin j) → E → ℝ := fun s z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z
  have hg : ∀ s : Finset (Fin j), ContDiff ℝ n (fun z => ∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) :=
    fun s => (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.neg).of_le le_top
  have hψ : ∀ s, ContDiff ℝ n (ψ s) := fun s => (hg s).mul hφ
  have hint : ∀ s, IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (ψ s) y * v y) Ω μ := fun s =>
    (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul (hg s) hφ hφc hφs vs hvs hv).2.2
  have hexp : (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) =
      fun z => ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, (∏ l ∈ s, ⟪a l, x⟫_ℝ) * ψ s z := by
    funext z
    simp_rw [ψ, prod_inner_sub_eq_sum_powerset a x z, Finset.sum_mul, mul_assoc]
  have hstep : ∀ y, iteratedFDerivAlong ℝ vs (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y *
        v y = ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∏ l ∈ s, ⟪a l, x⟫_ℝ) * (iteratedFDerivAlong ℝ vs (ψ s) y * v y) := fun y => by
    rw [hexp, iteratedFDerivAlong_fun_sum _ (fun s _ => contDiff_const.mul (hψ s)) vs hvs,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by
      rw [iteratedFDerivAlong_const_mul (hψ s) _ vs hvs, mul_assoc]
  simp_rw [hstep]
  rw [integral_finsetSum _ fun s _ => (hint s).const_mul _]
  exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _

private theorem setIntegral_iteratedFDeriv_prod_inner_sub_eq_sum
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {φ : E → ℝ}
    (hφ : ContDiff ℝ j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) (x : E) :
    ∫ y in Ω, iteratedFDeriv ℝ j (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a * v y ∂μ =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, (∏ l ∈ s, ⟪a l, x⟫_ℝ) *
        ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn a)
          (fun z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z) y * v y ∂μ := by
  rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_along a hφ v x,
    setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum a hφ hφc hφs (List.ofFn a) (by simp) hv x]

/-- Every Taylor-monomial pairing (`iteratedFDerivAlong` form) against a locally integrable
function is `C^m` for every `m : ℕ∞ω`. -/
theorem contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul
    {μ : Measure E} {Ω : Opens E} {m : ℕ∞ω} {j : ℕ} (a : Fin j → E) {n : ℕ∞ω} {φ : E → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    ContDiff ℝ m (fun x => ∫ y in Ω, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ) := by
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum a hφ hφc hφs vs hvs hv)]
  exact ContDiff.sum fun s _ =>
    (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff).mul contDiff_const

/-- Every Taylor-monomial pairing (`iteratedFDeriv` form) against a locally integrable function is
`C^m` for every `m : ℕ∞ω`. -/
theorem contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {μ : Measure E} {Ω : Opens E} {m : ℕ∞ω} {j : ℕ} (a : Fin j → E) {φ : E → ℝ}
    (hφ : ContDiff ℝ j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    ContDiff ℝ m (fun x => ∫ y in Ω, iteratedFDeriv ℝ j
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a * v y ∂μ) := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_along a hφ v]
  exact contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul a hφ hφc hφs
    (List.ofFn a) (by simp) hv

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Comparing the product-rule and powerset derivatives of `x' ↦ (∏ l, ⟪a l, x' - z⟫_ℝ) * φ z`
with respect to `x'` gives a pointwise identity in `z`. -/
private theorem sum_erase_prod_inner_sub_eq_sum_powerset_fderiv {j : ℕ} (a : Fin j → E)
    (φ : E → ℝ) (x h z : E) :
    (∑ p : Fin j, ⟪a p, h⟫_ℝ * ((∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) * φ z)) =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
        fderiv ℝ (fun x' => ∏ l ∈ s, ⟪a l, x'⟫_ℝ) x h *
          ((∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z) := by
  let c : Finset (Fin j) → E → ℝ := fun s x' => ∏ l ∈ s, ⟪a l, x'⟫_ℝ
  let ψ : Finset (Fin j) → ℝ := fun s => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z
  have hc : ∀ s, Differentiable ℝ (c s) := fun s =>
    (contDiff_prod (n := 1) fun l _ => (innerSL ℝ (a l)).contDiff).differentiable one_ne_zero
  have hfun : (fun x' => (∏ l : Fin j, ⟪a l, x' - z⟫_ℝ) * φ z) =
      fun x' => ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, c s x' * ψ s := by
    funext x'
    simp_rw [c, ψ, prod_inner_sub_eq_sum_powerset a x' z, Finset.sum_mul, mul_assoc]
  have hp : HasFDerivAt (fun x' => ∏ l : Fin j, ⟪a l, x' - z⟫_ℝ)
      (∑ p ∈ (Finset.univ : Finset (Fin j)),
        (∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) • innerSL ℝ (a p)) x :=
    HasFDerivAt.finsetProd fun l _ => by
      have h1 : HasFDerivAt (fun x' => ⟪a l, x'⟫_ℝ - ⟪a l, z⟫_ℝ) (innerSL ℝ (a l)) x :=
        (innerSL ℝ (a l)).hasFDerivAt.sub_const _
      simpa [inner_sub_right] using h1
  have hd1 := hp.mul_const (φ z)
  have hd2 : HasFDerivAt (fun x' => ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, c s x' * ψ s)
      (∑ s ∈ (Finset.univ : Finset (Fin j)).powerset, ψ s • fderiv ℝ (c s) x) x :=
    HasFDerivAt.fun_sum fun s _ => ((hc s x).hasFDerivAt).mul_const (ψ s)
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L h) (hd1.unique (hfun ▸ hd2))
  simp only [c, ψ, smul_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply,
    smul_eq_mul] at heq ⊢
  rw [Finset.mul_sum] at heq
  exact (Finset.sum_congr rfl fun p _ => by ring).trans
    (heq.trans (Finset.sum_congr rfl fun s _ => by ring))

/-- Spatial Fréchet derivative of a single Taylor-monomial pairing: differentiating in `x` along
`h` differentiates the polynomial factor `∏ l, ⟪a l, x - z⟫_ℝ` factor by factor under the integral
and `iteratedFDerivAlong`. -/
private theorem fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul
    {μ : Measure E} {Ω : Opens E} {j : ℕ} (a : Fin j → E) {n : ℕ∞ω} {φ : E → ℝ}
    (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (vs : List E) (hvs : vs.length ≤ n) {v : E → ℝ} (hv : LocallyIntegrableOn v Ω μ) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Ω, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l : Fin j, ⟪a l, x' - z⟫_ℝ) * φ z) y * v y ∂μ) x h =
      ∑ p : Fin j, ⟪a p, h⟫_ℝ * ∫ y in Ω, iteratedFDerivAlong ℝ vs
        (fun z => (∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ := by
  let ψ : Finset (Fin j) → E → ℝ := fun s z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z
  let gp : Fin j → E → ℝ := fun p z => (∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) * φ z
  let c : Finset (Fin j) → E → ℝ := fun s x' => ∏ l ∈ s, ⟪a l, x'⟫_ℝ
  have hc : ∀ s, Differentiable ℝ (c s) := fun s =>
    (contDiff_prod (n := 1) fun l _ => (innerSL ℝ (a l)).contDiff).differentiable one_ne_zero
  have hgψ : ∀ s : Finset (Fin j), ContDiff ℝ n (fun z => ∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) :=
    fun s => (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.neg).of_le le_top
  have hggp : ∀ p : Fin j, ContDiff ℝ n (fun z => ∏ l ∈ Finset.univ.erase p, ⟪a l, x - z⟫_ℝ) :=
    fun p => (contDiff_prod fun l _ => (innerSL ℝ (a l)).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top
  have hψ : ∀ s, ContDiff ℝ n (ψ s) := fun s => (hgψ s).mul hφ
  have hgp : ∀ p, ContDiff ℝ n (gp p) := fun p => (hggp p).mul hφ
  have hint : ∀ s, IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (ψ s) y * v y) Ω μ := fun s =>
    (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul (hgψ s) hφ hφc hφs vs hvs hv).2.2
  have hint_p : ∀ p, IntegrableOn (fun y => iteratedFDerivAlong ℝ vs (gp p) y * v y) Ω μ :=
    fun p => (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul (hggp p) hφ hφc hφs vs
      hvs hv).2.2
  rw [funext (setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum a hφ hφc hφs vs hvs hv),
    (HasFDerivAt.fun_sum fun s _ => ((hc s x).hasFDerivAt).mul_const _).fderiv,
    FunLike.coe_sum, Finset.sum_apply]
  simp only [smul_apply, smul_eq_mul]
  calc ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
        (∫ y in Ω, iteratedFDerivAlong ℝ vs (ψ s) y * v y ∂μ) * fderiv ℝ (c s) x h
      = ∫ y in Ω, (∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
          iteratedFDerivAlong ℝ vs (fun z => fderiv ℝ (c s) x h * ψ s z) y) * v y ∂μ := by
        rw [Finset.sum_congr rfl fun s _ => (mul_comm _ _).trans (integral_const_mul _ _).symm,
          ← integral_finsetSum _ fun s _ => (hint s).const_mul _]
        refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by
          rw [iteratedFDerivAlong_const_mul (hψ s) _ vs hvs, mul_assoc]
    _ = ∫ y in Ω, (∑ p : Fin j,
          iteratedFDerivAlong ℝ vs (fun z => ⟪a p, h⟫_ℝ * gp p z) y) * v y ∂μ :=
        setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => by
          rw [← iteratedFDerivAlong_fun_sum _ (fun s _ => contDiff_const.mul (hψ s)) vs hvs,
            ← funext (sum_erase_prod_inner_sub_eq_sum_powerset_fderiv a φ x h),
            iteratedFDerivAlong_fun_sum _ (fun p _ => contDiff_const.mul (hgp p)) vs hvs]
    _ = ∑ p : Fin j, ⟪a p, h⟫_ℝ * ∫ y in Ω, iteratedFDerivAlong ℝ vs (gp p) y * v y ∂μ := by
        simp_rw [iteratedFDerivAlong_const_mul (hgp _) _ vs hvs, Finset.sum_mul, mul_assoc]
        rw [integral_finsetSum _ fun p _ => (hint_p p).const_mul _]
        exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem iteratedFDerivAlong_insertNth_erase_eq {ι : Type*} (b : ι → E) {j : ℕ}
    {φ : E → ℝ} (hφ : ContDiff ℝ (j + 1) φ) (x : E) (p : Fin (j + 1)) (J : Fin j → ι)
    (i : ι) (y : E) :
    iteratedFDerivAlong ℝ (List.ofFn (b ∘ p.insertNth (α := fun _ => ι) i J))
      (fun z => (∏ l ∈ Finset.univ.erase p,
        ⟪b (p.insertNth (α := fun _ => ι) i J l), x - z⟫_ℝ) * φ z) y =
      fderiv ℝ (iteratedFDerivAlong ℝ (List.ofFn (b ∘ J))
        (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z)) y (b i) := by
  have hqg : ContDiff ℝ (j + 1) (fun z => ∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) :=
    (contDiff_prod fun l _ => (innerSL ℝ (b (J l))).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top
  have herase : (fun z => (∏ l ∈ Finset.univ.erase p,
        ⟪b (p.insertNth (α := fun _ => ι) i J l), x - z⟫_ℝ) * φ z) =
      fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z := by
    funext z
    have he : (Finset.univ : Finset (Fin (j + 1))).erase p = Finset.univ.map p.succAboveEmb := by
      rw [Fin.univ_succAbove j p, Finset.erase_cons]
    simp [he, Fin.insertNth_apply_succAbove]
  have hcomp : b ∘ p.insertNth (α := fun _ => ι) i J = p.insertNth (b i) (b ∘ J) :=
    funext (p.succAboveCases (by simp) fun l => by simp)
  rw [herase, hcomp,
    congrFun ((List.ofFn_insertNth_perm p (b i) (b ∘ J)).iteratedFDerivAlong_eq (hqg.mul hφ)
      (by simp)) y, iteratedFDerivAlong_cons_apply]

/-- Evaluating the `p`-th slot sum in the derivative of a Taylor-monomial pairing via
`Fin.insertNthEquiv`, permutation invariance of `iteratedFDerivAlong`, and weak integration by
parts against `hu : HasWeakLineDerivOn μ Ω u u' h`. -/
private theorem sum_slot_setIntegral_iteratedFDerivAlong_eq_neg
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) {j : ℕ} {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (x : E) (p : Fin (j + 1)) :
    (∑ I : Fin (j + 1) → ι, ⟪b (I p), h⟫_ℝ * ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
      (fun z => (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - z⟫_ℝ) * φ z) y * u y ∂μ) =
      -∑ J : Fin j → ι, ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ J))
        (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y * u' y ∂μ := by
  rw [← (p.insertNthEquiv fun _ : Fin (j + 1) => ι).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.insertNthEquiv_apply]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  let qg : E → ℝ := fun z => ∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ
  let g : E → ℝ := iteratedFDerivAlong ℝ (List.ofFn (b ∘ J)) (fun z => qg z * φ z)
  have hqg : ContDiff ℝ (j + 1) qg := (contDiff_prod fun l _ =>
    (innerSL ℝ (b (J l))).contDiff.comp (contDiff_const.sub contDiff_id)).of_le le_top
  have hg : ContDiff ℝ 1 g := (hqg.mul hφ).iteratedFDerivAlong (List.ofFn (b ∘ J))
    (by simp [add_comm])
  obtain ⟨hgs_sub, hgc, -⟩ := hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul
    hqg hφ hφc hφs (List.ofFn (b ∘ J)) (by simp) hu.locallyIntegrableOn
  have hgs : tsupport g ⊆ Ω := hgs_sub.trans hφs
  have hint_i : ∀ i : ι, IntegrableOn (fun y => ⟪b i, h⟫_ℝ * fderiv ℝ g y (b i) * u y) Ω μ :=
    fun i => by
      simpa only [smul_eq_mul, mul_assoc] using
        ((hu.locallyIntegrableOn.integrable_smul_left_of_hasCompactSupport
          ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
          (hgc.fderiv_apply ℝ (b i))
          ((tsupport_fderiv_apply_subset ℝ (b i)).trans hgs)).const_mul ⟪b i, h⟫_ℝ).integrableOn
  simp_rw [Fin.insertNth_apply_same, iteratedFDerivAlong_insertNth_erase_eq b hφ x p J,
    ← integral_const_mul, ← mul_assoc]
  rw [← integral_finsetSum _ fun i _ => hint_i i,
    ← hu.setIntegral_fderiv_mul_eq_neg hg hgc hgs]
  refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  conv_rhs => rw [← b.sum_repr' h, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- **Single-step weak derivative commutation for Taylor-monomial pairings.** If `u` has weak
directional derivative `u'` in the direction `h` on `Ω` and `φ : E → ℝ` is `C^{j+1}` with compact
support in `Ω`, differentiating the degree-`(j + 1)` orthonormal-basis Taylor-monomial pairing of
`u` at `x` along `h` yields `-(j + 1)` times the degree-`j` Taylor-monomial pairing of `u'`. No
translation invariance of `μ` is needed. -/
theorem HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) (j : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (x : E) :
    fderiv ℝ (fun x' => ∑ I : Fin (j + 1) → ι,
      ∫ y in Ω, iteratedFDeriv ℝ (j + 1)
        (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * u y ∂μ) x h =
      -(j + 1 : ℝ) * ∑ J : Fin j → ι,
        ∫ y in Ω, iteratedFDeriv ℝ j
          (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) * u' y ∂μ := by
  have hφ_j : ContDiff ℝ j φ := hφ.of_le (by norm_cast; omega)
  have hconv : ∀ {k : ℕ} {ψ : E → ℝ}, ContDiff ℝ k ψ → ∀ (w : E → ℝ) (I : Fin k → ι) (x' : E),
      ∫ y in Ω, iteratedFDeriv ℝ k
        (fun z => (∏ l : Fin k, ⟪b (I l), x' - z⟫_ℝ) * ψ z) y (b ∘ I) * w y ∂μ =
      ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
        (fun z => (∏ l : Fin k, ⟪b (I l), x' - z⟫_ℝ) * ψ z) y * w y ∂μ :=
    fun hψ w I x' => by
      simpa only [Function.comp_def] using
        setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_along (fun l => b (I l)) hψ w x'
  simp_rw [hconv hφ u, hconv hφ_j u']
  have hsum_d : HasFDerivAt
      (fun x' => ∑ I : Fin (j + 1) → ι, ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
        (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y * u y ∂μ)
      (∑ I ∈ (Finset.univ : Finset (Fin (j + 1) → ι)), fderiv ℝ
        (fun x' => ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y * u y ∂μ) x) x :=
    HasFDerivAt.fun_sum fun I _ =>
      (((contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul (m := 1) (fun l => b (I l))
        hφ hφc hφs _ (by simp) hu.locallyIntegrableOn).differentiable one_ne_zero) x).hasFDerivAt
  rw [hsum_d.fderiv, FunLike.coe_sum, Finset.sum_apply,
    Finset.sum_congr rfl fun I _ => fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul
      (fun l => b (I l)) hφ hφc hφs (List.ofFn (b ∘ I)) (by simp) hu.locallyIntegrableOn x h,
    Finset.sum_comm]
  simp_rw [sum_slot_setIntegral_iteratedFDerivAlong_eq_neg b hu hφ hφc hφs x]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem fderiv_const_mul_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) (c : ℝ) (j : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (x : E) :
    fderiv ℝ (fun x' => c * ∑ I : Fin (j + 1) → ι,
      ∫ y in Ω, iteratedFDeriv ℝ (j + 1)
        (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * u y ∂μ) x h =
      c * -(j + 1 : ℝ) * ∑ J : Fin j → ι,
        ∫ y in Ω, iteratedFDeriv ℝ j
          (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) * u' y ∂μ := by
  have hdiff : DifferentiableAt ℝ (fun x' => ∑ I : Fin (j + 1) → ι,
      ∫ y in Ω, iteratedFDeriv ℝ (j + 1)
        (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * u y ∂μ) x :=
    DifferentiableAt.fun_sum fun I _ =>
      ((contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (m := 1) (b ∘ I) hφ hφc hφs
        hu.locallyIntegrableOn).differentiable one_ne_zero) x
  rw [(hdiff.hasFDerivAt.const_mul c).fderiv, smul_apply, smul_eq_mul,
    hu.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b j hφ hφc hφs x, mul_assoc]

end TaylorExpansion

/-! ### Higher-order weak derivative commutation on `W^{k,p}` -/

section WkpCommutation

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem iteratedFDerivAlong_replicate_taylorMonomial_eq_zero_of_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {j r : ℕ} (hrj : r ≤ j)
    {φ : E → ℝ} (hφ : ContDiff ℝ r φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega)
    {w : E → ℝ} (hw : LocallyIntegrableOn w Omega mu) (x h : E) :
    iteratedFDerivAlong ℝ (List.replicate (j + 1) h)
      (fun x' => ∑ I : Fin r → ι,
        ∫ y in Omega, iteratedFDeriv ℝ r
          (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu) x = 0 := by
  rw [iteratedFDerivAlong_fun_sum (n := ∞) Finset.univ
    (f := fun (I : Fin r → ι) x' => ∫ y in Omega, iteratedFDeriv ℝ r
      (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu)
    (fun I _ => contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I) hφ hφc hφs hw)
    _ (by simp)]
  refine Finset.sum_eq_zero fun I _ => ?_
  have hexp : (fun x' => ∫ y in Omega, iteratedFDeriv ℝ r
        (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu) =
      fun x' => ∑ s ∈ (Finset.univ : Finset (Fin r)).powerset,
        (∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
          (fun z => (∏ l ∈ Finset.univ \ s, -⟪b (I l), z⟫_ℝ) * φ z) y * w y ∂mu) *
          ∏ l ∈ s, ⟪b (I l), x'⟫_ℝ := by
    funext x'
    simp_rw [Function.comp_def]
    rw [setIntegral_iteratedFDeriv_prod_inner_sub_eq_sum (fun l => b (I l)) hφ hφc hφs hw x']
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hexp, iteratedFDerivAlong_fun_sum (n := ∞) (Finset.univ : Finset (Fin r)).powerset
    (f := fun s x' => (∫ y in Omega, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
      (fun z => (∏ l ∈ Finset.univ \ s, -⟪b (I l), z⟫_ℝ) * φ z) y * w y ∂mu) *
      ∏ l ∈ s, ⟪b (I l), x'⟫_ℝ)
    (fun _ _ => contDiff_const.mul (contDiff_prod fun _ _ => (innerSL ℝ _).contDiff)) _ (by simp)]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hprod : ContDiff ℝ ∞ (fun x' => ∏ l ∈ s, ⟪b (I l), x'⟫_ℝ) :=
    contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff
  rw [iteratedFDerivAlong_const_mul hprod _ _ (by simp)]
  simp_rw [← innerSL_apply_apply ℝ]
  rw [congrFun (iteratedFDerivAlong_prod_clm_eq_zero (𝕜 := ℝ)
      (fun l : Fin r => innerSL ℝ (b (I l))) s (List.replicate (j + 1) h)
      (by have := s.card_le_univ; simp at this ⊢; omega)) x,
    Pi.zero_apply, mul_zero]

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem fderiv_normalized_taylorMonomial_eq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {w w' : E → ℝ} {h : E}
    (hw : HasWeakLineDerivOn mu Omega w w' h) (d : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (d + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x : E) :
    fderiv ℝ (fun x' => ((-1 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) *
      ∑ I : Fin (d + 1) → ι,
        ∫ y in Omega, iteratedFDeriv ℝ (d + 1)
          (fun z => (∏ l : Fin (d + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu) x h =
      ((-1 : ℝ) ^ d / (d.factorial : ℝ)) * ∑ J : Fin d → ι,
        ∫ y in Omega, iteratedFDeriv ℝ d
          (fun z => (∏ l : Fin d, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) * w' y ∂mu := by
  rw [fderiv_const_mul_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b hw _ d hφ hφc hφs x,
    Nat.factorial_succ]
  have hd1 : (d + 1 : ℝ) ≠ 0 := by positivity
  push_cast; field_simp [hd1]; ring

private theorem iteratedFDerivAlong_replicate_taylorMonomial_eq_of_ge
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Omega) (h : E) :
    ∀ (j d : ℕ) (u : Wkp mu Omega p (j + 1)), ContDiff ℝ (d + j + 1) φ → ∀ x : E,
      iteratedFDerivAlong ℝ (List.replicate (j + 1) h)
        (fun x' => ((-1 : ℝ) ^ (d + j + 1) / ((d + j + 1).factorial : ℝ)) *
          ∑ I : Fin (d + j + 1) → ι,
            ∫ y in Omega, iteratedFDeriv ℝ (d + j + 1)
              (fun z => (∏ l : Fin (d + j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
              Wkp.value (j + 1) u y ∂mu) x =
        ((-1 : ℝ) ^ d / (d.factorial : ℝ)) * ∑ J : Fin d → ι,
          ∫ y in Omega, iteratedFDeriv ℝ d
            (fun z => (∏ l : Fin d, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) *
            IteratedGradient.fullContractL j h (Wkp.iteratedGradient j u y) ∂mu
  | 0, d, u, hφ, x => by
      have hw : HasWeakLineDerivOn mu Omega (Wkp.value 1 u)
          (fun y => IteratedGradient.fullContractL 0 h (Wkp.iteratedGradient 0 u y)) h :=
        ((Wkp.hasWeakFDerivOn_value u).hasWeakLineDerivOn h).congr_ae_deriv
          (.of_forall fun y => by simp [real_inner_comm])
      simp only [Nat.zero_add, List.replicate_one, iteratedFDerivAlong_cons_apply,
        iteratedFDerivAlong_nil]
      simp only [Nat.add_zero] at hφ ⊢
      exact fderiv_normalized_taylorMonomial_eq b hw d hφ hφc hφs x
  | j + 1, d, u, hφ, x => by
      have hidx : d + (j + 1) + 1 = (d + 1) + j + 1 := by omega
      have hih : iteratedFDerivAlong ℝ (List.replicate (j + 1) h)
            (fun x'' => ((-1 : ℝ) ^ (d + (j + 1) + 1) / ((d + (j + 1) + 1).factorial : ℝ)) *
              ∑ I : Fin (d + (j + 1) + 1) → ι,
                ∫ y in Omega, iteratedFDeriv ℝ (d + (j + 1) + 1)
                  (fun z => (∏ l : Fin (d + (j + 1) + 1), ⟪b (I l), x'' - z⟫_ℝ) * φ z) y
                  (b ∘ I) * Wkp.value (j + 1 + 1) u y ∂mu) =
          fun x' => ((-1 : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * ∑ J : Fin (d + 1) → ι,
            ∫ y in Omega, iteratedFDeriv ℝ (d + 1)
              (fun z => (∏ l : Fin (d + 1), ⟪b (J l), x' - z⟫_ℝ) * φ z) y (b ∘ J) *
              IteratedGradient.fullContractL j h
                (Wkp.iteratedGradient j (Wkp.lowerOrder (j + 1) u) y) ∂mu := by
        ext x'
        have hstep := iteratedFDerivAlong_replicate_taylorMonomial_eq_of_ge b hφc hφs h j (d + 1)
          (Wkp.lowerOrder (j + 1) u) (hφ.of_le (by norm_cast; omega)) x'
        rw [← Wkp.value_succ] at hstep
        exact hidx.symm ▸ hstep
      have hw : HasWeakLineDerivOn mu Omega
          (fun y => IteratedGradient.fullContractL j h
            (Wkp.iteratedGradient j (Wkp.lowerOrder (j + 1) u) y))
          (fun y => IteratedGradient.fullContractL (j + 1) h
            (Wkp.iteratedGradient (j + 1) u y)) h :=
        (((Wkp.hasWeakFDerivOn_iteratedGradient j u).clm_comp
          (IteratedGradient.fullContractL j h)).hasWeakLineDerivOn h).congr_ae_deriv
          (.of_forall fun y => by
            simp only [IteratedGradient.fullContractL_succ, ContinuousLinearMap.comp_apply]
            rw [ContinuousLinearMap.apply_apply])
      rw [List.replicate_succ, iteratedFDerivAlong_cons_apply, hih]
      exact fderiv_normalized_taylorMonomial_eq b hw d (hφ.of_le (by norm_cast; omega)) hφc hφs x

private def averagedTaylorTerm {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (mu : Measure E) (Omega : Opens E) (φ w : E → ℝ) (r : ℕ) : E → ℝ := fun x =>
  ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
    ∫ y in Omega, iteratedFDeriv ℝ r
      (fun z => (∏ l : Fin r, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * w y ∂mu

/-- **Brenner–Scott weak derivative commutation identity.** For any `j, m : ℕ`, `u ∈ W^{j+1,p}(Ω)`
(`1 ≤ p ≤ ∞`), `h : E`, and `φ : E → ℝ` of class `C^m` compactly supported in `Ω`, contracting
`iteratedGradientChain · j x` of the degree-`m` averaged Taylor pairing of `u` along `h` yields
the degree-`(m - j - 1)` averaged Taylor pairing of
`y ↦ fullContractL j h (Wkp.iteratedGradient j u y)` (vanishing when `m ≤ j`). Only Sobolev order
`j + 1` is required. -/
theorem Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (j m : ℕ)
    (u : Wkp mu Omega p (j + 1)) {φ : E → ℝ} (hφ : ContDiff ℝ m φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    IteratedGradient.fullContractL j h
      (iteratedGradientChain
        (fun x' => ∑ r ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
            ∫ y in Omega, iteratedFDeriv ℝ r
              (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
              Wkp.value (j + 1) u y ∂mu)
        j x) =
      ∑ d ∈ Finset.range (m - j),
        ((-1 : ℝ) ^ d / (d.factorial : ℝ)) * ∑ J : Fin d → ι,
          ∫ y in Omega, iteratedFDeriv ℝ d
            (fun z => (∏ l : Fin d, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) *
            IteratedGradient.fullContractL j h (Wkp.iteratedGradient j u y) ∂mu := by
  let term := averagedTaylorTerm b mu Omega φ (Wkp.value (j + 1) u)
  have hloc : LocallyIntegrableOn (Wkp.value (j + 1) u) Omega mu :=
    Lp.locallyIntegrableOn _ Fact.out
  have hS_smooth : ∀ {k : ℕ∞ω} {r : ℕ}, r ≤ m → ContDiff ℝ k (fun x' => ∑ I : Fin r → ι,
      ∫ y in Omega, iteratedFDeriv ℝ r
        (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
        Wkp.value (j + 1) u y ∂mu) := fun hr =>
    ContDiff.sum fun I _ => contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (b ∘ I)
      (hφ.of_le (by norm_cast)) hφc hφs hloc
  have hterm_smooth : ∀ {k : ℕ∞ω}, ∀ r ∈ Finset.range (m + 1), ContDiff ℝ k (term r) :=
    fun r hr => contDiff_const.mul (hS_smooth (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)))
  have hsum_j : ContDiff ℝ (j + 1) (fun x' => ∑ r ∈ Finset.range (m + 1), term r x') :=
    ContDiff.sum hterm_smooth
  have hgoal : (fun x' => ∑ r ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ r / (r.factorial : ℝ)) * ∑ I : Fin r → ι,
          ∫ y in Omega, iteratedFDeriv ℝ r
            (fun z => (∏ l : Fin r, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) *
            Wkp.value (j + 1) u y ∂mu) =
      fun x' => ∑ r ∈ Finset.range (m + 1), term r x' := by
    ext x'; simp [term, averagedTaylorTerm]
  rw [hgoal,
    IteratedGradient.fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong j
      hsum_j.contDiffAt h,
    iteratedFDerivAlong_fun_sum (n := ∞) _ hterm_smooth _ (by simp)]
  rcases lt_or_ge j m with hjm | hmj
  · have hm_split : m + 1 = (j + 1) + (m - j) := by omega
    rw [hm_split, Finset.sum_range_add]
    have hlow : ∑ r ∈ Finset.range (j + 1),
        iteratedFDerivAlong ℝ (List.replicate (j + 1) h) (term r) x = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have hrj : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      dsimp only [term]
      unfold averagedTaylorTerm
      rw [iteratedFDerivAlong_const_mul (n := ∞) (hS_smooth (hrj.trans hjm.le)) _ _ (by simp),
        iteratedFDerivAlong_replicate_taylorMonomial_eq_zero_of_le b hrj
          (hφ.of_le (by norm_cast; omega)) hφc hφs hloc x h, mul_zero]
    rw [hlow, zero_add]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdm : d + j + 1 ≤ m := by have := Finset.mem_range.1 hd; omega
    have heq_idx : j + 1 + d = d + j + 1 := by omega
    dsimp only [term]
    unfold averagedTaylorTerm
    rw [heq_idx]
    exact iteratedFDerivAlong_replicate_taylorMonomial_eq_of_ge b hφc hφs h j d u
      (hφ.of_le (by norm_cast)) x
  · rw [Nat.sub_eq_zero_of_le hmj, Finset.range_zero, Finset.sum_empty]
    refine Finset.sum_eq_zero fun r hr => ?_
    have hrm : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    dsimp only [term]
    unfold averagedTaylorTerm
    rw [iteratedFDerivAlong_const_mul (n := ∞) (hS_smooth hrm) _ _ (by simp),
      iteratedFDerivAlong_replicate_taylorMonomial_eq_zero_of_le b (hrm.trans hmj)
        (hφ.of_le (by norm_cast)) hφc hφs hloc x h, mul_zero]

/-- **Coordinate-free spatial derivative of a first-order contracted weak-gradient integral.**
For `u ∈ W^{1,p}(Ω)` (`1 ≤ p ≤ ∞`) and any continuous `φ : E → ℝ` compactly supported in `Ω`,
differentiating `x ↦ ∫ fullContractL 0 (x - y) (iteratedGradient 0 u y) * φ y` along `h` yields
`∫ φ y * Wkp.value 0 (Wkp.lineDerivL h 0 u) y`. -/
theorem Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq
    (u : Wkp mu Omega p 1) {φ : E → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL 0 (x' - y) (Wkp.iteratedGradient 0 u y) * φ y ∂mu) x h =
      ∫ y in Omega, φ y * Wkp.value 0 (Wkp.lineDerivL h 0 u) y ∂mu := by
  let G := Wkp.iteratedGradient 0 u
  have hG : LocallyIntegrableOn G Omega mu := Lp.locallyIntegrableOn G Fact.out
  have hint₁ : IntegrableOn (fun y => φ y • G y) Omega mu :=
    (hG.integrable_smul_left_of_hasCompactSupport hφ hφc hφs).integrableOn
  have hloc₂ : LocallyIntegrableOn (fun y => ⟪y, G y⟫_ℝ) Omega mu := by
    simpa only [innerSL_apply_apply] using
      hG.continuousOn_clm_apply Omega.isOpen.isLocallyClosed
        (innerSL ℝ (E := E)).continuous.continuousOn
  have hint₂ : IntegrableOn (fun y => φ y * ⟪y, G y⟫_ℝ) Omega mu :=
    (hloc₂.integrable_smul_left_of_hasCompactSupport hφ hφc hφs).integrableOn
  let V : E := ∫ y in Omega, φ y • G y ∂mu
  let C : ℝ := ∫ y in Omega, φ y * ⟪y, G y⟫_ℝ ∂mu
  have hfun : (fun x' => ∫ y in Omega, IteratedGradient.fullContractL 0 (x' - y) (G y) * φ y ∂mu) =
      fun x' => innerSL ℝ V x' - C := by
    funext x'
    have hpt : ∀ y, IteratedGradient.fullContractL 0 (x' - y) (G y) * φ y =
        innerSL ℝ x' (φ y • G y) - φ y * ⟪y, G y⟫_ℝ := fun y => by
      simp only [IteratedGradient.fullContractL_zero, innerSL_apply_apply, inner_sub_left,
        inner_smul_right]
      ring
    simp_rw [hpt]
    rw [integral_sub ((innerSL ℝ x').integrable_comp hint₁) hint₂,
      (innerSL ℝ x').integral_comp_comm hint₁]
    simp only [V, C, innerSL_apply_apply, real_inner_comm]
  have hw₁ : HasWeakLineDerivOn mu Omega (Wkp.value 1 u) (fun y => ⟪h, G y⟫_ℝ) h :=
    ((Wkp.hasWeakFDerivOn_value u).hasWeakLineDerivOn h).congr_ae_deriv
      (.of_forall fun y => by simp [G, real_inner_comm])
  have hae := hw₁.ae_eq (Wkp.hasWeakLineDerivOn_lineDerivL h 0 u)
  rw [hfun, ((innerSL ℝ V).hasFDerivAt.sub_const C).fderiv]
  have hVh : innerSL ℝ V h = ∫ y in Omega, φ y * ⟪h, G y⟫_ℝ ∂mu := by
    dsimp only [V]
    rw [innerSL_apply_apply, real_inner_comm, ← innerSL_apply_apply ℝ,
      ← (innerSL ℝ h).integral_comp_comm hint₁]
    exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by simp
  rw [hVh]
  exact integral_congr_ae (hae.mono fun y hy => by dsimp only at hy ⊢; rw [hy])

private theorem fderiv_setIntegral_fullContractL_sub_succ_eq_of_contDiff (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {ψ : E → ℝ} (hψ : ContDiff ℝ (k + 2) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL (k + 1) (x' - y)
        (Wkp.iteratedGradient (k + 1) u y) * ψ y ∂mu) x h =
      (k + 2 : ℝ) * ∫ y in Omega,
        IteratedGradient.fullContractL k (x - y)
          (Wkp.iteratedGradient k (Wkp.lineDerivL h (k + 1) u) y) * ψ y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  have hw := Wkp.hasWeakLineDerivOn_lineDerivL h (k + 1) u
  rw [funext (Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv
        b (k + 1) u hψ hψc hψs),
    fderiv_const_mul_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul
      b hw ((-1 : ℝ) ^ (k + 2)) (k + 1) hψ hψc hψs x,
    Wkp.setIntegral_fullContractL_sub_mul_eq_sum_iteratedFDeriv b k
      (Wkp.lineDerivL h (k + 1) u) (hψ.of_le (by norm_cast; omega)) hψc hψs x,
    pow_succ (-1 : ℝ) (k + 1)]
  push_cast
  ring

omit [mu.IsAddHaarMeasure] in
private theorem fderiv_setIntegral_fullContractL_sub_mul_eq (m : ℕ)
    {G : E → IteratedGradient E m} (hG : LocallyIntegrableOn G Omega mu)
    {ψ : E → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Omega)
    (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL m (x' - y) (G y) * ψ y ∂mu) x h =
      ∫ y in Omega, ψ y * (∑ I : Fin (m + 1) → Fin (Module.finrank ℝ E),
        ∑ p : Fin (m + 1), ⟪stdOrthonormalBasis ℝ E (I p), h⟫_ℝ *
          (∏ l ∈ Finset.univ.erase p, ⟪stdOrthonormalBasis ℝ E (I l), x - y⟫_ℝ) *
          IteratedGradient.evalTupleL m (stdOrthonormalBasis ℝ E ∘ I) (G y)) ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  have hv : ∀ I : Fin (m + 1) → Fin (Module.finrank ℝ E),
      LocallyIntegrableOn (fun y => IteratedGradient.evalTupleL m (b ∘ I) (G y)) Omega mu :=
    fun I => (IteratedGradient.evalTupleL m (b ∘ I)).locallyIntegrableOn_comp hG
  have hψ0 : ContDiff ℝ 0 ψ := contDiff_zero.2 hψ
  have hexp : (fun x' => ∫ y in Omega, IteratedGradient.fullContractL m (x' - y) (G y) * ψ y ∂mu) =
      fun x' => ∑ I : Fin (m + 1) → Fin (Module.finrank ℝ E),
        ∫ y in Omega, iteratedFDerivAlong ℝ []
          (fun z => (∏ l : Fin (m + 1), ⟪b (I l), x' - z⟫_ℝ) * ψ z) y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y) ∂mu := by
    funext x'
    have hg_I : ∀ I : Fin (m + 1) → Fin (Module.finrank ℝ E),
        ContDiff ℝ 0 (fun z => ∏ l : Fin (m + 1), ⟪b (I l), x' - z⟫_ℝ) := fun I =>
      (contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff.comp
        (contDiff_const.sub contDiff_id)).of_le le_top
    have hint_I : ∀ I : Fin (m + 1) → Fin (Module.finrank ℝ E), IntegrableOn
        (fun y => (∏ l : Fin (m + 1), ⟪b (I l), x' - y⟫_ℝ) * ψ y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y)) Omega mu := fun I => by
      simpa only [iteratedFDerivAlong_nil] using
        (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul
          (hg_I I) hψ0 hψc hψs [] (by simp) (hv I)).2.2
    have hpt : ∀ y, IteratedGradient.fullContractL m (x' - y) (G y) * ψ y =
        ∑ I : Fin (m + 1) → Fin (Module.finrank ℝ E),
          (∏ l : Fin (m + 1), ⟪b (I l), x' - y⟫_ℝ) * ψ y *
            IteratedGradient.evalTupleL m (b ∘ I) (G y) := fun y => by
      conv_lhs =>
        rw [IteratedGradient.eq_sum_evalTupleL_rankOne b m (G y), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_smul, smul_eq_mul, IteratedGradient.fullContractL_rankOne]
      simp only [Function.comp_apply]
      ring
    simp_rw [hpt, iteratedFDerivAlong_nil]
    exact integral_finsetSum _ fun I _ => hint_I I
  have hsum_d : HasFDerivAt
      (fun x' => ∑ I : Fin (m + 1) → Fin (Module.finrank ℝ E),
        ∫ y in Omega, iteratedFDerivAlong ℝ []
          (fun z => (∏ l : Fin (m + 1), ⟪b (I l), x' - z⟫_ℝ) * ψ z) y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y) ∂mu)
      (∑ I ∈ (Finset.univ : Finset (Fin (m + 1) → Fin (Module.finrank ℝ E))), fderiv ℝ
        (fun x' => ∫ y in Omega, iteratedFDerivAlong ℝ []
          (fun z => (∏ l : Fin (m + 1), ⟪b (I l), x' - z⟫_ℝ) * ψ z) y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y) ∂mu) x) x :=
    HasFDerivAt.fun_sum fun I _ =>
      (((contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul (m := 1)
        (fun l => b (I l)) hψ0 hψc hψs [] (by simp) (hv I)).differentiable
        one_ne_zero) x).hasFDerivAt
  rw [hexp, hsum_d.fderiv, FunLike.coe_sum, Finset.sum_apply,
    Finset.sum_congr rfl fun I _ => fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul
      (fun l => b (I l)) hψ0 hψc hψs [] (by simp) (hv I) x h]
  have hgp_I : ∀ (I : Fin (m + 1) → Fin (Module.finrank ℝ E)) (p : Fin (m + 1)),
      ContDiff ℝ 0 (fun z => ∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - z⟫_ℝ) := fun I _ =>
    (contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff.comp
      (contDiff_const.sub contDiff_id)).of_le le_top
  have hint_Ip : ∀ (I : Fin (m + 1) → Fin (Module.finrank ℝ E)) (p : Fin (m + 1)),
      IntegrableOn (fun y => ⟪b (I p), h⟫_ℝ *
        ((∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) * ψ y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y))) Omega mu := fun I p => by
    have hint_base : IntegrableOn (fun y =>
        (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) * ψ y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y)) Omega mu := by
      simpa only [iteratedFDerivAlong_nil] using
        (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul
          (hgp_I I p) hψ0 hψc hψs [] (by simp) (hv I)).2.2
    exact hint_base.const_mul ⟪b (I p), h⟫_ℝ
  simp_rw [iteratedFDerivAlong_nil, ← integral_const_mul]
  have hinner : ∀ I : Fin (m + 1) → Fin (Module.finrank ℝ E),
      (∑ p : Fin (m + 1), ∫ y in Omega, ⟪b (I p), h⟫_ℝ *
        ((∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) * ψ y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y)) ∂mu) =
      ∫ y in Omega, ∑ p : Fin (m + 1), ⟪b (I p), h⟫_ℝ *
        ((∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) * ψ y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y)) ∂mu := fun I =>
    (integral_finsetSum _ fun p _ => hint_Ip I p).symm
  simp_rw [hinner]
  rw [← integral_finsetSum _ fun I _ => integrable_finsetSum _ fun p _ => hint_Ip I p]
  refine setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun I _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring

/-- **Coordinate-free spatial derivative of a higher-order contracted weak-gradient integral.**
For `u ∈ W^{k+2,p}(Ω)` (`1 ≤ p ≤ ∞`) and any continuous `φ : E → ℝ` compactly supported in `Ω`,
differentiating `x ↦ ∫ fullContractL (k + 1) (x - y) (D^{k+2} u y) * φ y` along `h` produces
`(k + 2)` times the order-`(k + 1)` contracted integral of `Wkp.lineDerivL h (k + 1) u`. -/
theorem Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) {φ : E → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Omega) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in Omega,
      IteratedGradient.fullContractL (k + 1) (x' - y)
        (Wkp.iteratedGradient (k + 1) u y) * φ y ∂mu) x h =
      (k + 2 : ℝ) * ∫ y in Omega,
        IteratedGradient.fullContractL k (x - y)
          (Wkp.iteratedGradient k (Wkp.lineDerivL h (k + 1) u) y) * φ y ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  let G₁ := Wkp.iteratedGradient (k + 1) u
  let G₂ := Wkp.iteratedGradient k (Wkp.lineDerivL h (k + 1) u)
  have hG₁ : LocallyIntegrableOn G₁ Omega mu := Lp.locallyIntegrableOn G₁ Fact.out
  have hG₂ : LocallyIntegrableOn G₂ Omega mu := Lp.locallyIntegrableOn G₂ Fact.out
  let W₁ : E → ℝ := fun y => ∑ I : Fin (k + 2) → Fin (Module.finrank ℝ E),
    ∑ p : Fin (k + 2), ⟪b (I p), h⟫_ℝ *
      (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) *
      IteratedGradient.evalTupleL (k + 1) (b ∘ I) (G₁ y)
  let W₂ : E → ℝ := fun y => (k + 2 : ℝ) * IteratedGradient.fullContractL k (x - y) (G₂ y)
  have hW₁ : LocallyIntegrableOn W₁ Omega mu :=
    locallyIntegrableOn_finsetSum _ fun I _ =>
      locallyIntegrableOn_finsetSum _ fun p _ => by
        have hcont : Continuous fun y =>
            ⟪b (I p), h⟫_ℝ * ∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ :=
          continuous_const.mul ((contDiff_prod (n := 0) fun l _ =>
            (innerSL ℝ (b (I l))).contDiff.comp
              (contDiff_const.sub contDiff_id)).continuous)
        simpa only [Function.comp_apply, smul_eq_mul, mul_assoc] using
          ((IteratedGradient.evalTupleL (k + 1) (b ∘ I)).locallyIntegrableOn_comp hG₁
            ).continuousOn_smul_of_isOpen Omega.isOpen hcont.continuousOn
  have hW₂ : LocallyIntegrableOn W₂ Omega mu := by
    have hclm : Continuous fun y => IteratedGradient.fullContractL (E := E) k (x - y) :=
      (IteratedGradient.contDiff_fullContractL (n := 0) k).continuous.comp
        (continuous_const.sub continuous_id)
    simpa only [W₂, smul_eq_mul] using
      (hG₂.continuousOn_clm_apply Omega.isOpen.isLocallyClosed
        hclm.continuousOn).continuousOn_smul_of_isOpen Omega.isOpen
          (continuousOn_const (c := (k + 2 : ℝ)))
  have hrhs : ∀ g : E → ℝ, (k + 2 : ℝ) *
      (∫ y in Omega, IteratedGradient.fullContractL k (x - y) (G₂ y) * g y ∂mu) =
      ∫ y in Omega, g y * W₂ y ∂mu := fun g => by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun Omega.isOpen.measurableSet fun y _ => by dsimp only [W₂]; ring
  have hwhole : ∀ {g w : E → ℝ}, tsupport g ⊆ Omega →
      ∫ y in Omega, g y * w y ∂mu = ∫ y, g y • w y ∂mu := fun {g w} hg => by
    simp_rw [← smul_eq_mul]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport fun h' => hy (hg h'), zero_smul]
  rw [fderiv_setIntegral_fullContractL_sub_mul_eq (k + 1) hG₁ hφ hφc hφs x h, hrhs φ,
    hwhole hφs, hwhole hφs]
  obtain ⟨δ, hδ, hδΩ⟩ := hφc.isCompact.exists_cthickening_subset_open Omega.isOpen hφs
  set K' := cthickening δ (tsupport φ)
  have hK' : IsCompact K' := hφc.isCompact.cthickening
  have hW₁K : IntegrableOn W₁ K' mu := hW₁.integrableOn_compact_subset hδΩ hK'
  have hW₂K : IntegrableOn W₂ K' mu := hW₂.integrableOn_compact_subset hδΩ hK'
  set C := (∫ y in K', ‖W₁ y‖ ∂mu) + ∫ y in K', ‖W₂ y‖ ∂mu
  have hC : 0 ≤ C := add_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _)
  refine eq_of_forall_dist_le fun ε hε => ?_
  set η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨ψ, hψK', hψ⟩ :=
    hφ.exists_testFunction_dist_le hφc.isCompact subset_rfl hδ hδΩ hη
  have hφK' : tsupport φ ⊆ K' := self_subset_cthickening _
  have hb1 := MeasureTheory.norm_integral_smul_sub_le hK' hW₁K hφ ψ.contDiff.continuous
    hφK' hψK' fun y _ => by simpa [dist_comm] using hψ y
  have hb2 := MeasureTheory.norm_integral_smul_sub_le hK' hW₂K hφ ψ.contDiff.continuous
    hφK' hψK' fun y _ => by simpa [dist_comm] using hψ y
  have hψ_eq : ∫ y, (ψ : E → ℝ) y • W₁ y ∂mu = ∫ y, (ψ : E → ℝ) y • W₂ y ∂mu := by
    rw [← hwhole ψ.tsupport_subset, ← hwhole ψ.tsupport_subset, ← hrhs ψ,
      ← fderiv_setIntegral_fullContractL_sub_mul_eq (k + 1) hG₁ ψ.contDiff.continuous
        ψ.hasCompactSupport ψ.tsupport_subset x h]
    exact fderiv_setIntegral_fullContractL_sub_succ_eq_of_contDiff k u
      (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport ψ.tsupport_subset x h
  rw [dist_eq_norm]
  calc ‖(∫ y, φ y • W₁ y ∂mu) - ∫ y, φ y • W₂ y ∂mu‖
      = ‖((∫ y, φ y • W₁ y ∂mu) - ∫ y, (ψ : E → ℝ) y • W₁ y ∂mu) -
          ((∫ y, φ y • W₂ y ∂mu) - ∫ y, (ψ : E → ℝ) y • W₂ y ∂mu)‖ := by
        rw [hψ_eq]; congr 1; abel
    _ ≤ ‖(∫ y, φ y • W₁ y ∂mu) - ∫ y, (ψ : E → ℝ) y • W₁ y ∂mu‖ +
          ‖(∫ y, φ y • W₂ y ∂mu) - ∫ y, (ψ : E → ℝ) y • W₂ y ∂mu‖ := norm_sub_le _ _
    _ ≤ η * (∫ y in K', ‖W₁ y‖ ∂mu) + η * ∫ y in K', ‖W₂ y‖ ∂mu := add_le_add hb1 hb2
    _ = η * C := by ring
    _ ≤ η * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
    _ = ε := div_mul_cancel₀ ε (by linarith)

end WkpCommutation

/-! ### Polynomiality in `TauCeti.polynomialsDegLE` -/

section Polynomiality

variable {ι : Type*} [Fintype ι]

/-- Every single Taylor-monomial pairing (`iteratedFDerivAlong` form) of degree `j ≤ m` against a
locally integrable function on an open subset of `EuclideanSpace ℝ ι` defines a polynomial function
in `TauCeti.polynomialsDegLE ι m`. -/
theorem setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {Ω : Opens (EuclideanSpace ℝ ι)} {j m : ℕ}
    (hjm : j ≤ m) (a : Fin j → EuclideanSpace ℝ ι) {n : ℕ∞ω}
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (vs : List (EuclideanSpace ℝ ι)) (hvs : vs.length ≤ n)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    (fun x => ∫ y in Ω, iteratedFDerivAlong ℝ vs
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ) ∈
      polynomialsDegLE ι m := by
  have hconv : (fun x => ∫ y in Ω, iteratedFDerivAlong ℝ vs
        (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y * v y ∂μ) =
      ∑ s ∈ (Finset.univ : Finset (Fin j)).powerset,
        (∫ y in Ω, iteratedFDerivAlong ℝ vs
          (fun z => (∏ l ∈ Finset.univ \ s, -⟪a l, z⟫_ℝ) * φ z) y * v y ∂μ) •
          fun x => ∏ l ∈ s, ⟪a l, x⟫_ℝ := by
    ext x
    rw [setIntegral_iteratedFDerivAlong_prod_inner_sub_eq_sum a hφ hφc hφs vs hvs hv x,
      Finset.sum_apply]
    exact Finset.sum_congr rfl fun s _ => by simp [smul_eq_mul, mul_comm]
  rw [hconv]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _
    (prod_inner_mem_polynomialsDegLE s a
      ((s.card_le_univ.trans_eq (Fintype.card_fin j)).trans hjm))

/-- `iteratedFDeriv` form of
`TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE`. -/
theorem setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {Ω : Opens (EuclideanSpace ℝ ι)} {j m : ℕ}
    (hjm : j ≤ m) (a : Fin j → EuclideanSpace ℝ ι) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ j φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    (fun x => ∫ y in Ω, iteratedFDeriv ℝ j
      (fun z => (∏ l : Fin j, ⟪a l, x - z⟫_ℝ) * φ z) y a * v y ∂μ) ∈
      polynomialsDegLE ι m := by
  simp_rw [setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_along a hφ v]
  exact setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE hjm a hφ
    hφc hφs (List.ofFn a) (by simp) hv

/-- Finite tuple-sum corollary of
`TauCeti.setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE`. -/
theorem sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE
    {κ : Type*} [Fintype κ] (b : κ → EuclideanSpace ℝ ι)
    {μ : Measure (EuclideanSpace ℝ ι)} {Ω : Opens (EuclideanSpace ℝ ι)} {j m : ℕ}
    (hjm : j ≤ m) {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ j φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    {v : EuclideanSpace ℝ ι → ℝ} (hv : LocallyIntegrableOn v Ω μ) :
    (fun x => ∑ I : Fin j → κ,
      ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ) ∈
      polynomialsDegLE ι m := by
  have hsum_fn : (fun x => ∑ I : Fin j → κ,
        ∫ y in Ω, iteratedFDeriv ℝ j
          (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ) =
      ∑ I : Fin j → κ, fun x => ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y (b ∘ I) * v y ∂μ := by
    ext x; simp
  rw [hsum_fn]
  exact Submodule.sum_mem (polynomialsDegLE ι m) fun I _ =>
    setIntegral_iteratedFDeriv_prod_inner_sub_mul_mem_polynomialsDegLE hjm (b ∘ I) hφ
      hφc hφs hv

/-- Integrating `fullContractL k (x - y) (G y) * φ y` against any locally integrable field `G` and
continuous compactly supported weight `φ` gives a polynomial of total degree at most `m` whenever
`k + 1 ≤ m`. No differentiability of `φ` is needed. -/
theorem setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {Ω : Opens (EuclideanSpace ℝ ι)}
    {k m : ℕ} (hkm : k + 1 ≤ m)
    {G : EuclideanSpace ℝ ι → IteratedGradient (EuclideanSpace ℝ ι) k}
    (hG : LocallyIntegrableOn G Ω μ) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (fun x => ∫ y in Ω, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂μ) ∈
      polynomialsDegLE ι m := by
  let b := EuclideanSpace.basisFun ι ℝ
  have hφ0 : ContDiff ℝ 0 φ := contDiff_zero.2 hφ
  have hv : ∀ I : Fin (k + 1) → ι,
      LocallyIntegrableOn (fun y => IteratedGradient.evalTupleL k (b ∘ I) (G y)) Ω μ :=
    fun I => (IteratedGradient.evalTupleL k (b ∘ I)).locallyIntegrableOn_comp hG
  have hexp : (fun x => ∫ y in Ω, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂μ) =
      ∑ I : Fin (k + 1) → ι, fun x => ∫ y in Ω, iteratedFDerivAlong ℝ []
        (fun z => (∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) * φ z) y *
        IteratedGradient.evalTupleL k (b ∘ I) (G y) ∂μ := by
    ext x
    have hg_I : ∀ I : Fin (k + 1) → ι,
        ContDiff ℝ 0 (fun z => ∏ l : Fin (k + 1), ⟪b (I l), x - z⟫_ℝ) := fun I =>
      (contDiff_prod fun l _ => (innerSL ℝ (b (I l))).contDiff.comp
        (contDiff_const.sub contDiff_id)).of_le le_top
    have hint_I : ∀ I : Fin (k + 1) → ι, IntegrableOn
        (fun y => (∏ l : Fin (k + 1), ⟪b (I l), x - y⟫_ℝ) * φ y *
          IteratedGradient.evalTupleL k (b ∘ I) (G y)) Ω μ := fun I => by
      simpa only [iteratedFDerivAlong_nil] using
        (hasCompactSupport_and_integrableOn_iteratedFDerivAlong_mul
          (hg_I I) hφ0 hφc hφs [] (by simp) (hv I)).2.2
    have hpt : ∀ y, IteratedGradient.fullContractL k (x - y) (G y) * φ y =
        ∑ I : Fin (k + 1) → ι, (∏ l : Fin (k + 1), ⟪b (I l), x - y⟫_ℝ) * φ y *
          IteratedGradient.evalTupleL k (b ∘ I) (G y) := fun y => by
      conv_lhs =>
        rw [IteratedGradient.eq_sum_evalTupleL_rankOne b k (G y), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_smul, smul_eq_mul, IteratedGradient.fullContractL_rankOne]
      simp only [Function.comp_apply]
      ring
    simp_rw [hpt, Finset.sum_apply, iteratedFDerivAlong_nil]
    exact integral_finsetSum _ fun I _ => hint_I I
  rw [hexp]
  exact Submodule.sum_mem (polynomialsDegLE ι m) fun I _ =>
    setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_mem_polynomialsDegLE hkm (fun l => b (I l))
      hφ0 hφc hφs [] (by simp) (hv I)

/-- On `W^{k+1,p}(Ω)` (`1 ≤ p ≤ ∞`), the contracted highest-derivative integral
`x ↦ ∫ y in Ω, fullContractL k (x - y) (iteratedGradient k u y) * φ y ∂μ` belongs to
`polynomialsDegLE ι m` whenever `k + 1 ≤ m` and `φ` is continuous with compact support in `Ω`. -/
theorem Wkp.setIntegral_fullContractL_sub_iteratedGradient_mul_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    {Ω : Opens (EuclideanSpace ℝ ι)} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k m : ℕ} (hkm : k + 1 ≤ m)
    (u : Wkp μ Ω p (k + 1)) {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (fun x => ∫ y in Ω,
      IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y ∂μ) ∈
      polynomialsDegLE ι m :=
  setIntegral_fullContractL_sub_mul_mem_polynomialsDegLE hkm
    (Lp.locallyIntegrableOn _ Fact.out) hφ hφc hφs

end Polynomiality

/-! ### Explicit `Lᵖ(Ω) → L^∞` diameter and chunkiness bounds -/

section Bounds

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Uniform `Lᵖ(Ω) → L^∞(closure Ω)` diameter and chunkiness bound for contracted fields.** For
bounded `Ω`, `1 ≤ p ≤ ∞`, `G ∈ Lᵖ(Ω; IteratedGradient E k)`, `x ∈ closure Ω`, and `φ` supported in
`closedBall x₀ ρ` (`0 < ρ`, `diam Ω ≤ γ * ρ`) with `‖φ y‖ ≤ M * ρ ^ (-finrank ℝ E)` on `Ω`,
`‖∫_Ω fullContractL k (x - y) (G y) φ y‖` is bounded by
`M * μ(B(0,1))^{1-1/p} * γ^{n/p} * (diam Ω)^{k + 1 - n/p} * ‖G‖`. -/
theorem norm_setIntegral_fullContractL_sub_mul_le
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ)
    (G : Lp (IteratedGradient E k) p (mu.restrict Omega))
    {x : E} (hx : x ∈ closure (Omega : Set E)) {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ}
    (hρ : 0 < ρ) (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ ((k + 1 : ℝ) - (Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖G‖ := by
  let d := Metric.diam (Omega : Set E)
  let n := Module.finrank ℝ E
  obtain ⟨y₀, hy₀⟩ := closure_nonempty_iff.1 ⟨x, hx⟩
  have hMρ : 0 ≤ M * ρ ^ (-(n : ℝ)) := (norm_nonneg (φ y₀)).trans (hφ y₀ hy₀)
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left hMρ (Real.rpow_pos_of_pos hρ _)
  have hγ : 0 ≤ γ := nonneg_of_mul_nonneg_left (Metric.diam_nonneg.trans hdiam) hρ
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · have : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).1 hn0
    have hzero : ∀ y, IteratedGradient.fullContractL k (x - y) (G y) * φ y = 0 := fun y => by
      rw [Subsingleton.elim (x - y) 0, IteratedGradient.fullContractL_zero_direction,
        zero_apply, zero_mul]
    simp only [hzero, integral_zero, norm_zero]
    positivity
  have := Module.nontrivial_of_finrank_pos hn_pos
  have hd_pos : 0 < d := Omega.isOpen.diam_pos hΩ_bdd hy₀
  refine (Lp.norm_setIntegral_le_of_support_subset_closedBall hΩ_bdd G
    (K := M * d ^ (k + 1)) hρ hdiam
    ((Function.support_mul_subset_right _ _).trans hsupp) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with y hy
    have hxy : ‖x - y‖ ≤ d := by
      dsimp only [d]; rw [← dist_eq_norm, ← Metric.diam_closure]
      exact Metric.dist_le_diam_of_mem hΩ_bdd.closure hx (subset_closure hy)
    calc ‖IteratedGradient.fullContractL k (x - y) (G y) * φ y‖
        ≤ (‖G y‖ * ‖x - y‖ ^ (k + 1)) * ‖φ y‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (IteratedGradient.norm_fullContractL_apply_le k _ _) (norm_nonneg _)
      _ ≤ (‖G y‖ * d ^ (k + 1)) * (M * ρ ^ (-(n : ℝ))) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxy _) (norm_nonneg _))
            (hφ y hy) (norm_nonneg _) (by positivity)
      _ = M * d ^ (k + 1) * ρ ^ (-(n : ℝ)) * ‖G y‖ := by ring
  · have hpow : d ^ (k + 1) * d ^ (-(n : ℝ) / p.toReal) =
        d ^ ((k + 1 : ℝ) - (n : ℝ) / p.toReal) := by
      rw [← Real.rpow_natCast d (k + 1), ← Real.rpow_add hd_pos]; congr 1; push_cast; ring
    linear_combination M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
      γ ^ ((n : ℝ) / p.toReal) * ‖G‖ * hpow

/-- **Order-zero cutoff integral bound on `W^{k,p}(Ω)`.** For bounded `Ω`, `1 ≤ p ≤ ∞`, and any
weight `φ` supported in `closedBall x₀ ρ` (`0 < ρ`, `diam Ω ≤ γ * ρ`) satisfying
`‖φ y‖ ≤ M * ρ ^ (-finrank ℝ E)` on `Ω`, the integral `∫_Ω (value k u y) φ y` is bounded by
`M * μ(B(0,1))^{1-1/p} * γ^{n/p} * (diam Ω)^{-n/p} * ‖value k u‖`. -/
theorem Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p k)
    {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ} (hρ : 0 < ρ)
    (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega, Wkp.value k u y * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖Wkp.value k u‖ := by
  refine Lp.norm_setIntegral_le_of_support_subset_closedBall hΩ_bdd (Wkp.value k u) hρ hdiam
    ((Function.support_mul_subset_right _ _).trans hsupp) ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with y hy
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hφ y hy) (norm_nonneg _)

/-- **Uniform `Lᵖ(Ω) → L^∞(closure Ω)` diameter and chunkiness bound for contracted weak
derivatives.** Specialization of `TauCeti.norm_setIntegral_fullContractL_sub_mul_le` to
`Wkp.iteratedGradient k u`. -/
theorem Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {x : E} (hx : x ∈ closure (Omega : Set E)) {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ}
    (hρ : 0 < ρ) (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega,
      IteratedGradient.fullContractL k (x - y) (Wkp.iteratedGradient k u y) * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ ((k + 1 : ℝ) - (Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖Wkp.iteratedGradient k u‖ :=
  norm_setIntegral_fullContractL_sub_mul_le hΩ_bdd k (Wkp.iteratedGradient k u) hx hρ hdiam
    hsupp hφ

end Bounds

/-! ### Concrete checks on `(-1, 1) ⊆ ℝ` -/

section Examples

-- Coordinate-free first-order derivative commutation on `(-1, 1) ⊆ ℝ` for continuous `φ`:
-- differentiating `x ↦ ∫ (x - y) u'(y) φ(y) dy` in direction `1` yields `∫ φ(y) (∂₁ u)(y) dy`.
example {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Set.Ioo (-1 : ℝ) 1) (x : ℝ) :
    fderiv ℝ (fun x' => ∫ y in Set.Ioo (-1 : ℝ) 1,
      IteratedGradient.fullContractL 0 (x' - y) (Wkp.iteratedGradient 0 u y) * φ y) x 1 =
      ∫ y in Set.Ioo (-1 : ℝ) 1, φ y * Wkp.value 0 (Wkp.lineDerivL 1 0 u) y :=
  Wkp.fderiv_setIntegral_fullContractL_sub_zero_eq u hφ hφc hφs x 1

-- Second-order derivative commutation on `(-1, 1) ⊆ ℝ` for continuous `φ`: differentiating
-- `x ↦ ∫ (x - y)² u''(y) φ(y) dy` in direction `1` brings down the factor `2`.
example {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 2)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Set.Ioo (-1 : ℝ) 1) (x : ℝ) :
    fderiv ℝ (fun x' => ∫ y in Set.Ioo (-1 : ℝ) 1,
      IteratedGradient.fullContractL 1 (x' - y) (Wkp.iteratedGradient 1 u y) * φ y) x 1 =
      2 * ∫ y in Set.Ioo (-1 : ℝ) 1,
        IteratedGradient.fullContractL 0 (x - y)
          (Wkp.iteratedGradient 0 (Wkp.lineDerivL 1 1 u) y) * φ y := by
  simpa using Wkp.fderiv_setIntegral_fullContractL_sub_succ_eq 0 u hφ hφc hφs x 1

-- One-dimensional `p = 1` scaling check on `Ω = (-1, 1)` (`diam Ω = 2`, `ρ = 1`, `γ = 2`):
-- the order-zero and order-one bounds carry diameter factors `2⁻¹` and `2⁰ = 1`, so with `γ = 2`
-- they simplify to `M * ‖value 1 u‖` and `2 * M * ‖iteratedGradient 0 u‖`.
example (u : Wkp volume ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ 1 1)
    {x : ℝ} (hx : x ∈ closure (Set.Ioo (-1 : ℝ) 1)) {φ : ℝ → ℝ} {M : ℝ}
    (hsupp : Function.support φ ⊆ Metric.closedBall (0 : ℝ) 1)
    (hφ : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, ‖φ y‖ ≤ M) :
    ‖∫ y in Set.Ioo (-1 : ℝ) 1, Wkp.value 1 u y * φ y‖ +
      ‖∫ y in Set.Ioo (-1 : ℝ) 1,
        IteratedGradient.fullContractL 0 (x - y) (Wkp.iteratedGradient 0 u y) * φ y‖ ≤
      M * ‖Wkp.value 1 u‖ + 2 * M * ‖Wkp.iteratedGradient 0 u‖ := by
  let I : Opens ℝ := ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
  have hbdd : Bornology.IsBounded (I : Set ℝ) := Metric.isBounded_Ioo (-1) 1
  have hdiam : Metric.diam (Set.Ioo (-1 : ℝ) 1) = 2 := by
    rw [Real.diam_Ioo (by norm_num)]; norm_num
  have hφ' : ∀ y ∈ (I : Set ℝ), ‖φ y‖ ≤ M * (1 : ℝ) ^ (-(Module.finrank ℝ ℝ : ℝ)) :=
    fun y hy => by simpa [I] using hφ y hy
  have htwo : (2 : ℝ) * ((2 : ℝ) ^ (-1 : ℝ) * ‖Wkp.value 1 u‖) = ‖Wkp.value 1 u‖ := by
    rw [← mul_assoc]; norm_num
  have hb0 : ‖∫ y in Set.Ioo (-1 : ℝ) 1, Wkp.value 1 u y * φ y‖ ≤ M * ‖Wkp.value 1 u‖ :=
    (Wkp.norm_setIntegral_value_mul_le_of_support_subset_closedBall
      (Omega := I) hbdd 1 u zero_lt_one (γ := 2) (by simpa [I] using hdiam.le) hsupp
      hφ').trans_eq (by simpa [I, hdiam, mul_assoc] using congrArg (M * ·) htwo)
  have hb1 : ‖∫ y in Set.Ioo (-1 : ℝ) 1,
        IteratedGradient.fullContractL 0 (x - y) (Wkp.iteratedGradient 0 u y) * φ y‖ ≤
      2 * M * ‖Wkp.iteratedGradient 0 u‖ :=
    (Wkp.norm_setIntegral_fullContractL_sub_iteratedGradient_mul_le
      (Omega := I) hbdd 0 u hx zero_lt_one (γ := 2) (by simpa [I] using hdiam.le) hsupp
      hφ').trans_eq (by simp [I, hdiam, mul_comm M 2])
  exact add_le_add hb0 hb1

end Examples

end TauCeti
