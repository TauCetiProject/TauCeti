/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Mollification.Interior
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Convolution.Basic

/-!
# Interior mollification of higher weak derivatives

For a function in `W^{k+2,p}(Ω)`, the Fréchet derivative of the mollification of its
order-`k+1` weak derivative is the mollification of its order-`k+2` weak derivative.
The convolution uses zero extensions, but the identity is guaranteed wherever the translated
kernel support is contained in `Ω`; no regularity of the boundary is assumed.

The result supplies the successive derivative identities needed to construct smooth
local approximations in the iterated weak Sobolev spaces. It uses the weak-derivative
identity recorded at each graph step and the interior convolution theorem.

The interior mollification is packaged as `TauCeti.Wkp.smoothField`, the convolution of a
normalized bump with the zero extension of a field in `Lᵖ(Ω)`. It is smooth on the whole space
(`TauCeti.Wkp.contDiff_smoothField`); where the bump stays in `Ω`, its gradient and Hessian are the
mollified weak gradient and weak Hessian (`TauCeti.Wkp.gradient_smoothField`,
`TauCeti.Wkp.fderiv_gradient_smoothField_value`). At arbitrary order, the same identification is
`TauCeti.Wkp.iteratedGradientChain_smoothField_value`. The mollification of a function agreeing
with a continuous `v` stays close to `v` where `v` varies little
(`TauCeti.Wkp.dist_smoothField_le`). `TauCeti.Wkp.smoothField_eq_zero_of_notMem_add_closedBall`
locates its support near the set off which the field vanishes.
These are the inputs for passing estimates from smooth functions to strong `W^{2,p}` solutions.

The classical argument is in L. C. Evans, *Partial Differential Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution ENNReal Gradient Pointwise Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The first derivative identity for the mollified Sobolev jet. The gradient stored by
`Wkp` is converted to a linear functional using the real inner product. -/
theorem hasFDerivAt_indicator_convolution_value (u : Wkp mu Omega p 1)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator (value 1 u : E → ℝ)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip, mu] rho)
      ((((Omega : Set E).indicator
        (fun y => innerSL ℝ (iteratedGradient 0 u y))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ).flip, mu] rho) x) x := by
  have hgrad : MemLp (fun y => innerSL ℝ (iteratedGradient 0 u y)) p
      (mu.restrict Omega) := by
    exact (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp_memLp'
      (Lp.memLp (iteratedGradient 0 u))
  exact (hasWeakFDerivOn_value u).hasFDerivAt_indicator_convolution_right
    (Lp.memLp _) hgrad Fact.out Fact.out rho hrho hrho_cpt x hx

/-- Pointwise derivative form of `hasFDerivAt_indicator_convolution_value`. -/
-- Compute the Wkp derivative before converting its value field to W1p.
@[simp↓] theorem fderiv_indicator_convolution_value (u : Wkp mu Omega p 1)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator (value 1 u : E → ℝ)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip, mu] rho) x =
      (((Omega : Set E).indicator
        (fun y => innerSL ℝ (iteratedGradient 0 u y))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ).flip, mu] rho) x :=
  (hasFDerivAt_indicator_convolution_value u rho hrho hrho_cpt x hx).fderiv

/-- The classical derivative of the mollified `k`th iterated weak-gradient field
is the mollified `(k+1)`st field in the interior of the domain. -/
theorem hasFDerivAt_indicator_convolution_iteratedGradient (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator
        (iteratedGradient k (lowerOrder (k + 1) u) : E → IteratedGradient E k)) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E k →L[ℝ] IteratedGradient E k).flip, mu] rho)
      ((((Omega : Set E).indicator
        (iteratedGradient (k + 1) u : E → IteratedGradient E (k + 1))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E (k + 1) →L[ℝ]
              IteratedGradient E (k + 1)).flip, mu] rho) x) x := by
  exact (hasWeakFDerivOn_iteratedGradient k u).hasFDerivAt_indicator_convolution_right
    (Lp.memLp _) (Lp.memLp _) Fact.out Fact.out rho hrho hrho_cpt x hx

/-- Pointwise derivative form of `hasFDerivAt_indicator_convolution_iteratedGradient`. -/
@[simp] theorem fderiv_indicator_convolution_iteratedGradient (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator
        (iteratedGradient k (lowerOrder (k + 1) u) : E → IteratedGradient E k)) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E k →L[ℝ] IteratedGradient E k).flip, mu] rho) x =
      (((Omega : Set E).indicator
        (iteratedGradient (k + 1) u : E → IteratedGradient E (k + 1))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E (k + 1) →L[ℝ]
              IteratedGradient E (k + 1)).flip, mu] rho) x :=
  (hasFDerivAt_indicator_convolution_iteratedGradient k u rho hrho hrho_cpt x hx).fderiv

/-- With a normalized smooth bump, the support condition is supplied by a closed ball
contained in the domain. This version can be applied at each stage of a Sobolev jet
without choosing a separate support bound for the bump. -/
theorem hasFDerivAt_indicator_convolution_normed_iteratedGradient
    [HasContDiffBump E] (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator
        (iteratedGradient k (lowerOrder (k + 1) u) : E → IteratedGradient E k)) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E k →L[ℝ] IteratedGradient E k).flip, mu]
            phi.normed mu)
      ((((Omega : Set E).indicator
        (iteratedGradient (k + 1) u : E → IteratedGradient E (k + 1))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E (k + 1) →L[ℝ]
              IteratedGradient E (k + 1)).flip, mu] phi.normed mu) x) x := by
  exact (hasWeakFDerivOn_iteratedGradient k u).hasFDerivAt_indicator_convolution_normed
    (Lp.memLp _) (Lp.memLp _) Fact.out Fact.out phi x hx

/-- The derivative of a normalized-bump mollification of the value of a first-order
Sobolev function, at points whose bump stays in the domain. -/
theorem hasFDerivAt_indicator_convolution_normed_value [HasContDiffBump E]
    (u : Wkp mu Omega p 1) (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator (value 1 u : E → ℝ)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip, mu] phi.normed mu)
      ((((Omega : Set E).indicator
        (fun y => innerSL ℝ (iteratedGradient 0 u y))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ).flip, mu]
            phi.normed mu) x) x := by
  have hgrad : MemLp (fun y => innerSL ℝ (iteratedGradient 0 u y)) p
      (mu.restrict Omega) := by
    exact (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp_memLp'
      (Lp.memLp (iteratedGradient 0 u))
  exact (hasWeakFDerivOn_value u).hasFDerivAt_indicator_convolution_normed
    (Lp.memLp _) hgrad Fact.out Fact.out phi x hx

/-- Pointwise derivative form of `hasFDerivAt_indicator_convolution_normed_value`. -/
-- Compute the Wkp derivative before converting its value field to W1p.
@[simp↓] theorem fderiv_indicator_convolution_normed_value [HasContDiffBump E]
    (u : Wkp mu Omega p 1) (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator (value 1 u : E → ℝ)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip, mu]
          phi.normed mu) x =
      (((Omega : Set E).indicator
        (fun y => innerSL ℝ (iteratedGradient 0 u y))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ).flip, mu]
          phi.normed mu) x :=
  (hasFDerivAt_indicator_convolution_normed_value u phi x hx).fderiv

/-- Pointwise derivative form of
`hasFDerivAt_indicator_convolution_normed_iteratedGradient`. -/
@[simp] theorem fderiv_indicator_convolution_normed_iteratedGradient
    [HasContDiffBump E] (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator
        (iteratedGradient k (lowerOrder (k + 1) u) : E → IteratedGradient E k)) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E k →L[ℝ] IteratedGradient E k).flip, mu]
            phi.normed mu) x =
      (((Omega : Set E).indicator
        (iteratedGradient (k + 1) u : E → IteratedGradient E (k + 1))) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] IteratedGradient E (k + 1) →L[ℝ]
              IteratedGradient E (k + 1)).flip, mu] phi.normed mu) x :=
  (hasFDerivAt_indicator_convolution_normed_iteratedGradient k u phi x hx).fderiv

/-- The smooth convolution representative of a zero-extended field: the convolution of the
normalized bump `phi` with the extension by zero of `f ∈ Lᵖ(Ω)`. Applied to the value and the weak
derivatives of a Sobolev function, it gives the interior mollification of that function together
with its classical derivatives. -/
def smoothField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) : E → F :=
  phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator (f : E → F)

omit [BorelSpace E] [mu.IsAddHaarMeasure] [Fact (1 ≤ p)] in
/-- `smoothField phi f` is the convolution of the normalized bump with the zero extension of `f`. -/
theorem smoothField_def {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) :
    smoothField phi f =
      phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator (f : E → F) := by
  rw [smoothField]

/-- Mollifying a bounded field after zero extension preserves its essential supremum bound
at every point of the ambient space. This is a bound on the field mollification, not on
classical derivatives across the boundary of `Ω`. -/
theorem norm_smoothField_top_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F ∞ (mu.restrict Omega)) (x : E) :
    ‖smoothField phi f x‖ ≤ ‖f‖ := by
  have hf := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  rw [smoothField_def, convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
    (EventuallyEq.refl _ _) hf.coeFn_toLp.symm]
  have h := norm_convolution_lsmul_le_integral_norm_mul_norm phi.integrable_normed
    (hf.toLp _) x
  simpa only [Real.norm_of_nonneg (phi.nonneg_normed _), phi.integral_normed,
    one_mul, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict
      Omega.isOpen.measurableSet.nullMeasurableSet, ← Lp.norm_def] using h

/-- The smooth convolution representative of a field in `Lᵖ(Ω)` is smooth on the whole space. -/
theorem contDiff_smoothField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothField phi f) := by
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  exact phi.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed (hmem.locallyIntegrable Fact.out)

omit [Fact (1 ≤ p)] in
/-- A mollified field vanishes at every point whose bump ball misses the set off which the field
vanishes. -/
theorem smoothField_eq_zero_of_notMem_add_closedBall {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) {K : Set E} (f : Lp F p (mu.restrict Omega))
    (hf : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → f x = 0) {y : E}
    (hy : y ∉ K + Metric.closedBall (0 : E) phi.rOut) :
    smoothField phi f y = 0 := by
  have hae : (Omega : Set E).indicator (f : E → F) =ᵐ[mu]
      K.indicator ((Omega : Set E).indicator (f : E → F)) := by
    filter_upwards [(ae_restrict_iff' Omega.isOpen.measurableSet).1 hf] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK]
      by_cases hxO : x ∈ (Omega : Set E)
      · rw [indicator_of_mem hxO, hx hxO hxK]
      · exact indicator_of_notMem hxO _
  rw [smoothField_def, convolution_congr _ (EventuallyEq.refl _ _) hae]
  refine Function.notMem_support.1 fun hmem => hy ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset _ hmem
  rw [ContDiffBump.support_normed_eq] at ha
  have hbK : b ∈ K := support_indicator_subset hb
  exact ⟨b, hbK, a, Metric.ball_subset_closedBall ha, add_comm b a⟩

/-- Where the bump stays in `Ω`, the derivative of the mollified order-`k+1` weak derivative of
`u ∈ W^{k+2,p}(Ω)` is the mollified order-`k+2` weak derivative. -/
theorem fderiv_smoothField (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ (smoothField phi (iteratedGradient k (lowerOrder (k + 1) u))) x =
      smoothField phi (iteratedGradient (k + 1) u) x := by
  simpa only [smoothField, convolution_flip] using
    fderiv_indicator_convolution_normed_iteratedGradient k u phi x hx

/-- Where the bump stays in `Ω`, the gradient of the mollified value of `u ∈ W^{1,p}(Ω)` is the
mollified weak gradient. -/
theorem gradient_smoothField (u : Wkp mu Omega p 1)
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    gradient (smoothField phi (value 1 u)) x =
      smoothField phi (iteratedGradient 0 u) x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  have hd := fderiv_indicator_convolution_normed_value u phi x hx
  rw [convolution_flip, convolution_flip] at hd
  rw [smoothField, hd]
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp (iteratedGradient 0 u))
  have hi := (phi.hasCompactSupport_normed (μ := mu)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.continuous_normed (hmem.locallyIntegrable Fact.out) x
  -- Passing the Riesz map through the integral identifies the vector convolution's dual.
  symm
  rw [smoothField, convolution_def]
  refine ((InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap
    |>.integral_comp_comm hi).symm.trans ?_
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : x - y ∈ Omega <;> simp [hy, ContinuousLinearMap.lsmul_apply]

/-- For `u ∈ W^{k+1,p}(Ω)`, the classical order-`k+1` iterated gradient of
`smoothField phi (value (k + 1) u)` equals the mollification of its highest weak derivative
`iteratedGradient k u` wherever the closed bump ball lies in `Ω`, for `1 ≤ p ≤ ∞`. -/
theorem iteratedGradientChain_smoothField_value (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    iteratedGradientChain (smoothField phi (value (k + 1) u)) k x =
      smoothField phi (iteratedGradient k u) x := by
  induction k generalizing x with
  | zero =>
    simpa only [iteratedGradientChain_zero] using gradient_smoothField u phi x hx
  | succ k ih =>
    have hnear : ∀ᶠ y in 𝓝 x, Metric.closedBall y phi.rOut ⊆ Omega := by
      have h := (isCompact_closedBall (0 : E) phi.rOut).eventually_forall_of_forall_eventually
        (P := fun y z ↦ y + z ∈ (Omega : Set E)) (x₀ := x) (fun z hz ↦
          continuous_add.continuousAt.eventually (Omega.isOpen.mem_nhds (hx (by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hz))))
      filter_upwards [h] with y hy z hz
      simpa only [add_sub_cancel] using hy (z - y) (by
        simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz)
    have heq : iteratedGradientChain (smoothField phi (value (k + 2) u)) k =ᶠ[𝓝 x]
        smoothField phi (iteratedGradient k (lowerOrder (k + 1) u)) := by
      filter_upwards [hnear] with y hy
      rw [value_succ]
      exact ih (lowerOrder (k + 1) u) y hy
    rw [iteratedGradientChain_succ, heq.fderiv_eq]
    exact fderiv_smoothField k u phi x hx

/-- Where the closed bump ball stays in `Ω`, the derivative at `x` of the gradient of the
mollified value of `u ∈ W^{2,p}(Ω)`, its Hessian operator, is the mollified weak Hessian. -/
theorem fderiv_gradient_smoothField_value (u : Wkp mu Omega p 2) (phi : ContDiffBump (0 : E))
    {x : E} (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ (∇ (smoothField phi (value 2 u))) x = smoothField phi (iteratedGradient 1 u) x := by
  simpa only [iteratedGradientChain_succ, iteratedGradientChain_zero] using
    iteratedGradientChain_smoothField_value 1 u phi x hx

omit [Fact (1 ≤ p)] in
/-- The classical order-`k+1` derivative of a mollified Sobolev function is bounded by the
essential supremum of its weak derivative wherever the closed bump ball stays in `Ω`. -/
theorem norm_iteratedGradientChain_smoothField_value_top_le (k : ℕ)
    (u : Wkp mu Omega ∞ (k + 1)) (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    ‖iteratedGradientChain (smoothField phi (value (k + 1) u)) k x‖ ≤
      ‖iteratedGradient k u‖ := by
  rw [iteratedGradientChain_smoothField_value k u phi x hx]
  exact norm_smoothField_top_le phi _ x

/-- On compact `K ⊆ Ω`, the classical order-`k+1` iterated gradient of
`smoothField (phi i) (value (k + 1) u)` eventually agrees on `K` with
`smoothField (phi i) (iteratedGradient k u)`, for `u ∈ W^{k+1,p}(Ω)`. -/
theorem eventually_eqOn_iteratedGradientChain_smoothField_value
    (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ Omega) :
    ∀ᶠ i in l, EqOn (iteratedGradientChain (smoothField (phi i) (value (k + 1) u)) k)
      (smoothField (phi i) (iteratedGradient k u)) K := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKO
  filter_upwards [hphi.eventually (gt_mem_nhds hδ)] with i hi x hx
  apply iteratedGradientChain_smoothField_value k u (phi i) x
  intro y hy
  exact hδO (Metric.mem_cthickening_of_dist_le y x δ K hx
    ((Metric.mem_closedBall.mp hy).trans hi.le))

omit [Fact (1 ≤ p)] in
/-- **Mollification of a continuous representative.** If `f ∈ Lᵖ(Ω)` agrees almost everywhere on
`Ω` with `v`, the ball of radius `phi.rOut` about `x` lies in `Ω`, and `v` stays within `ε` of
`v x` on that ball, then the mollification `smoothField phi f` stays within `ε` of `v x` at `x`. -/
theorem dist_smoothField_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (phi : ContDiffBump (0 : E)) {f : Lp F p (mu.restrict Omega)} {v : E → F}
    (hfv : f =ᵐ[mu.restrict Omega] v) {x : E} {ε : ℝ}
    (hx : Metric.ball x phi.rOut ⊆ Omega)
    (hv : ∀ y ∈ Metric.ball x phi.rOut, dist (v y) (v x) ≤ ε) :
    dist (smoothField phi f x) (v x) ≤ ε := by
  have hO := Omega.isOpen.measurableSet
  have hind : (Omega : Set E).indicator (f : E → F) =ᵐ[mu] (Omega : Set E).indicator v := by
    filter_upwards [(ae_restrict_iff' hO).1 hfv] with y hy
    by_cases hyO : y ∈ (Omega : Set E)
    · simp [hyO, hy hyO]
    · simp [hyO]
  have hmeas : AEStronglyMeasurable ((Omega : Set E).indicator v) mu :=
    ((aestronglyMeasurable_indicator_iff hO).2 (Lp.aestronglyMeasurable f)).congr hind
  have hxO : x ∈ (Omega : Set E) := hx (Metric.mem_ball_self phi.rOut_pos)
  rw [smoothField_def, convolution_congr _ (EventuallyEq.refl _ _) hind]
  convert phi.dist_normed_convolution_le hmeas fun y hy => ?_ using 2
  · exact (Set.indicator_of_mem hxO v).symm
  · rw [Set.indicator_of_mem (hx hy), Set.indicator_of_mem hxO]
    exact hv y hy

end TauCeti.Wkp
