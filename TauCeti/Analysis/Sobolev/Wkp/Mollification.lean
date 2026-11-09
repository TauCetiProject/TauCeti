/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Mollification.Interior
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Interior mollification of higher weak derivatives

For a function in `W^{k+2,p}(Ω)`, the Fréchet derivative of the mollification of its
order-`k+1` weak derivative is the mollification of its order-`k+2` weak derivative.
The convolution uses zero extensions, but the identity holds only where the translated
kernel support is contained in `Ω`; no regularity of the boundary is assumed.

The result supplies the successive derivative identities needed to construct smooth
local approximations in the iterated weak Sobolev spaces. It uses the weak-derivative
identity recorded at each graph step and the interior convolution theorem.

`TauCeti.Wkp.smoothField` packages the normalized-bump mollification of a zero-extended field as
a smooth function on the whole space. `TauCeti.Wkp.gradient_smoothField` and
`TauCeti.Wkp.fderiv_smoothField` restate the derivative identities for it, and
`TauCeti.Wkp.smoothField_eq_zero` locates its support near the set off which the field vanishes.

The classical argument is in L. C. Evans, *Partial Differential Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution ENNReal Pointwise

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

/-- The mollification `φ ⋆ 1_Ω f` of the zero extension of a field `f ∈ Lᵖ(Ω)` by a normalized
bump `φ`. It is smooth on the whole space (`contDiff_smoothField`), and where the bump ball lies
in `Ω` it differentiates like the weak derivatives (`gradient_smoothField`,
`fderiv_smoothField`). -/
def smoothField [HasContDiffBump E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) : E → F :=
  phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator (f : E → F)

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] [Fact (1 ≤ p)] in
/-- `smoothField` is the convolution of the normalized bump with the zero extension. -/
theorem smoothField_def [HasContDiffBump E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) :
    smoothField phi f =
      phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator (f : E → F) :=
  (rfl)

/-- The mollification of a zero-extended `Lᵖ` field is smooth. -/
theorem contDiff_smoothField [HasContDiffBump E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothField phi f) := by
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  exact phi.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed (hmem.locallyIntegrable Fact.out)

omit [Fact (1 ≤ p)] in
/-- A mollified field vanishes at every point whose bump ball misses the set off which the field
vanishes. -/
theorem smoothField_eq_zero [HasContDiffBump E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (phi : ContDiffBump (0 : E)) {K : Set E} (f : Lp F p (mu.restrict Omega))
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
  rw [smoothField_def, convolution_congr _ (Filter.EventuallyEq.refl _ _) hae]
  refine Function.notMem_support.1 fun hmem => hy ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset _ hmem
  rw [ContDiffBump.support_normed_eq] at ha
  have hbK : b ∈ K := support_indicator_subset hb
  exact ⟨b, hbK, a, Metric.ball_subset_closedBall ha, add_comm b a⟩

/-- At a point whose bump ball lies in `Ω`, the derivative of the mollified `k`th iterated
weak-gradient field is the mollified `(k+1)`st field. -/
theorem fderiv_smoothField [HasContDiffBump E] (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ (smoothField phi (iteratedGradient k (lowerOrder (k + 1) u))) x =
      smoothField phi (iteratedGradient (k + 1) u) x := by
  simpa only [smoothField_def, convolution_flip] using
    fderiv_indicator_convolution_normed_iteratedGradient k u phi x hx

/-- At a point whose bump ball lies in `Ω`, the gradient of the mollified value of a first-order
Sobolev function is the mollified weak gradient. -/
theorem gradient_smoothField [HasContDiffBump E] (u : Wkp mu Omega p 1)
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    gradient (smoothField phi (value 1 u)) x =
      smoothField phi (iteratedGradient 0 u) x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  have hd := fderiv_indicator_convolution_normed_value u phi x hx
  rw [convolution_flip, convolution_flip] at hd
  rw [smoothField_def, hd]
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp (iteratedGradient 0 u))
  have hi := (phi.hasCompactSupport_normed (μ := mu)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.continuous_normed (hmem.locallyIntegrable Fact.out) x
  -- Passing the Riesz map through the integral identifies the vector convolution's dual.
  symm
  rw [smoothField_def, convolution_def]
  refine ((InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap
    |>.integral_comp_comm hi).symm.trans ?_
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : x - y ∈ Omega <;> simp [hy, ContinuousLinearMap.lsmul_apply]

end TauCeti.Wkp
