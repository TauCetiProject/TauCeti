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

/-!
# Interior mollification of higher weak derivatives

For a function in `W^{k+2,p}(Ω)`, the Fréchet derivative of the mollification of its
order-`k+1` weak derivative is the mollification of its order-`k+2` weak derivative.
The convolution uses zero extensions, but the identity holds only where the translated
kernel support is contained in `Ω`; no regularity of the boundary is assumed.

The result supplies the successive derivative identities needed to construct smooth
local approximations in the iterated weak Sobolev spaces. It uses the weak-derivative
identity recorded at each graph step and the interior convolution theorem.

The interior mollification is packaged as `TauCeti.Wkp.smoothField`, the convolution of a
normalized bump with the zero extension of a field in `Lᵖ(Ω)`. It is smooth on the whole space
(`TauCeti.Wkp.contDiff_smoothField`); where the bump stays in `Ω`, its gradient and Hessian are the
mollified weak gradient and weak Hessian (`TauCeti.Wkp.gradient_smoothField`,
`TauCeti.Wkp.fderiv_gradient_smoothField_value`); and the mollification of a function agreeing
with a continuous `v` stays close to `v` where `v` varies little
(`TauCeti.Wkp.dist_smoothField_le`).
These are the inputs for passing estimates from smooth functions to strong `W^{2,p}` solutions.

The classical argument is in L. C. Evans, *Partial Differential Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution ENNReal Gradient Topology

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

/-- The smooth convolution representative of a field in `Lᵖ(Ω)` is smooth on the whole space. -/
theorem contDiff_smoothField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothField phi f) := by
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  exact phi.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed (hmem.locallyIntegrable Fact.out)

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

/-- Where every bump centred near `x` stays in `Ω`, the derivative at `x` of the gradient of the
mollified value of `u ∈ W^{2,p}(Ω)`, its Hessian operator, is the mollified weak Hessian. -/
theorem fderiv_gradient_smoothField_value (u : Wkp mu Omega p 2) (phi : ContDiffBump (0 : E))
    {x : E} (hx : ∀ᶠ y in 𝓝 x, Metric.closedBall y phi.rOut ⊆ Omega) :
    fderiv ℝ (∇ (smoothField phi (value 2 u))) x = smoothField phi (iteratedGradient 1 u) x := by
  have hgrad : ∇ (smoothField phi (value 2 u)) =ᶠ[𝓝 x]
      smoothField phi (iteratedGradient 0 (lowerOrder 1 u)) := by
    filter_upwards [hx] with y hy
    rw [value_succ]
    exact gradient_smoothField (lowerOrder 1 u) phi y hy
  rw [hgrad.fderiv_eq]
  exact fderiv_smoothField 0 u phi x hx.self_of_nhds

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
