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
identity recorded at each graph step and the interior convolution theorem. Iterating these
identities, `TauCeti.Wkp.iteratedGradientChain_normed_convolution_indicator_value` identifies
every classical iterated-gradient field of a mollified value with the mollified weak derivative
of the same order, wherever the bump stays in `Ω`.

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

/-- **Derivatives of a mollified Sobolev function.** Let `u ∈ W^{k+1,p}(Ω)` and let `φ` be a smooth
bump whose closed support ball, centred at any point of the open set `U`, lies in `Ω`. On `U`, the
classical iterated-gradient field of order `k` of the mollified zero extension of the value of `u`
is the mollified zero extension of the highest weak derivative of `u`. -/
theorem iteratedGradientChain_normed_convolution_indicator_value [HasContDiffBump E]
    (phi : ContDiffBump (0 : E))
    {U : Set E} (hU : IsOpen U) (hphi : ∀ x ∈ U, Metric.closedBall x phi.rOut ⊆ Omega) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)) (x : E), x ∈ U →
      iteratedGradientChain
          (phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
            (Omega : Set E).indicator (value (k + 1) u : E → ℝ)) k x =
        (phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
          (Omega : Set E).indicator (iteratedGradient k u : E → IteratedGradient E k)) x := by
  intro k
  induction k with
  | zero =>
      intro u x hx
      rw [iteratedGradientChain_zero]
      apply (InnerProductSpace.toDual ℝ E).injective
      rw [toDual_gradient]
      have hd := (hasFDerivAt_indicator_convolution_normed_value u phi x (hphi x hx)).fderiv
      rw [convolution_flip, convolution_flip] at hd
      rw [hd]
      have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
        (Lp.memLp (iteratedGradient 0 u))
      have hi := (phi.hasCompactSupport_normed (μ := mu)).convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ) phi.continuous_normed
        (hmem.locallyIntegrable Fact.out) x
      -- Passing the Riesz map through the integral identifies the vector convolution's dual.
      symm
      rw [convolution_def]
      refine ((InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap
        |>.integral_comp_comm hi).symm.trans ?_
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : x - y ∈ Omega <;> simp [hy, ContinuousLinearMap.lsmul_apply]
  | succ k ih =>
      intro u x hx
      rw [iteratedGradientChain_succ]
      have heq : iteratedGradientChain
          (phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
            (Omega : Set E).indicator (value (k + 1 + 1) u : E → ℝ)) k =ᶠ[𝓝 x]
          phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
            (Omega : Set E).indicator
              (iteratedGradient k (lowerOrder (k + 1) u) : E → IteratedGradient E k) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        simpa only [value_succ (k + 1) u] using ih (lowerOrder (k + 1) u) y hy
      rw [heq.fderiv_eq]
      simpa only [convolution_flip] using
        (hasFDerivAt_indicator_convolution_normed_iteratedGradient k u phi x (hphi x hx)).fderiv

end TauCeti.Wkp
