/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Mollification.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Interior mollification of domain Sobolev functions

A function and its weak derivative in `Lᵖ(Ω)`, for `1 ≤ p ≤ ∞`, can be extended by zero
and convolved with a smooth compactly supported kernel. Wherever the translated kernel
support lies inside `Ω`, the classical derivative of the mollification is the mollification
of the weak derivative. Zero extension need not preserve weak differentiability at the boundary;
the support condition ensures that no boundary term enters the identity.

`HasWeakFDerivOn.hasFDerivAt_convolution_indicator_right` states this for arbitrary kernels.
`HasWeakFDerivOn.hasFDerivAt_normedBump_indicator` specializes to normalized smooth bumps,
with the geometric condition that the closed ball of the outer radius lies inside the domain.
The vector-valued formulation applies to successive weak derivative fields when constructing
smooth local approximations in higher-order Sobolev spaces.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] [SFinite mu] [IsLocallyFiniteMeasure mu]
  {Omega : Opens E} {u : E → F} {U : E → E →L[ℝ] F} {p q : ℝ≥0∞}

/-- Interior differentiation of convolution after extension by zero. The function and its
weak derivative may have different integrability exponents, including infinity. -/
theorem HasWeakFDerivOn.hasFDerivAt_convolution_indicator_right
    (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho)
      ((((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] rho) x) x := by
  have hu_ext : MemLp ((Omega : Set E).indicator u) p mu :=
    (memLp_indicator_iff_restrict (f := u) Omega.isOpen.measurableSet).2 hu
  have hU_ext : MemLp ((Omega : Set E).indicator U) q mu :=
    (memLp_indicator_iff_restrict (f := U) Omega.isOpen.measurableSet).2 hU
  have h_ext : HasWeakFDerivOn mu Omega
      ((Omega : Set E).indicator u) ((Omega : Set E).indicator U) :=
    (h.congr_ae (indicator_ae_eq_restrict Omega.isOpen.measurableSet).symm).congr_ae_deriv
      (indicator_ae_eq_restrict Omega.isOpen.measurableSet).symm
  exact h_ext.hasFDerivAt_convolution_right (hu_ext.locallyIntegrable hp)
    (hU_ext.locallyIntegrable hq) rho hrho hrho_cpt x hx

/-- Mollification by a normalized smooth bump differentiates a domain weak derivative inside
any closed ball of the bump's outer radius contained in the domain. -/
theorem HasWeakFDerivOn.hasFDerivAt_normedBump_indicator
    [FiniteDimensional ℝ E] [HasContDiffBump E]
    (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] phi.normed mu)
      ((((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] phi.normed mu) x) x := by
  apply h.hasFDerivAt_convolution_indicator_right hu hU hp hq
    (phi.normed mu) phi.contDiff_normed phi.hasCompactSupport_normed x
  intro y hy
  apply hx
  rw [phi.tsupport_normed_eq] at hy
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
    sub_zero] using hy

end TauCeti
