/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Mollification.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Interior mollification of domain Sobolev functions

A function and its weak derivative in `Lᵖ(Ω)`, for `1 ≤ p ≤ ∞`, can be extended by zero
and convolved with a smooth compactly supported kernel. Wherever the translated kernel
support lies inside `Ω`, the classical derivative of the mollification is the mollification
of the weak derivative. Zero extension need not preserve weak differentiability at the boundary;
the support condition ensures that no boundary term enters the identity.

`HasWeakFDerivOn.hasFDerivAt_indicator_convolution_right` states this for arbitrary kernels.
`HasWeakFDerivOn.hasFDerivAt_indicator_convolution_normed` specializes to normalized smooth bumps,
with the geometric condition that the closed ball of the outer radius lies inside the domain.
The vector-valued formulation applies to successive weak derivative fields when constructing
smooth local approximations in higher-order Sobolev spaces.

`HasWeakFDerivOn.exists_testFunction_convolution_normed` packages the mollifications of a compactly
supported field as test functions on `Ω` whose derivatives near the support are the mollifications
of the weak derivative; this approximates Sobolev test fields by smooth ones.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution ENNReal Distributions Pointwise

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [SFinite mu] [IsLocallyFiniteMeasure mu]
  {Omega : Opens E} {u : E → F} {U : E → E →L[ℝ] F} {p q : ℝ≥0∞}

/-- If `U` is a weak derivative field of `u` on `Omega`, with `u ∈ Lᵖ(Omega)` and
`U ∈ L^q(Omega)` for `1 ≤ p, q ≤ ∞`, the convolution of the zero extension of `u` with a
smooth compactly supported kernel `rho` has derivative at `x` the convolution of the zero
extension of `U` with `rho`, whenever `x - tsupport rho ⊆ Omega`. -/
theorem HasWeakFDerivOn.hasFDerivAt_indicator_convolution_right
    [mu.IsAddLeftInvariant] (h : HasWeakFDerivOn mu Omega u U)
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
    (memLp_indicator_iff_restrict (f := u) Omega.isOpen.measurableSet.nullMeasurableSet).2 hu
  have hU_ext : MemLp ((Omega : Set E).indicator U) q mu :=
    (memLp_indicator_iff_restrict (f := U) Omega.isOpen.measurableSet.nullMeasurableSet).2 hU
  exact h.indicator.hasFDerivAt_convolution_right (hu_ext.locallyIntegrable hp)
    (hU_ext.locallyIntegrable hq) rho hrho hrho_cpt x hx

/-- Where `x - tsupport rho ⊆ Omega`, the Fréchet derivative of the convolution of the zero
extension of `u` with `rho` equals the convolution of the zero extension of its weak derivative
field `U` with `rho`. The fields may have different integrability exponents `1 ≤ p, q ≤ ∞`. -/
theorem HasWeakFDerivOn.fderiv_indicator_convolution_right
    [mu.IsAddLeftInvariant] (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x =
      (((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] rho) x :=
  (h.hasFDerivAt_indicator_convolution_right hu hU hp hq rho hrho hrho_cpt x hx).fderiv

omit [SFinite mu] [IsLocallyFiniteMeasure mu] in
/-- At any point `x` whose closed ball of radius `phi.rOut` lies in `Omega`, the mollification
of the zero extension of `u` by the normalized bump has derivative the mollification of the
zero extension of its weak derivative field `U`. -/
theorem HasWeakFDerivOn.hasFDerivAt_indicator_convolution_normed
    [FiniteDimensional ℝ E] [HasContDiffBump E] [mu.IsAddHaarMeasure]
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
  apply h.hasFDerivAt_indicator_convolution_right hu hU hp hq
    (phi.normed mu) phi.contDiff_normed phi.hasCompactSupport_normed x
  intro y hy
  apply hx
  rw [phi.tsupport_normed_eq] at hy
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
    sub_zero] using hy

omit [SFinite mu] [IsLocallyFiniteMeasure mu] in
/-- At a point `x` with `closedBall x phi.rOut ⊆ Omega`, the Fréchet derivative of the
mollification of the zero extension of `u` by the normalized bump equals the mollification
of the zero extension of its weak derivative field `U`. -/
theorem HasWeakFDerivOn.fderiv_indicator_convolution_normed
    [FiniteDimensional ℝ E] [HasContDiffBump E] [mu.IsAddHaarMeasure]
    (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] phi.normed mu) x =
      (((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] phi.normed mu) x :=
  (h.hasFDerivAt_indicator_convolution_normed hu hU hp hq phi x hx).fderiv

omit [SFinite mu] [IsLocallyFiniteMeasure mu] in
/-- **Mollifications of compactly supported Sobolev fields are test functions.** Let `u` be a
compactly supported `Lᵖ` field with weak derivative field `U ∈ L^q(Omega)`, `1 ≤ p, q`, and let
the closed `δ`-balls around the points of `K = cthickening δ (tsupport u)` lie in `Omega`. Then
for a normalized bump `phi` with `phi.rOut ≤ δ`, the mollification of `u` by `phi` is a test
function on `Omega` supported in `K`, whose derivative on `K` is the mollification of the zero
extension of `U`. -/
theorem HasWeakFDerivOn.exists_testFunction_convolution_normed
    [FiniteDimensional ℝ E] [HasContDiffBump E] [mu.IsAddHaarMeasure]
    (h : HasWeakFDerivOn mu Omega u U) (huc : HasCompactSupport u) (hu : MemLp u p mu)
    (hU : MemLp U q (mu.restrict Omega)) (hp : 1 ≤ p) (hq : 1 ≤ q) {δ : ℝ}
    (hball : ∀ x ∈ Metric.cthickening δ (tsupport u), Metric.closedBall x δ ⊆ Omega)
    (phi : ContDiffBump (0 : E)) (hphi : phi.rOut ≤ δ) :
    ∃ φ : 𝓓(Omega, F), ⇑φ = phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u ∧
      tsupport φ ⊆ Metric.cthickening δ (tsupport u) ∧
      ∀ x ∈ Metric.cthickening δ (tsupport u), fderiv ℝ φ x =
        (phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator U) x := by
  have hK'Omega : Metric.cthickening δ (tsupport u) ⊆ Omega := fun x hx =>
    hball x hx (Metric.mem_closedBall_self (phi.rOut_pos.le.trans hphi))
  set g := phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u
  have hgs : tsupport g ⊆ Metric.cthickening δ (tsupport u) := by
    have hsupp : Function.support g ⊆ Metric.thickening phi.rOut (tsupport u) := by
      refine (support_convolution_subset _).trans ?_
      rw [phi.support_normed_eq, ← ball_add_zero]
      exact add_subset_add_left (subset_tsupport u)
    exact (closure_mono hsupp).trans <| (Metric.closure_thickening_subset_cthickening _ _).trans <|
      Metric.cthickening_mono hphi _
  refine ⟨⟨g, phi.hasCompactSupport_normed.contDiff_convolution_left _ phi.contDiff_normed
      (hu.locallyIntegrable hp), huc.isCompact.cthickening.of_isClosed_subset
        (isClosed_tsupport _) hgs, hgs.trans hK'Omega⟩, rfl, hgs, fun x hx => ?_⟩
  have huOmega : (Omega : Set E).indicator u = u :=
    indicator_eq_self.2 ((subset_tsupport u).trans
      ((Metric.self_subset_cthickening _).trans hK'Omega))
  have := h.fderiv_indicator_convolution_normed (hu.restrict Omega) hU hp hq phi x
    ((Metric.closedBall_subset_closedBall hphi).trans (hball x hx))
  rw [huOmega, convolution_flip, convolution_flip] at this
  exact this

end TauCeti
