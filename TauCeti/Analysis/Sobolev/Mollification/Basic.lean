/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollification of weakly differentiable functions

This file proves the identity at the heart of mollification in Sobolev spaces. If `u'` is the
weak derivative of `u` in the direction `v` on an open domain and `rho` is smooth with compact
support, then

`D_v (u ⋆ rho) = u' ⋆ rho`

at every point `x` for which `x - tsupport rho` lies in the domain. The convolved function
(and, for the Fréchet form, its weak derivative field) is assumed locally integrable on the
whole space; zero extensions of domain `Lᵖ` functions satisfy this assumption. No weak
derivative identity outside the domain is required.

The results hold for functions with values in an arbitrary real Banach space and for any
s-finite, left-invariant measure on a real normed space, such as an additive Haar measure.

This identity applies successively to the derivative fields of a Sobolev function, and is the
analytic input to local smooth approximation and Meyers--Serrin density.

## Main statements

* `TauCeti.HasWeakLineDerivOn.hasLineDerivAt_convolution_right`: convolution by a smooth,
  compactly supported scalar kernel turns a local weak directional derivative into the
  corresponding classical directional derivative.
* `TauCeti.HasWeakFDerivOn.hasFDerivAt_convolution_right`: the Fréchet form, identifying the
  derivative with the convolution of the weak derivative field.
* `TauCeti.HasWeakLineDerivOn.lineDeriv_convolution_right` and
  `TauCeti.HasWeakFDerivOn.fderiv_convolution_right`: the corresponding derivative equations.

## References

L. C. Evans, *Partial Differential Equations*, Section 5.3.1, Theorem 1; L. C. Evans and
R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, Section 4.1.1.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped ContDiff Convolution Distributions

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddLeftInvariant] [SFinite mu] {Omega : Opens E}

/-- **A weak derivative commutes with convolution by a smooth compactly supported kernel.**
If `u'` is the weak derivative of `u` in the direction `v` on `Omega`, then the convolution of
`u` with `rho` has directional derivative `(u' ⋆ rho) x` in the direction `v` at every point `x`
whose translated kernel support `x - tsupport rho` is contained in `Omega`. -/
theorem HasWeakLineDerivOn.hasLineDerivAt_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasLineDerivAt ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) ((u' ⋆[(lsmul ℝ ℝ).flip, mu] rho) x) x v := by
  have hsmooth : ContDiff ℝ ∞ fun t ↦ rho (x - t) := by fun_prop
  have hcpt : HasCompactSupport fun t ↦ rho (x - t) :=
    hrho_cpt.comp_homeomorph (Homeomorph.subLeft x)
  have hsupp : tsupport (fun t ↦ rho (x - t)) ⊆ Omega := fun t ht ↦ by
    simpa using hx _ (tsupport_comp_subset_preimage rho (f := (x - ·)) (by fun_prop) ht)
  have hline (t : E) : lineDeriv ℝ (fun s ↦ rho (x - s)) t v = -fderiv ℝ rho (x - t) v := by
    simpa [Function.comp_def] using ((hrho.differentiable (by simp) (x - t)).hasFDerivAt.comp t
      ((hasFDerivAt_id t).const_sub x)).hasLineDerivAt v |>.lineDeriv
  have hweak := h.integral_lineDeriv_smul_eq_neg_integral_smul ⟨_, hsmooth, hcpt, hsupp⟩
  simp only [TestFunction.coe_mk, hline, neg_smul, integral_neg, neg_inj] at hweak
  convert (hrho_cpt.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu
    (hrho.of_le (by simp)) x).hasLineDerivAt v using 1
  rw [convolution_precompR_apply (lsmul ℝ ℝ).flip hu (hrho_cpt.fderiv ℝ)
    (hrho.continuous_fderiv (by simp)) x v]
  simpa only [convolution_def, flip_apply, lsmul_apply] using hweak.symm

/-- The directional derivative of a convolution with a smooth compactly supported kernel is the
convolution of the weak directional derivative with that kernel. -/
theorem HasWeakLineDerivOn.lineDeriv_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    lineDeriv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) x v = (u' ⋆[(lsmul ℝ ℝ).flip, mu] rho) x :=
  (h.hasLineDerivAt_convolution_right hu rho hrho hrho_cpt x hx).lineDeriv

/-- **The Fréchet derivative of a mollification is the mollification of the weak derivative.**
If `U` is a weak derivative field of `u` on `Omega` and both are locally integrable on the whole
space, the convolution of `u` with a smooth compactly supported scalar kernel `rho` has derivative
`(U ⋆ rho) x` at every point `x` whose translated kernel support `x - tsupport rho` lies in
`Omega`. -/
theorem HasWeakFDerivOn.hasFDerivAt_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) ((U ⋆[(lsmul ℝ ℝ).flip, mu] rho) x) x := by
  have hd := hrho_cpt.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu (hrho.of_le (by simp)) x
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  refine ((hd.hasLineDerivAt v).unique ((h.hasWeakLineDerivOn v).hasLineDerivAt_convolution_right
    hu rho hrho hrho_cpt x hx)).trans ?_
  have hInt := (hrho_cpt.convolutionExists_right (lsmul ℝ ℝ).flip hU hrho.continuous x).integrable
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hInt]
  simp only [flip_apply, lsmul_apply, smul_apply]

/-- The Fréchet derivative of a convolution with a smooth compactly supported kernel is the
convolution of the weak Fréchet derivative field with that kernel. -/
theorem HasWeakFDerivOn.fderiv_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) x = (U ⋆[(lsmul ℝ ℝ).flip, mu] rho) x :=
  (h.hasFDerivAt_convolution_right hu hU rho hrho hrho_cpt x hx).fderiv

end TauCeti
