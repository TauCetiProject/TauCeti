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

`D_v (u * rho) = u' * rho`

at every point `x` for which `x - tsupport rho` lies in the domain. The convolved function
is assumed locally integrable on the whole space; zero extensions of domain `Lᵖ` functions
satisfy this assumption. No weak derivative identity outside the domain is required.

Mathlib supplies the complementary classical fact: differentiating a convolution moves the
derivative onto its smooth right factor. The weak integration-by-parts identity then moves that
derivative back from `rho` to `u`. The result is stated for functions with values in an arbitrary
real Banach space and for any sigma-finite additive Haar measure on a real normed space.

This is the analytic step needed to show that mollifying a weak Sobolev function produces a
smooth function with the expected derivatives. This local identity applies successively to the
derivative fields of a Sobolev function, and is the analytic input to local smooth approximation
and Meyers--Serrin density.

## Main declaration

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

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] [SFinite mu] {Omega : Opens E}

omit [MeasurableSpace E] [BorelSpace E] in
private theorem contDiff_const_sub (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho) (x : E) :
    ContDiff ℝ ∞ fun t ↦ rho (x - t) :=
  hrho.comp (contDiff_const.sub contDiff_id)

omit [MeasurableSpace E] [NormedSpace ℝ E] [BorelSpace E] in
private theorem hasCompactSupport_const_sub (rho : E → ℝ)
    (hrho : HasCompactSupport rho) (x : E) :
    HasCompactSupport fun t ↦ rho (x - t) :=
  hrho.comp_homeomorph (Homeomorph.subLeft x)

omit [MeasurableSpace E] [NormedSpace ℝ E] [BorelSpace E] in
private theorem tsupport_const_sub_subset (rho : E → ℝ) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    tsupport (fun t ↦ rho (x - t)) ⊆ Omega := by
  intro t ht
  have ht' : x - t ∈ tsupport rho :=
    tsupport_comp_subset_preimage rho (continuous_const.sub continuous_id) ht
  exact (sub_sub_cancel x t) ▸ hx (x - t) ht'

omit [MeasurableSpace E] [BorelSpace E] in
private theorem lineDeriv_const_sub (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (x t v : E) :
    lineDeriv ℝ (fun s ↦ rho (x - s)) t v = -(fderiv ℝ rho (x - t) v) := by
  have hsub : HasFDerivAt (fun s : E ↦ x - s) (-ContinuousLinearMap.id ℝ E) t := by
    convert
      (hasFDerivAt_const (𝕜 := ℝ) (x := t) x).sub (hasFDerivAt_id (𝕜 := ℝ) t) using 1
    · ext s
      rfl
    · simp
  have hcomp := (hrho.differentiable (by simp) (x - t)).hasFDerivAt.comp t hsub
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg] using
    (hcomp.hasLineDerivAt v).lineDeriv

/-- **A weak derivative commutes with convolution by a smooth compactly supported kernel.**
If `u'` is the weak derivative of `u` in the direction `v` on `Omega`, then the
convolution has the convolved weak derivative at points whose translated kernel support
is contained in `Omega`. -/
theorem HasWeakLineDerivOn.hasLineDerivAt_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasLineDerivAt ℝ
      (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho)
      ((u' ⋆[(ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x) x v := by
  let rhoTest : 𝓓(Omega, ℝ) :=
    ⟨fun t ↦ rho (x - t), contDiff_const_sub rho hrho x,
      hasCompactSupport_const_sub rho hrho_cpt x, tsupport_const_sub_subset rho x hx⟩
  have hweak := h.integral_lineDeriv_smul_eq_neg_integral_smul rhoTest
  simp only [rhoTest, TestFunction.coe_mk] at hweak
  have hconv :
      ∫ t, fderiv ℝ rho (x - t) v • u t ∂mu =
        ∫ t, rho (x - t) • u' t ∂mu := by
    simpa only [lineDeriv_const_sub rho hrho x, neg_smul, integral_neg,
      neg_inj]
      using hweak
  convert
    (hrho_cpt.hasFDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip hu
      (hrho.of_le (by simp)) x).hasLineDerivAt v using 1
  rw [convolution_precompR_apply
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip hu
    (hrho_cpt.fderiv ℝ) (hrho.continuous_fderiv (by simp)) x v]
  simp only [convolution_def,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
  exact hconv.symm

/-- The directional derivative of a convolution with a smooth compactly supported kernel is the
convolution of the weak directional derivative with that kernel. -/
theorem HasWeakLineDerivOn.lineDeriv_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    lineDeriv ℝ
      (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x v =
      (u' ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x :=
  (h.hasLineDerivAt_convolution_right hu rho hrho hrho_cpt x hx).lineDeriv

/-- **The Fréchet derivative of a mollification is the mollification of the weak derivative.**
If `U` is a weak derivative field of `u` on `Omega`, convolution by a smooth compactly
supported scalar kernel has derivative `U` convolved with that kernel wherever the
translated kernel support lies in `Omega`. Both fields are locally integrable globally. -/
theorem HasWeakFDerivOn.hasFDerivAt_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt
      (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho)
      ((U ⋆[(ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] rho) x) x := by
  have hd := hrho_cpt.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip hu
    (hrho.of_le (by simp)) x
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  have hline := (h.hasWeakLineDerivOn v).hasLineDerivAt_convolution_right hu rho hrho hrho_cpt x hx
  have hderiv :
      ((u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip.precompR E,
        mu] fderiv ℝ rho) x) v =
        ((fun t => U t v) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x :=
    (hd.hasLineDerivAt v).unique hline
  calc
    ((u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip.precompR E,
      mu] fderiv ℝ rho) x) v =
        ((fun t => U t v) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ :
            ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x := hderiv
    _ = ((U ⋆[(ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] rho) x) v := by
      have hInt := (hrho_cpt.convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip hU hrho.continuous
            x).integrable
      simp only [convolution_def]
      rw [ContinuousLinearMap.integral_apply hInt v]
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
        smul_apply]

/-- The Fréchet derivative of a convolution with a smooth compactly supported kernel is the
convolution of the weak Fréchet derivative field with that kernel. -/
theorem HasWeakFDerivOn.fderiv_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ
      (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x =
      (U ⋆[(ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] rho) x :=
  (h.hasFDerivAt_convolution_right hu hU rho hrho hrho_cpt x hx).fderiv

end TauCeti
