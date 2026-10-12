/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Bilinear pairings of two directional derivatives of a compactly supported map

For a compactly supported `C²` map `u` on a finite-dimensional real space and a continuous
bilinear map `B`, the integral of `B (∂_v u) (∂_w u)` against a Haar measure does not change when
the two directions are exchanged. Integrating by parts in the direction `w` turns it into
`-∫ B (∂_w ∂_v u) u`, and the exchanged integral into `-∫ B (∂_v ∂_w u) u`; the two agree because
the second derivative is symmetric.

Consequently the integral vanishes whenever `B` is alternating. That is the vanishing of the
integral over the whole space of the pullback of a constant two-form along a compactly supported
map — the "null Lagrangian" phenomenon: for a map from the plane to the plane, with `B` the
standard area form and the two coordinate directions, the integrand is the Jacobian determinant.
It is what makes the energy of a compactly supported map into a symplectic vector space equal the
square of the `L²` norm of its Cauchy--Riemann defect.

## Main results

* `TauCeti.integral_bilinear_fderiv_apply_comm`: the integral of `B (∂_v u) (∂_w u)` is symmetric
  in the two directions, and `TauCeti.integral_bilinForm_fderiv_apply_comm` its form for a
  bilinear form on a finite-dimensional space.
* `TauCeti.integral_bilinForm_fderiv_apply_eq_zero_of_isAlt`: for an alternating bilinear form
  the integral vanishes.

## References

* Sébastien Gouëzel, `Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`, theorem
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`: the integration by parts in a single
  direction that every proof here is built on.
-/

public section

namespace TauCeti

open MeasureTheory

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → V}

/-- Exchanging the two differentiation directions does not change the integral of a continuous
bilinear pairing of two directional derivatives of a compactly supported `C²` map. -/
theorem integral_bilinear_fderiv_apply_comm (B : V →L[ℝ] V →L[ℝ] W) (hu : ContDiff ℝ 2 u)
    (hsupp : HasCompactSupport u) (v w : E) :
    ∫ x, B (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ =
      ∫ x, B (fderiv ℝ u x w) (fderiv ℝ u x v) ∂μ := by
  have hu' : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hcdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hcd2u : Continuous (fderiv ℝ (fderiv ℝ u)) := hu'.continuous_fderiv (by norm_num)
  -- a bilinear pairing whose right factor has compact support has compact support
  have hcs : ∀ F G : E → V, HasCompactSupport G → HasCompactSupport fun x ↦ B (F x) (G x) :=
    fun F G hG ↦ hG.mono fun x hx ↦ by
      simp only [Function.mem_support] at hx ⊢
      contrapose! hx
      simp [hx]
  -- the derivative in the direction `w` of the derivative of `u` in the direction `v`
  have hsnd : ∀ (v w : E) (x : E),
      fderiv ℝ (fun y ↦ fderiv ℝ u y v) x w = fderiv ℝ (fderiv ℝ u) x w v := by
    intro v w x
    rw [fderiv_clm_apply (hu'.differentiable (by norm_num) x) (differentiableAt_const v)]
    simp
  -- integration by parts in the direction `w`, for each ordered pair of directions
  have step : ∀ v w : E, ∫ x, B (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ =
      -∫ x, B (fderiv ℝ (fderiv ℝ u) x w v) (u x) ∂μ := by
    intro v w
    have hcv : Continuous fun x ↦ fderiv ℝ u x v := hcdu.clm_apply continuous_const
    have h1 : Integrable
        (fun x ↦ B (fderiv ℝ (fun y ↦ fderiv ℝ u y v) x w) (u x)) μ := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hcs _ _ hsupp)
      simp only [hsnd v w]
      exact (B.continuous.comp ((hcd2u.clm_apply continuous_const).clm_apply
        continuous_const)).clm_apply hu.continuous
    have h2 : Integrable (fun x ↦ B (fderiv ℝ u x v) (fderiv ℝ u x w)) μ :=
      Continuous.integrable_of_hasCompactSupport
        ((B.continuous.comp hcv).clm_apply (hcdu.clm_apply continuous_const))
        (hcs _ _ (hsupp.fderiv_apply (𝕜 := ℝ) w))
    have h3 : Integrable (fun x ↦ B (fderiv ℝ u x v) (u x)) μ :=
      Continuous.integrable_of_hasCompactSupport
        ((B.continuous.comp hcv).clm_apply hu.continuous) (hcs _ _ hsupp)
    have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := μ) (B := B)
      (f := fun x ↦ fderiv ℝ u x v) (g := u) (v := w) h1 h2 h3
      (fun x _ ↦ ((hu'.differentiable (by norm_num) x).clm_apply
        (differentiableAt_const v)))
      (fun x _ ↦ hu.differentiable (by norm_num) x)
    simpa only [hsnd v w] using this
  have hsymm : ∀ x : E, fderiv ℝ (fderiv ℝ u) x w v = fderiv ℝ (fderiv ℝ u) x v w :=
    fun x ↦ (hu.contDiffAt.isSymmSndFDerivAt (by simp)).eq w v
  rw [step v w, step w v]
  simp only [hsymm]

variable [FiniteDimensional ℝ V]

/-- Exchanging the two differentiation directions does not change the integral of a bilinear form
evaluated on two directional derivatives of a compactly supported `C²` map into a
finite-dimensional space. -/
theorem integral_bilinForm_fderiv_apply_comm (b : LinearMap.BilinForm ℝ V) (hu : ContDiff ℝ 2 u)
    (hsupp : HasCompactSupport u) (v w : E) :
    ∫ x, b (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ =
      ∫ x, b (fderiv ℝ u x w) (fderiv ℝ u x v) ∂μ := by
  simpa using integral_bilinear_fderiv_apply_comm b.toContinuousBilinearMap hu hsupp v w

/-- The integral of an alternating bilinear form evaluated on two directional derivatives of a
compactly supported `C²` map vanishes: the pullback of a constant two-form along a compactly
supported map integrates to zero. -/
theorem integral_bilinForm_fderiv_apply_eq_zero_of_isAlt {b : LinearMap.BilinForm ℝ V}
    (hb : b.IsAlt) (hu : ContDiff ℝ 2 u) (hsupp : HasCompactSupport u) (v w : E) :
    ∫ x, b (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ = 0 := by
  have hneg : ∀ x : E, b (fderiv ℝ u x w) (fderiv ℝ u x v) =
      -b (fderiv ℝ u x v) (fderiv ℝ u x w) := fun x ↦ (hb.neg _ _).symm
  have h := integral_bilinForm_fderiv_apply_comm (μ := μ) b hu hsupp v w
  simp only [hneg, integral_neg] at h
  linarith

end TauCeti

end
