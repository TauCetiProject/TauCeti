/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Basic

/-!
# Smooth winding reference fields on the plane

The affine Sobolev space of framed degree-`m` vortex fields is centered at a smooth pair
which equals `(-i m dθ, exp(i m θ))` outside a disc. Here `referenceConnection` and
`referenceSection` construct such a pair using a radial cutoff. Connections are actual
complex-valued real continuous-linear one-forms; their values are purely imaginary.
The cutoff removes the angular singularity on a neighborhood of the origin.

The end formulas, rotation laws and compact support of changes of cutoff are proved
explicitly. The latter allows different references to define the same affine Sobolev
space. These reference pairs are not asserted to solve the vortex equations.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric
open scoped ContDiff Topology

private def cutoff (f : ContDiffBump (0 : ℝ)) (z : ℂ) : ℝ :=
  1 - f (‖z‖ ^ 2)

private theorem contDiff_cutoff (f : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (cutoff f) :=
  contDiff_const.sub (f.contDiff.comp (contDiff_norm_sq ℂ))

private theorem cutoff_eq_zero (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ f.rIn) : cutoff f z = 0 := by
  simp [cutoff, f.one_of_mem_closedBall (x := ‖z‖ ^ 2)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg] using hz)]

private theorem cutoff_eq_one (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) : cutoff f z = 1 := by
  simp [cutoff, f.zero_of_le_dist (x := ‖z‖ ^ 2)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg] using hz)]

private theorem cutoff_eventuallyEq_zero (f : ContDiffBump (0 : ℝ)) :
    cutoff f =ᶠ[𝓝 0] 0 := by
  have h := f.eventuallyEq_one.comp_tendsto
    (by simpa using (continuous_norm.pow 2).tendsto (0 : ℂ))
  filter_upwards [h] with z hz
  simp only [Function.comp_apply, Pi.one_apply, Pi.pow_apply] at hz
  simp [cutoff, hz]

/-- A globally smooth section equal to the winding phase `(z / ‖z‖)^m` outside a disc.
The bump is applied to the squared radius, so the construction is rotation-equivariant. -/
def referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) : ℂ :=
  (cutoff f z : ℂ) * (z / (‖z‖ : ℂ)) ^ m

/-- A globally smooth imaginary connection one-form equal to `-i m dθ` outside a disc,
where `dθ_z(v) = Im(v / z)`. -/
def referenceConnection (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (-(m : ℂ) * I * (cutoff f z : ℂ)) •
    ((ofRealCLM.comp imCLM).comp (ContinuousLinearMap.mul ℝ ℂ z⁻¹))

/-- Evaluation of the reference section in the fixed complex coordinate. -/
@[simp]
theorem referenceSection_apply (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) :
    referenceSection f m z = (1 - f (‖z‖ ^ 2) : ℝ) * (z / (‖z‖ : ℂ)) ^ m := by
  simp [referenceSection, cutoff]

/-- Evaluation of the reference connection on a real tangent vector. -/
@[simp]
theorem referenceConnection_apply (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z v : ℂ) :
    referenceConnection f m z v =
      -(m : ℂ) * I * (1 - f (‖z‖ ^ 2) : ℝ) * ((v / z).im : ℂ) := by
  simp [referenceConnection, cutoff, div_eq_mul_inv, mul_comm]

/-- The reference section vanishes on the inner disc. -/
theorem referenceSection_eq_zero (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ f.rIn) : referenceSection f m z = 0 := by
  simp [referenceSection, cutoff_eq_zero f hz]

/-- The connection vanishes on the inner disc, removing the angular singularity. -/
theorem referenceConnection_eq_zero (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ f.rIn) : referenceConnection f m z = 0 := by
  simp [referenceConnection, cutoff_eq_zero f hz]

/-- The reference section has the exact prescribed winding tail. -/
theorem referenceSection_eq_phase (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) : referenceSection f m z = (z / (‖z‖ : ℂ)) ^ m := by
  simp [referenceSection, cutoff_eq_one f hz]

/-- The reference connection has the exact angular tail `-i m dθ`. -/
theorem referenceConnection_eq_angular (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) (v : ℂ) :
    referenceConnection f m z v = -(m : ℂ) * I * ((v / z).im : ℂ) := by
  simp [referenceConnection, cutoff_eq_one f hz, div_eq_mul_inv, mul_comm]

/-- The section is smooth even at the origin. -/
theorem contDiff_referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (referenceSection f m) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [cutoff_eventuallyEq_zero f] with z hz
    simp [referenceSection, hz]
  · have hn : ContDiffAt ℝ ∞ (fun w : ℂ ↦ (‖w‖ : ℂ)) z :=
      ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℂ hz)
    have hp : ContDiffAt ℝ ∞ (fun w : ℂ ↦ w / (‖w‖ : ℂ)) z := by
      simpa only [div_eq_mul_inv, Pi.inv_apply, id_eq] using
        contDiffAt_id.mul (hn.inv (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)))
    exact (ofRealCLM.contDiff.comp (contDiff_cutoff f)).contDiffAt.mul (hp.pow m)

/-- The connection is a smooth map into the space of one-forms, including at the origin. -/
theorem contDiff_referenceConnection (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (referenceConnection f m) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const (c := (0 : ℂ →L[ℝ] ℂ))).congr_of_eventuallyEq
    filter_upwards [cutoff_eventuallyEq_zero f] with z hz
    simp [referenceConnection, hz]
  · exact (contDiffAt_const.mul (ofRealCLM.contDiff.comp
        (contDiff_cutoff f)).contDiffAt).smul
      (contDiffAt_const.clm_comp ((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp z
        (contDiffAt_id.inv hz)))

/-- The exact winding tail has unit norm. -/
theorem norm_referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) : ‖referenceSection f m z‖ = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
    linarith [f.rOut_pos]
  rw [referenceSection_eq_phase f m hz, norm_pow, norm_div]
  simp [norm_ne_zero_iff.2 hz0]

/-- Rotation of the coordinate multiplies the reference section by the degree-`m` phase. -/
theorem referenceSection_mul (f : ContDiffBump (0 : ℝ)) (m : ℕ) {u : ℂ}
    (hu : ‖u‖ = 1) (z : ℂ) :
    referenceSection f m (u * z) = u ^ m * referenceSection f m z := by
  simp only [referenceSection, cutoff, norm_mul, hu, one_mul]
  rw [mul_div_assoc, mul_pow]
  ring

/-- The reference connection is invariant under simultaneous rotation of point and vector. -/
theorem referenceConnection_mul (f : ContDiffBump (0 : ℝ)) (m : ℕ) {u : ℂ}
    (hu : ‖u‖ = 1) (z v : ℂ) :
    referenceConnection f m (u * z) (u * v) = referenceConnection f m z v := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  simp [referenceConnection_apply, hu, mul_div_mul_left _ _ hu0]

private theorem hasCompactSupport_cutoff_sub (f g : ContDiffBump (0 : ℝ)) :
    HasCompactSupport (cutoff f - cutoff g) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (max f.rOut g.rOut + 1))
  intro z hz
  have hnorm : max f.rOut g.rOut + 1 < ‖z‖ := by simpa using hz
  have hf : f.rOut ≤ ‖z‖ ^ 2 := by nlinarith [le_max_left f.rOut g.rOut, f.rOut_pos]
  have hg : g.rOut ≤ ‖z‖ ^ 2 := by nlinarith [le_max_right f.rOut g.rOut, g.rOut_pos]
  simp [cutoff_eq_one f hf, cutoff_eq_one g hg]

/-- Changing the radial cutoff changes the section by a compactly supported smooth field. -/
theorem hasCompactSupport_referenceSection_sub (f g : ContDiffBump (0 : ℝ)) (m : ℕ) :
    HasCompactSupport (referenceSection f m - referenceSection g m) := by
  apply (hasCompactSupport_cutoff_sub f g).mono
  intro z hz
  simp only [Function.mem_support, Pi.sub_apply, ne_eq, sub_eq_zero] at *
  exact fun h ↦ hz (by simp [referenceSection, h])

/-- Changing the radial cutoff changes the connection by a compactly supported smooth one-form. -/
theorem hasCompactSupport_referenceConnection_sub (f g : ContDiffBump (0 : ℝ)) (m : ℕ) :
    HasCompactSupport (referenceConnection f m - referenceConnection g m) := by
  apply (hasCompactSupport_cutoff_sub f g).mono
  intro z hz
  simp only [Function.mem_support, Pi.sub_apply, ne_eq, sub_eq_zero] at *
  exact fun h ↦ hz (by simp [referenceConnection, h])

end TauCeti.Vortex
