/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Gradient of the planar Newtonian kernel

This file computes the full Fréchet derivative of the planar Newtonian kernel away from its
pole.  The result is the covector

`-(2π ‖z‖²)⁻¹ ⟪z, ·⟫`,

whose operator norm is `(2π ‖z‖)⁻¹`.  Translated versions give the corresponding formulas for a
pole at an arbitrary point.  These inverse-distance estimates are the pointwise kernel input for
forming and differentiating planar Newtonian potentials.

The calculation uses Mathlib's derivative of the squared norm and the Fréchet chain rule for the
real logarithm.  It complements `FundamentalSolution.Planar.Flux`, which computes only the
derivative in the radial direction needed for the circle flux.

The normalization and inverse-distance gradient formula follow Evans, *Partial Differential
Equations*, Section 2.2.

## Main declarations

* `TauCeti.hasFDerivAt_planarNewtonianKernel`: the full derivative at a nonzero point.
* `TauCeti.fderiv_planarNewtonianKernel_apply`: its value in an arbitrary direction.
* `TauCeti.norm_fderiv_planarNewtonianKernel`: its inverse-distance operator norm.
* `TauCeti.hasFDerivAt_planarNewtonianKernel_sub`: the translated full derivative.
* `TauCeti.fderiv_planarNewtonianKernel_sub_apply`: the corresponding translated formula.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace
open scoped Topology

/-- Away from the origin, the planar Newtonian kernel has derivative
`-(2π)⁻¹ ‖z‖⁻² ⟪z, ·⟫`. -/
theorem hasFDerivAt_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt planarNewtonianKernel
      ((-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z) z := by
  have hsq :
      HasFDerivAt (fun w : ℂ ↦ ‖w‖ ^ 2) (2 • innerSL ℝ z) z := by
    simpa only [id_eq, one_apply_eq_self, one_smul, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id z).norm_sq
  have hlog :
      HasFDerivAt (fun w : ℂ ↦ Real.log (‖w‖ ^ 2))
        ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    hsq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  have heq :
      planarNewtonianKernel =
        fun w : ℂ ↦ (-(2 * Real.pi)⁻¹ / 2) * Real.log (‖w‖ ^ 2) := by
    funext w
    rw [planarNewtonianKernel_def, Real.log_pow]
    ring
  have hmap :
      ((-(2 * Real.pi)⁻¹ / 2) • ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z))) =
        ((-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z) := by
    ext v
    simp only [smul_apply, innerSL_apply_apply]
    ring
  rw [heq, ← hmap]
  exact hlog.const_mul (-(2 * Real.pi)⁻¹ / 2)

/-- The derivative of the planar Newtonian kernel along an affine real curve away from the
origin. -/
theorem hasDerivAt_planarNewtonianKernel_affine (b v : ℂ) {t : ℝ}
    (h : b + t • v ≠ 0) :
    HasDerivAt (fun s : ℝ => planarNewtonianKernel (b + s • v))
      ((-(2 * Real.pi)⁻¹ * (‖b + t • v‖ ^ 2)⁻¹) * ⟪b + t • v, v⟫_ℝ) t := by
  have hf := hasFDerivAt_planarNewtonianKernel h
  have hcurve : HasDerivAt (fun s : ℝ => b + s • v) v t :=
    by simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add b
  simpa only [Function.comp_def, smul_apply, smul_eq_mul,
    innerSL_apply_apply] using hf.comp_hasDerivAt t hcurve

/-- The planar Newtonian kernel is not differentiable at its pole: it is unbounded there, but
takes the value `0` at the origin. -/
theorem not_differentiableAt_planarNewtonianKernel_zero :
    ¬DifferentiableAt ℝ planarNewtonianKernel 0 := by
  intro h
  have hc : Filter.Tendsto planarNewtonianKernel (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa using h.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hlog : Filter.Tendsto (fun z : ℂ ↦ Real.log ‖z‖) (𝓝[≠] 0) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero
  have hatTop : Filter.Tendsto planarNewtonianKernel (𝓝[≠] (0 : ℂ)) Filter.atTop := by
    rw [funext planarNewtonianKernel_def]
    exact hlog.const_mul_atBot_of_neg (by simpa using Real.pi_pos)
  exact not_tendsto_nhds_of_tendsto_atTop hatTop _ hc

/-- The Fréchet derivative of the planar Newtonian kernel as a continuous linear functional.
At the pole, where the kernel is not differentiable, both sides are `0`. -/
theorem fderiv_planarNewtonianKernel (z : ℂ) :
    fderiv ℝ planarNewtonianKernel z =
      (-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [fderiv_zero_of_not_differentiableAt not_differentiableAt_planarNewtonianKernel_zero]
    simp
  · exact (hasFDerivAt_planarNewtonianKernel hz).fderiv

/-- The evaluation of `fderiv` of the planar Newtonian kernel in the direction `v` is the radial
inner product `⟪z, v⟫` scaled by `-(2π ‖z‖²)⁻¹`. Away from the pole this is the directional
derivative; at the pole, where the kernel is not differentiable, `fderiv` takes the default
value `0` and both sides are `0` (it is not an actual directional derivative). -/
theorem fderiv_planarNewtonianKernel_apply (z v : ℂ) :
    fderiv ℝ planarNewtonianKernel z v =
      (-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) * ⟪z, v⟫_ℝ := by
  rw [fderiv_planarNewtonianKernel]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- The operator norm of `fderiv` of the planar Newtonian kernel is the inverse distance (at the
pole `fderiv` is the default `0`). -/
@[simp]
theorem norm_fderiv_planarNewtonianKernel (z : ℂ) :
    ‖fderiv ℝ planarNewtonianKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [fderiv_planarNewtonianKernel]
  rw [fderiv_planarNewtonianKernel, norm_smul, innerSL_apply_norm]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_mul, abs_of_pos (by positivity),
    abs_of_pos hpi, abs_inv, abs_pow, abs_of_pos hn]
  field_simp

/-- A planar Newtonian kernel with pole at `a` has the translated Fréchet derivative. -/
theorem hasFDerivAt_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    HasFDerivAt (fun w : ℂ ↦ planarNewtonianKernel (w - a))
      ((-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a)) z := by
  rw [hasFDerivAt_comp_sub]
  exact hasFDerivAt_planarNewtonianKernel (sub_ne_zero.mpr hza)

/-- The formula for `fderiv` of a planar Newtonian kernel with pole at `a`; at the pole it is the
default value `0`, not an actual derivative. -/
theorem fderiv_planarNewtonianKernel_sub (z a : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z =
      (-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a) := by
  rw [fderiv_comp_sub]
  exact fderiv_planarNewtonianKernel (z - a)

/-- The evaluation of `fderiv` of a planar Newtonian kernel with pole at `a` in the direction `v`.
Away from `a` this is the directional derivative; at the pole `fderiv` takes the default value
`0` and both sides are `0` (it is not an actual directional derivative). -/
theorem fderiv_planarNewtonianKernel_sub_apply (z a v : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z v =
      (-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) * ⟪z - a, v⟫_ℝ := by
  rw [fderiv_planarNewtonianKernel_sub]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- The operator norm of `fderiv` of a planar Newtonian kernel with pole at `a` is the inverse
distance (at the pole `fderiv` is the default `0`). -/
@[simp]
theorem norm_fderiv_planarNewtonianKernel_sub (z a : ℂ) :
    ‖fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z‖ =
      (2 * Real.pi * ‖z - a‖)⁻¹ := by
  rw [fderiv_comp_sub]
  exact norm_fderiv_planarNewtonianKernel (z - a)

end TauCeti

end
