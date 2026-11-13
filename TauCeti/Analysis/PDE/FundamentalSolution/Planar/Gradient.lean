/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Gradient of the planar Newtonian kernel

The full Fréchet derivative of the planar Newtonian kernel away from its pole, the covector

`-(2π ‖z‖²)⁻¹ ⟪z, ·⟫`,

and its translates (`TauCeti.hasFDerivAt_planarNewtonianKernel`,
`TauCeti.fderiv_planarNewtonianKernel_apply`, `TauCeti.hasFDerivAt_planarNewtonianKernel_sub`,
`TauCeti.fderiv_planarNewtonianKernel_sub_apply`) are in
`TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic`, where the Laplacian at the pole needs them.
This file adds the operator norm `(2π ‖z‖)⁻¹` of the gradient and the derivative along an affine
curve. These inverse-distance estimates are the pointwise kernel input for forming and
differentiating planar Newtonian potentials.

The calculation uses Mathlib's derivative of the squared norm and the Fréchet chain rule for the
real logarithm.  It complements `FundamentalSolution.Planar.Flux`, which computes only the
derivative in the radial direction needed for the circle flux.

The normalization and inverse-distance gradient formula follow Evans, *Partial Differential
Equations*, Section 2.2.

## Main declarations

* `TauCeti.hasDerivAt_planarNewtonianKernel_affine`: the derivative along an affine real curve.
* `TauCeti.norm_fderiv_planarNewtonianKernel`: the inverse-distance operator norm of the gradient.
* `TauCeti.norm_fderiv_planarNewtonianKernel_sub`: the same for a kernel with pole `a`.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace

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
