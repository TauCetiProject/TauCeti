/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Second derivatives of plane waves

A plane wave on a real inner product space `F` is a function `x ↦ g ⟪w, x⟫` of one linear
coordinate. Its second derivative is `g''(⟪w, x⟫) ⟪w, v⟫ ⟪w, v'⟫`, and on a finite-dimensional
space its Laplacian is `g''(⟪w, x⟫) ‖w‖²`. For `g = cos` and `g = sin` these are the Fourier modes
`cos ⟪w, x⟫` and `sin ⟪w, x⟫`, eigenfunctions of `-Δ` with eigenvalue `‖w‖²`.

## Main results

* `TauCeti.iteratedFDeriv_two_comp_inner`: the second derivative of a plane wave.
* `TauCeti.laplacian_comp_inner`: `Δ (g ⟪w, ·⟫) = g''(⟪w, ·⟫) ‖w‖²`.
* `TauCeti.laplacian_cos_inner`, `TauCeti.laplacian_sin_inner`: the Fourier modes are
  eigenfunctions of the Laplacian.
-/

public section

open InnerProductSpace
open scoped InnerProductSpace Laplacian

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The second derivative of the plane wave `x ↦ g ⟪w, x⟫` is
`g''(⟪w, x⟫) ⟪w, v⟫ ⟪w, v'⟫`. -/
theorem iteratedFDeriv_two_comp_inner {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (w x v v' : F) :
    iteratedFDeriv ℝ 2 (fun y ↦ g ⟪w, y⟫_ℝ) x ![v, v'] =
      iteratedDeriv 2 g ⟪w, x⟫_ℝ * ⟪w, v⟫_ℝ * ⟪w, v'⟫_ℝ := by
  have h := (innerSL ℝ w).iteratedFDeriv_comp_right hg x (i := 2) le_rfl
  change iteratedFDeriv ℝ 2 (g ∘ innerSL ℝ w) x ![v, v'] = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp only [innerSL_apply_apply, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul]
  ring

variable [FiniteDimensional ℝ F]

/-- **The Laplacian of a plane wave**: `Δ (g ⟪w, ·⟫) = g''(⟪w, ·⟫) ‖w‖²`. -/
theorem laplacian_comp_inner {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (w x : F) :
    Δ (fun y ↦ g ⟪w, y⟫_ℝ) x = iteratedDeriv 2 g ⟪w, x⟫_ℝ * ‖w‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ F
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_comp_inner hg, mul_assoc, ← Finset.mul_sum]
  congr 1
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner w w]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm (b i) w]

/-- The cosine mode `cos ⟪w, ·⟫` is an eigenfunction of `-Δ` with eigenvalue `‖w‖²`. -/
theorem laplacian_cos_inner (w x : F) :
    Δ (fun y ↦ Real.cos ⟪w, y⟫_ℝ) x = -‖w‖ ^ 2 * Real.cos ⟪w, x⟫_ℝ := by
  rw [laplacian_comp_inner (Real.contDiff_cos (n := 2)), iteratedDeriv_succ, iteratedDeriv_one,
    Real.deriv_cos', deriv.fun_neg', Real.deriv_sin]
  ring

/-- The sine mode `sin ⟪w, ·⟫` is an eigenfunction of `-Δ` with eigenvalue `‖w‖²`. -/
theorem laplacian_sin_inner (w x : F) :
    Δ (fun y ↦ Real.sin ⟪w, y⟫_ℝ) x = -‖w‖ ^ 2 * Real.sin ⟪w, x⟫_ℝ := by
  rw [laplacian_comp_inner (Real.contDiff_sin (n := 2)), iteratedDeriv_succ, iteratedDeriv_one,
    Real.deriv_sin, Real.deriv_cos']
  ring

end TauCeti
