/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Plane-wave derivatives and Laplacian eigenvalues

A plane wave on a real inner product space `F` is a function `x ↦ g ⟪w, x⟫` of one linear
coordinate. Its second derivative is `g''(⟪w, x⟫) ⟪w, v⟫ ⟪w, v'⟫`, and on a finite-dimensional
space its Laplacian is `g''(⟪w, x⟫) ‖w‖²`. For `g = cos` and `g = sin` these are the Fourier modes
`cos ⟪w, x⟫` and `sin ⟪w, x⟫`, satisfying `Δ f = -‖w‖² f`. The cosine mode is an
eigenfunction of `-Δ` with eigenvalue `‖w‖²`; the sine mode is one when `w ≠ 0`.

Adapted from Giada Franz's formalization in
[`ForTauCeti/Analysis/Fourier/Torus/PlaneWave.lean`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/master/ForTauCeti/Analysis/Fourier/Torus/PlaneWave.lean).

## Main results

* `TauCeti.iteratedFDeriv_two_comp_inner`: the second derivative of a plane wave.
* `TauCeti.laplacian_cos_inner`, `TauCeti.laplacian_sin_inner`: the Laplacian identities for
  the Fourier modes, with the sine eigenfunction interpretation requiring `w ≠ 0`.
-/

public section

open InnerProductSpace
open scoped InnerProductSpace Laplacian

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The second derivative of the plane wave `x ↦ g ⟪w, x⟫` is
`g''(⟪w, x⟫) ⟪w, v⟫ ⟪w, v'⟫`. -/
theorem iteratedFDeriv_two_comp_inner {g : ℝ → ℝ} (w x : F)
    (hg : ContDiffAt ℝ 2 g ⟪w, x⟫_ℝ) (v v' : F) :
    iteratedFDeriv ℝ 2 (fun y ↦ g ⟪w, y⟫_ℝ) x ![v, v'] =
      iteratedDeriv 2 g ⟪w, x⟫_ℝ * ⟪w, v⟫_ℝ * ⟪w, v'⟫_ℝ := by
  obtain ⟨s, hs, hgs⟩ := hg.contDiffOn le_rfl (by norm_num)
  obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  have h := (innerSL ℝ w).iteratedFDerivWithin_comp_right (hgs.mono hus)
    hu.uniqueDiffOn (hu.preimage (innerSL ℝ w).continuous).uniqueDiffOn hxu (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ (hu.preimage (innerSL ℝ w).continuous) hxu] at h
  simp only [innerSL_apply_apply] at h
  rw [iteratedFDerivWithin_of_isOpen _ hu hxu] at h
  have hcomp : (fun y ↦ g ⟪w, y⟫_ℝ) = g ∘ innerSL ℝ w := by
    simp only [Function.comp_def, innerSL_apply_apply]
  rw [hcomp, h, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp only [innerSL_apply_apply, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul]
  ring

variable [FiniteDimensional ℝ F]

/-- The cosine mode `cos ⟪w, ·⟫` is an eigenfunction of `-Δ` with eigenvalue `‖w‖²`. -/
theorem laplacian_cos_inner (w x : F) :
    Δ (fun y ↦ Real.cos ⟪w, y⟫_ℝ) x = -‖w‖ ^ 2 * Real.cos ⟪w, x⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ F
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_comp_inner w x Real.contDiff_cos.contDiffAt,
    iteratedDeriv_succ, iteratedDeriv_zero, Real.deriv_cos', deriv.fun_neg', Real.deriv_sin,
    mul_assoc, ← sq, ← Finset.mul_sum, b.sum_sq_inner_left]
  ring

/-- The sine mode satisfies `Δ (sin ⟪w, ·⟫) = -‖w‖² sin ⟪w, ·⟫`. When `w ≠ 0`, it is
an eigenfunction of `-Δ` with eigenvalue `‖w‖²`. -/
theorem laplacian_sin_inner (w x : F) :
    Δ (fun y ↦ Real.sin ⟪w, y⟫_ℝ) x = -‖w‖ ^ 2 * Real.sin ⟪w, x⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ F
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_comp_inner w x Real.contDiff_sin.contDiffAt,
    iteratedDeriv_succ, iteratedDeriv_zero, Real.deriv_sin, Real.deriv_cos',
    mul_assoc, ← sq, ← Finset.mul_sum, b.sum_sq_inner_left]
  ring

end TauCeti
