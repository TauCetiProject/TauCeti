/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean coordinates for positive-definite real Clifford forms

The positive-definite real Clifford form is the squared Euclidean norm after passing between
function and Euclidean-space coordinates. Consequently, its unit quadric is identified with the
Euclidean unit sphere, and its isometries are linear isometries of `EuclideanSpace ℝ (Fin n)`
with the same determinant.

## Main definitions

* `TauCeti.realCliffordIsometryEquivEuclidean`: an isometry of `realCliffordForm n 0` as a linear
  isometry of `EuclideanSpace ℝ (Fin n)`.

## Main results

* `TauCeti.realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq` identifies the positive-definite
  real Clifford form with the squared Euclidean norm in Euclidean coordinates.
* `TauCeti.norm_euclideanSpaceEquiv_symm_eq_one_of_realCliffordForm_zero_eq_one` sends
  unit-quadric vectors to Euclidean unit vectors.
* `TauCeti.realCliffordForm_zero_euclideanSpaceEquiv_eq_one` sends Euclidean unit vectors to the
  unit quadric.
* `TauCeti.det_realCliffordIsometryEquivEuclidean`: the determinant of an isometry is the same
  in both coordinate systems.
-/

public section

namespace TauCeti

open Metric

/-- The positive-definite real Clifford form is the squared Euclidean norm in Euclidean
coordinates. -/
@[simp]
theorem realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n)) :
    realCliffordForm n 0 (EuclideanSpace.equiv (Fin n) ℝ u) = ‖u‖ ^ 2 := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one,
    QuadraticMap.weightedSumSquares_apply]
  simp only [Pi.one_apply, one_smul, PiLp.continuousLinearEquiv_apply]
  simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq u).symm

/-- A vector on the unit quadric of the positive-definite real Clifford form has Euclidean norm
one in Euclidean coordinates. -/
theorem norm_euclideanSpaceEquiv_symm_eq_one_of_realCliffordForm_zero_eq_one {n : ℕ}
    {v : Fin n → ℝ} (hv : realCliffordForm n 0 v = 1) :
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ = 1 := by
  have hsquare : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ ^ 2 = 1 := by
    rw [← realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq]
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hv
  nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin n) ℝ).symm v)]

/-- Every Euclidean unit vector lies on the unit quadric of the positive-definite real Clifford
form after passing to Euclidean coordinates. -/
theorem realCliffordForm_zero_euclideanSpaceEquiv_eq_one {n : ℕ}
    (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    realCliffordForm n 0 (EuclideanSpace.equiv (Fin n) ℝ u) = 1 := by
  rw [realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq]
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using u.property
  rw [hu, one_pow]

/-- An isometry `f` of the positive-definite form `realCliffordForm n 0` on `Fin n → ℝ`, read as
a linear isometry of `EuclideanSpace ℝ (Fin n)`: it applies `f` to coordinates. -/
noncomputable def realCliffordIsometryEquivEuclidean {n : ℕ}
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearEquiv := ((EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.trans f.toLinearEquiv).trans
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  norm_map' u := by
    have h := realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (f (EuclideanSpace.equiv (Fin n) ℝ u)))
    rw [ContinuousLinearEquiv.apply_symm_apply, f.map_app,
      realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h.symm

@[simp]
theorem realCliffordIsometryEquivEuclidean_apply {n : ℕ}
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) (v : Fin n → ℝ) :
    realCliffordIsometryEquivEuclidean f (WithLp.toLp 2 v) = WithLp.toLp 2 (f v) :=
  (rfl)

/-- The determinant of an isometry read on `EuclideanSpace ℝ (Fin n)` is its determinant on
`Fin n → ℝ`. -/
@[simp]
theorem det_realCliffordIsometryEquivEuclidean {n : ℕ}
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) :
    LinearMap.det ((realCliffordIsometryEquivEuclidean f).toLinearEquiv :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      LinearMap.det (f.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :=
  LinearMap.det_conj _ (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv

end TauCeti
