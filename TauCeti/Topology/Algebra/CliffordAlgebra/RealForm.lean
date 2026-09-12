/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean coordinates for positive-definite real Clifford forms

The positive-definite real Clifford form is the squared Euclidean norm after passing between
function and Euclidean-space coordinates. Consequently, its unit quadric is identified with the
Euclidean unit sphere.

## Main results

* `TauCeti.realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq` identifies the positive-definite
  real Clifford form with the squared Euclidean norm in Euclidean coordinates.
* `TauCeti.norm_euclideanSpaceEquiv_symm_eq_one_of_realCliffordForm_zero_eq_one` sends
  unit-quadric vectors to Euclidean unit vectors.
* `TauCeti.realCliffordForm_zero_euclideanSpaceEquiv_eq_one` sends Euclidean unit vectors to the
  unit quadric.
-/

public section

namespace TauCeti

open Metric

/-- The positive-definite real Clifford form is the squared Euclidean norm in Euclidean
coordinates. -/
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
    simpa only [mem_sphere, dist_zero_right] using u.2
  rw [hu, one_pow]

end TauCeti
