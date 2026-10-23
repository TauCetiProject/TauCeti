/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import Mathlib.Algebra.Group.Even

/-!
# Diagonal forms with coefficients in the same square classes

Rescaling each coordinate by a unit identifies diagonal quadratic forms whose corresponding
coefficients differ by squares. This is the form-level comparison used when choosing
coefficients by approximation in local square classes. The comparison uses Mathlib's
`QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares`.
-/

public section

open QuadraticMap

namespace TauCeti

/-- Two diagonal forms with unit weights are isometric if corresponding weights differ by
squares. -/
theorem equivalent_weightedSumSquares_of_isSquare_div
    {R ι : Type*} [CommSemiring R] [Fintype ι] {w v : ι → Rˣ}
    (h : ∀ i, IsSquare (w i / v i)) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R v) := by
  classical
  choose c hc using h
  rw [QuadraticMap.weightedSumSquares_units, QuadraticMap.weightedSumSquares_units]
  refine ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares c (fun i => ?_)⟩
  have hi : v i * c i ^ 2 = w i := by
    simp only [← pow_two] at hc
    rw [← hc i]
    simp
  exact congrArg Units.val hi

end TauCeti
