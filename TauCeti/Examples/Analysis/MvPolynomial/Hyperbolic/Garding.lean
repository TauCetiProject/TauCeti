/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
public import TauCeti.Examples.Analysis.MvPolynomial.Hyperbolic

/-!
# Checks for Gårding's theorem on the directions of hyperbolicity

* `xy` on `ℝ²` is hyperbolic in the direction `(1, 2)`, a point of its cone `Γ(xy, (1, 1))`, and
  its cone in that direction is again the open quadrant.
* The open quadrant, the cone of `xy`, is convex.
-/

public section

open MvPolynomial Set

namespace TauCeti.HyperbolicExamples

/-- `(1, 2)` lies in the Gårding cone of `xy` in the direction `(1, 1)`. -/
theorem one_two_mem_gardingCone_X_mul_X :
    ![(1 : ℝ), 2] ∈ gardingCone (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) 1 := by
  rw [gardingCone_X_mul_X]
  simp

/-- `xy` is hyperbolic of degree `2` in the direction `(1, 2)`. -/
example : IsHyperbolic (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) 2 ![1, 2] :=
  isHyperbolic_X_mul_X.of_mem_gardingCone one_two_mem_gardingCone_X_mul_X

/-- The Gårding cone of `xy` in the direction `(1, 2)` is the open quadrant. -/
example : gardingCone (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) ![1, 2] = {x | 0 < x 0 ∧ 0 < x 1} := by
  rw [isHyperbolic_X_mul_X.gardingCone_eq_of_mem one_two_mem_gardingCone_X_mul_X,
    gardingCone_X_mul_X]

/-- The open quadrant, the Gårding cone of `xy`, is convex. -/
example : Convex ℝ {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 < x 1} :=
  gardingCone_X_mul_X ▸ isHyperbolic_X_mul_X.convex_gardingCone

end TauCeti.HyperbolicExamples
