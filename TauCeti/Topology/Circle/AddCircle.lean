/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The additive circle and the complex unit circle

For a nonzero real period `T`, Mathlib's `AddCircle.homeomorphCircle` identifies `AddCircle T`
with the complex unit circle `Circle`. This file records where that identification sends the
distinguished points: `0 : AddCircle T` is the point `1 : Circle`, so the inverse homeomorphism
carries `1` back to `0`; more generally it carries `exp (2πix / T)` back to the class of `x`.
Applied to both factors, it identifies the torus `S¹ × S¹` with the standard torus
`UnitAddTorus (Fin 2) = ℝ² / ℤ²`.

## Main definitions

* `TauCeti.circleProdHomeomorphUnitAddTorus` — the homeomorphism `S¹ × S¹ ≃ₜ ℝ² / ℤ²`.

## Main results

* `AddCircle.homeomorphCircle_symm_one` — the inverse circle homeomorphism sends `1` to `0` for
  every nonzero real period.
* `AddCircle.homeomorphCircle_symm_exp` — it sends `exp (2πix / T)` to the class of `x`.
* `TauCeti.circleProdHomeomorphUnitAddTorus_apply`,
  `TauCeti.circleProdHomeomorphUnitAddTorus_symm_apply` — the torus homeomorphism and its inverse
  act factorwise through `AddCircle.homeomorphCircle`.
* `TauCeti.circleProdHomeomorphUnitAddTorus_exp` — the torus homeomorphism sends
  `(exp (2πia), exp (2πib))` to the class of `(a, b)`.
-/

public section

namespace AddCircle

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `1 : Circle` to `0`. -/
@[simp]
theorem homeomorphCircle_symm_one {T : ℝ} (hT : T ≠ 0) :
    (AddCircle.homeomorphCircle hT).symm 1 = 0 := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero]

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `exp (2πix / T)` to the
class of `x`. -/
@[simp]
theorem homeomorphCircle_symm_exp {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    (AddCircle.homeomorphCircle hT).symm (Circle.exp (2 * Real.pi / T * x)) = x := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]

end AddCircle

namespace TauCeti

/-- The torus `S¹ × S¹` is homeomorphic to the standard torus `UnitAddTorus (Fin 2) = ℝ² / ℤ²`,
each circle factor being identified with `ℝ / ℤ` by `AddCircle.homeomorphCircle`. -/
noncomputable def circleProdHomeomorphUnitAddTorus : Circle × Circle ≃ₜ UnitAddTorus (Fin 2) :=
  ((AddCircle.homeomorphCircle one_ne_zero).symm.prodCongr
    (AddCircle.homeomorphCircle one_ne_zero).symm).trans Homeomorph.finTwoArrow.symm

/-- The identification of `S¹ × S¹` with `ℝ² / ℤ²` reads each circle factor through
`AddCircle.homeomorphCircle.symm`. -/
@[simp]
theorem circleProdHomeomorphUnitAddTorus_apply (z : Circle × Circle) :
    circleProdHomeomorphUnitAddTorus z =
      ![(AddCircle.homeomorphCircle one_ne_zero).symm z.1,
        (AddCircle.homeomorphCircle one_ne_zero).symm z.2] := by
  ext i
  fin_cases i <;> rfl

/-- The inverse identification of `ℝ² / ℤ²` with `S¹ × S¹` sends the coordinates of a point to the
circle by `AddCircle.toCircle`. -/
@[simp]
theorem circleProdHomeomorphUnitAddTorus_symm_apply (x : UnitAddTorus (Fin 2)) :
    circleProdHomeomorphUnitAddTorus.symm x =
      (AddCircle.toCircle (x 0), AddCircle.toCircle (x 1)) := by
  simp [circleProdHomeomorphUnitAddTorus, AddCircle.homeomorphCircle_apply]

/-- The identification of `S¹ × S¹` with `ℝ² / ℤ²` sends `(exp (2πia), exp (2πib))` to the class
of `(a, b)`. -/
theorem circleProdHomeomorphUnitAddTorus_exp (a b : ℝ) :
    circleProdHomeomorphUnitAddTorus
        (Circle.exp (2 * Real.pi * a), Circle.exp (2 * Real.pi * b)) =
      ![(a : UnitAddCircle), (b : UnitAddCircle)] := by
  have h (x : ℝ) : (AddCircle.homeomorphCircle one_ne_zero).symm (Circle.exp (2 * Real.pi * x)) =
      (x : UnitAddCircle) := by
    simpa using AddCircle.homeomorphCircle_symm_exp one_ne_zero x
  ext i
  fin_cases i <;> simp [circleProdHomeomorphUnitAddTorus, h]

end TauCeti
