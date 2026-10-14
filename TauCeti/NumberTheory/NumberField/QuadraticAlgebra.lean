/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Quadratic algebras as number fields

A rational quadratic algebra whose defining polynomial has no rational root is a number field.
The nonsquare hypothesis for an integer parameter transfers to its rational cast.
-/

public section

namespace Rat

/-- A nonsquare integer remains nonsquare in the rationals. -/
instance instFactNotIsSquareIntCast (D : ℤ) [Fact (¬ IsSquare D)] :
    Fact (¬ IsSquare (D : ℚ)) := ⟨Rat.isSquare_intCast_iff.not.mpr Fact.out⟩

end Rat

namespace QuadraticAlgebra

/-- A rational quadratic algebra with no rational root is a number field. -/
instance instNumberField {a b : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    NumberField (QuadraticAlgebra ℚ a b) := NumberField.of_module_finite ℚ _

end QuadraticAlgebra
