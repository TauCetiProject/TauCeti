/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import TauCeti.Algebra.QuadraticAlgebra.Square
public import TauCeti.Algebra.Ring.Semireal
import TauCeti.Algebra.Order.Ring.Ordering.Semireal

/-! # Square roots in the complexification of a real closed field

`QuadraticAlgebra.isSquare` specializes the algebraic square-root construction to a real
closed field, without requiring an order on that field as a hypothesis. This square-closure
property is used to prove algebraic closedness of the complexification.

The semireal square obstruction supplies the field instance on `QuadraticAlgebra R (-1) 0`.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [Field R]

/-- Every element of `R[i]` is a square when `R` is real closed, without choosing an order. -/
theorem isSquare [IsRealClosed R] (z : QuadraticAlgebra R (-1) 0) : IsSquare z := by
  obtain ⟨o, ho⟩ := IsSemireal.exists_linearOrder (K := R)
  let := o
  have := ho
  exact z.isSquare_of_forall_nonneg_isSquare fun h => .of_nonneg h

end QuadraticAlgebra
