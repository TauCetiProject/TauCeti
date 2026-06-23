/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Squarefree.Basic

/-!
# A squarefree non-unit is not a square

This file records the general commutative-monoid fact that a squarefree element which is not a
unit is not a square. Mathlib has the converse direction (`IsUnit.squarefree`) but not this one.
The statement is phrased with `Squarefree` dot-notation, so a caller holding `ha : Squarefree a`
and `hu : ¬ IsUnit a` can write `ha.not_isSquare hu`.
-/

/-- A squarefree non-unit of a commutative monoid is not a square: a square `r * r` would have
`r` as a square factor, so squarefreeness forces `r`, and hence `r * r`, to be a unit. -/
theorem Squarefree.not_isSquare {R : Type*} [CommMonoid R] {a : R}
    (ha : Squarefree a) (hu : ¬ IsUnit a) : ¬ IsSquare a := by
  rintro ⟨r, rfl⟩
  exact hu ((ha r dvd_rfl).mul (ha r dvd_rfl))
