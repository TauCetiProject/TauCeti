/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree helpers for multiquadratic radicands

This file records small squarefree arithmetic facts used by the multiquadratic degree and
prime-discriminant APIs.
-/

namespace TauCeti.Multiquadratic

/-- A squarefree non-unit of a commutative monoid is not a square: a square `r * r` has `r` as a
square factor, so squarefreeness forces `r` to be a unit, hence so is `r * r`. This converts the
arithmetic squarefreeness of a radicand product into the `¬ IsSquare` hypothesis the degree theorems
consume. -/
theorem not_isSquare_of_squarefree_of_not_isUnit {R : Type*} [CommMonoid R] {a : R}
    (ha : Squarefree a) (hu : ¬ IsUnit a) : ¬ IsSquare a := by
  rintro ⟨r, rfl⟩
  exact hu ((ha r dvd_rfl).mul (ha r dvd_rfl))

end TauCeti.Multiquadratic
