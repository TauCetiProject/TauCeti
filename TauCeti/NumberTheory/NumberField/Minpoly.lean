/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Minimal polynomials of algebraic integers

An algebraic integer `x` of a number field `K` has a minimal polynomial over `ℤ`, as an element of
`𝓞 K`, and a minimal polynomial over `ℚ`, as an element of `K`. Since `ℤ` is integrally closed,
the second is the first with its coefficients cast to `ℚ`.

## Main results

* `NumberField.RingOfIntegers.minpoly_rat_coe`:
  `minpoly ℚ (x : K) = (minpoly ℤ x).map (algebraMap ℤ ℚ)`.
-/

public section

open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

-- This identification is stated, for integral primitive elements, in the human-authored
-- specification `TauCetiRoadmap/NumberFieldArithmetic/Suggested.lean`, Layer 3.2.

/-- The minimal polynomial over `ℚ` of an algebraic integer `x`, viewed in `K`, is its minimal
polynomial over `ℤ` with the coefficients cast to `ℚ`. -/
theorem minpoly_rat_coe (x : 𝓞 K) :
    minpoly ℚ (x : K) = (minpoly ℤ x).map (algebraMap ℤ ℚ) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ x.isIntegral_coe, minpoly_coe]

end NumberField.RingOfIntegers
