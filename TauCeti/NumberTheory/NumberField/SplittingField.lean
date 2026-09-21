/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Splitting fields over number fields are number fields

The splitting field `f.SplittingField` of a polynomial `f` over a number field `K` is a finite
extension of `K`, hence a number field. In particular the splitting field of a rational
polynomial is a number field, so its Galois group `f.Gal` is the Galois group of a number field
and the arithmetic of `𝓞 f.SplittingField` (primes, Frobenius elements) is available in it
directly.

## Main results

* `Polynomial.SplittingField.instNumberField`: the splitting field of a polynomial over a number
  field is a number field.
-/

public section

namespace Polynomial.SplittingField

variable {K : Type*} [Field K] [NumberField K]

-- The instance is Layer 3.8 of the human-authored roadmap
-- `TauCetiRoadmap/NumberFieldArithmetic/Suggested.lean`, stated there for `K = ℚ`.
/-- The splitting field of a polynomial over a number field is a number field. -/
instance instNumberField (f : K[X]) : NumberField f.SplittingField :=
  NumberField.of_module_finite K f.SplittingField

end Polynomial.SplittingField
