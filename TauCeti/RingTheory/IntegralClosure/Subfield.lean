/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Subfields of fields algebraic over `ℚ`

A subfield of a field of characteristic zero is a `ℚ`-algebra through its own field structure,
not as a `ℚ`-subalgebra, so Mathlib's `Subalgebra.isIntegral` does not apply to it. This file
records the corresponding instance.

## Main results

* `Subfield.isIntegral`: a subfield of a field algebraic over `ℚ` is algebraic over `ℚ`.
-/

public section

namespace Subfield

/-- **A subfield of a field algebraic over `ℚ` is algebraic over `ℚ`.** The subfield analogue of
`Subalgebra.isIntegral`. -/
instance isIntegral {L : Type*} [Field L] [CharZero L] [Algebra.IsIntegral ℚ L]
    (F : Subfield L) : Algebra.IsIntegral ℚ F :=
  Algebra.IsIntegral.of_injective F.subtype.toRatAlgHom F.subtype_injective

end Subfield
