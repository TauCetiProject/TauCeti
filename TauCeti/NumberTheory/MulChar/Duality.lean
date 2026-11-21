/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Duality

/-!
# The finite type of multiplicative characters of a monoid with finitely many units

Let `M` be a commutative monoid with finitely many units and `R` a domain. Mathlib's
`MulChar.finite` says that there are only finitely many characters `MulChar M R`. This file adds
the `Fintype` instance that sums over all characters need.

## Main results

* `MulChar.instFintypeMulChar`: `MulChar M R` is a `Fintype` for `Mˣ` finite and `R` a domain.
-/

public section

namespace MulChar

/-- The characters of a monoid with finitely many units, with values in a domain, form a finite
type (Mathlib's `MulChar.finite`). This instance lets one write sums over all characters. -/
noncomputable instance instFintypeMulChar {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R]
    [IsDomain R] : Fintype (MulChar M R) :=
  .ofFinite _

end MulChar
