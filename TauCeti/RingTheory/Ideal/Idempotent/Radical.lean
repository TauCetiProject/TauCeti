/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import TauCeti.RingTheory.Ideal.Idempotent.FG

/-!
# Idempotence of radical ideals over algebraically closed fields

In a commutative ring `R` that is integrally closed in an algebraically closed field `K`, every
element has a square root in `R`: its square root in `K` is integral over `R` and therefore
descends to `R`. By `Ideal.IsRadical.isIdempotentElem_of_exists_pow_eq` (with `n = 2`), every
radical ideal of `R` is idempotent.

In particular, the maximal ideal of a valuation domain whose fraction field is algebraically closed
is idempotent.

## Main results

* `Ideal.IsRadical.isIdempotentElem_of_isAlgClosed`: every radical ideal of a ring integrally
  closed in an algebraically closed field is idempotent.
-/

public section

namespace Ideal.IsRadical

/-- In a ring that is integrally closed in an algebraically closed field `K`, every radical ideal
is idempotent: each of its elements is the square of an element of the ideal. This covers the
maximal ideal of a valuation ring whose fraction field is algebraically closed. -/
theorem isIdempotentElem_of_isAlgClosed {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsRadical)
    (K : Type*) [Field K] [Algebra R K] [IsIntegrallyClosedIn R K] [IsAlgClosed K] :
    IsIdempotentElem I := by
  refine hI.isIdempotentElem_of_exists_pow_eq (n := 2) le_rfl fun x _ ↦ ?_
  -- A square root of `x` in `K` is integral over `R`, so it is the image of some `c ∈ R`.
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R K x) two_pos
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow (R := R) two_pos
    (hy ▸ isIntegral_algebraMap)
  exact ⟨c, IsIntegralClosure.algebraMap_injective R R K (by simpa using hy)⟩

end Ideal.IsRadical
