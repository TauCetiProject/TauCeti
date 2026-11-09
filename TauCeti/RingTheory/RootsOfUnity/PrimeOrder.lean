/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Roots of unity of prime order

For a prime `p`, every `p`-th root of unity `ζ ≠ 1` of a commutative monoid is a primitive `p`-th
root of unity: its order divides `p` and is not `1`. This is the analogue, inside the subgroup
`rootsOfUnity p M` of an arbitrary commutative monoid, of Mathlib's
`isPrimitiveRoot_of_mem_nthRootsFinset` for domains.

## Main results

* `rootsOfUnity.isPrimitiveRoot_of_ne_one`: for a prime `p`, a `p`-th root of unity other than `1`
  is a primitive `p`-th root of unity.
-/

public section

/-- **A nontrivial root of unity of prime order is primitive**: for a prime `p`, a `p`-th root of
unity `ζ ≠ 1` of a commutative monoid has order `p`. -/
theorem rootsOfUnity.isPrimitiveRoot_of_ne_one {M : Type*} [CommMonoid M] {p : ℕ} [Fact p.Prime]
    {ζ : rootsOfUnity p M} (hζ : ζ ≠ 1) : IsPrimitiveRoot ζ p :=
  IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime (Subtype.ext ((mem_rootsOfUnity p _).1 ζ.2)) hζ)
