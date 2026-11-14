/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Roots of unity of prime order

For a prime `p`, every element `ζ ≠ 1` of a commutative monoid with `ζ ^ p = 1` is a primitive
`p`-th root of unity: its order divides `p` and is not `1`. This is the monoid analogue of
Mathlib's `isPrimitiveRoot_of_mem_nthRootsFinset` for domains. Consequently no power `ζ ^ m` with
`0 < m < p` is `1`; in particular the elements `ζ ≠ 1` of `rootsOfUnity p M` have this property.

## Main results

* `IsPrimitiveRoot.of_pow_eq_one_of_ne_one`: for a prime `p`, an element `ζ ≠ 1` with
  `ζ ^ p = 1` is a primitive `p`-th root of unity.
* `rootsOfUnity.isPrimitiveRoot_of_ne_one`: for a prime `p`, a `p`-th root of unity `ζ ≠ 1` is
  primitive.
* `rootsOfUnity.pow_ne_one_of_ne_one`: for a prime `p`, a `p`-th root of unity `ζ ≠ 1` satisfies
  `ζ ^ m ≠ 1` for `0 < m < p`.
-/

public section

/-- **A nontrivial root of unity of prime order is primitive**: for a prime `p`, an element
`ζ ≠ 1` of a commutative monoid with `ζ ^ p = 1` has order `p`. -/
theorem IsPrimitiveRoot.of_pow_eq_one_of_ne_one {M : Type*} [CommMonoid M] {p : ℕ} [Fact p.Prime]
    {ζ : M} (h : ζ ^ p = 1) (hζ : ζ ≠ 1) : IsPrimitiveRoot ζ p :=
  IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h hζ)

/-- For a prime `p`, a `p`-th root of unity `ζ ≠ 1` of a commutative monoid `M` is a primitive
`p`-th root of unity in `M`. -/
theorem rootsOfUnity.isPrimitiveRoot_of_ne_one {M : Type*} [CommMonoid M] {p : ℕ}
    [Fact p.Prime] {ζ : rootsOfUnity p M} (hζ : ζ ≠ 1) : IsPrimitiveRoot ((ζ : Mˣ) : M) p :=
  IsPrimitiveRoot.of_pow_eq_one_of_ne_one ((mem_rootsOfUnity' p _).1 ζ.2)
    (rootsOfUnity.coe_injective.ne hζ)

/-- For a prime `p`, a `p`-th root of unity `ζ ≠ 1` of a commutative monoid satisfies `ζ ^ m ≠ 1`
for every `0 < m < p`, since `ζ` is primitive. -/
theorem rootsOfUnity.pow_ne_one_of_ne_one {M : Type*} [CommMonoid M] {p : ℕ} [Fact p.Prime]
    {ζ : rootsOfUnity p M} (hζ : ζ ≠ 1) {m : ℕ} (h0 : m ≠ 0) (hm : m < p) : ζ ^ m ≠ 1 :=
  (IsPrimitiveRoot.of_pow_eq_one_of_ne_one (Subtype.ext ((mem_rootsOfUnity p _).1 ζ.2))
    hζ).pow_ne_one_of_pos_of_lt h0 hm
