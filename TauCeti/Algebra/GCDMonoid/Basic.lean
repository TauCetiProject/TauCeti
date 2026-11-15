/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Basic lemmas on GCD monoids

Basic complements to `Mathlib.Algebra.GCDMonoid.Basic`:

* `TauCeti.isDomain_of_isGCDMonoid`: a nontrivial commutative semiring with an `IsGCDMonoid`
  structure is a domain, since a GCD monoid is cancellative.
* `IsRelPrime.gcd_mul_left_cancel_right`: in a `NormalizedGCDMonoid`, a factor relatively prime to
  the left argument cancels from a product on the right of `GCDMonoid.gcd`.
-/

public section

namespace TauCeti

/-- A nontrivial commutative semiring with GCDs is a domain. -/
theorem isDomain_of_isGCDMonoid {D : Type*} [CommSemiring D] [IsGCDMonoid D] [Nontrivial D] :
    IsDomain D :=
  { IsGCDMonoid.isCancelMulZero (α := D) with }

end TauCeti

/-- In a normalized GCD monoid, a factor relatively prime to the left argument cancels from a
product on the right: if `IsRelPrime x y`, then `GCDMonoid.gcd x (y * z) = GCDMonoid.gcd x z`. -/
theorem IsRelPrime.gcd_mul_left_cancel_right {α : Type*} [CommMonoidWithZero α]
    [NormalizedGCDMonoid α] {x y : α} (h : IsRelPrime x y) (z : α) :
    GCDMonoid.gcd x (y * z) = GCDMonoid.gcd x z := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  · exact dvd_gcd (gcd_dvd_left _ _)
      ((h.of_dvd_left (gcd_dvd_left _ _)).dvd_of_dvd_mul_left (gcd_dvd_right _ _))
  · exact gcd_dvd_gcd_mul_left_right x z y
