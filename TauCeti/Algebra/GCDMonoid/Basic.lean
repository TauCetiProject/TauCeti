/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Nontrivial rings with GCDs

A nontrivial commutative semiring with a GCD monoid structure is a domain, since a GCD monoid is
cancellative.
-/

public section

namespace TauCeti

/-- A nontrivial commutative semiring with GCDs is a domain. -/
theorem isDomain_of_isGCDMonoid {D : Type*} [CommSemiring D] [IsGCDMonoid D] [Nontrivial D] :
    IsDomain D :=
  { IsGCDMonoid.isCancelMulZero (α := D) with }

end TauCeti
