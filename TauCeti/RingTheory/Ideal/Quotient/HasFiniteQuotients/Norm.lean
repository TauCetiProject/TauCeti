/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

/-!
# Northcott absolute norm on nonzero ideals

In an infinite Dedekind domain with finite quotients, only finitely many nonzero ideals have
absolute norm at most any bound. The resulting Northcott instance supplies finite cutoff carriers
for counting nonzero ideals over any such domain.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

/-- The absolute norm on nonzero ideals of an infinite Dedekind domain with finite quotients is
Northcott, by `Ring.HasFiniteQuotients.finite_absNorm_le`. Mathlib already supplies the
corresponding instance on height-one primes. -/
instance instNorthcottAbsNormNonZeroDivisors {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Infinite R] [Ring.HasFiniteQuotients R] :
    Northcott (fun I : (Ideal R)⁰ ↦ Ideal.absNorm (I : Ideal R)) := by
  constructor
  intro B
  exact (Ring.HasFiniteQuotients.finite_absNorm_le (S := R) B).preimage
    Subtype.val_injective.injOn

end TauCeti
