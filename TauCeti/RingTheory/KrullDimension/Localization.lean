/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height

/-!
# Krull dimension of a localization

The primes of a localization at `M` correspond to the primes of the base ring disjoint from
`M`, with the same heights (`IsLocalization.height_under`). Thus a bound on these heights bounds
the dimension of the localization (`TauCeti.ringKrullDim_localization_le_of_height_le`).
-/

public section

namespace TauCeti

/-- If every prime of `A` disjoint from `M` has height at most `n`, then a localization of `A`
at `M` has Krull dimension at most `n`. -/
theorem ringKrullDim_localization_le_of_height_le {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S] {n : ℕ}
    (hdim : ∀ p : Ideal A, p.IsPrime → Disjoint (M : Set A) p → Ideal.height p ≤ n) :
    ringKrullDim S ≤ n := by
  refine (ringKrullDim_le_iff_height_le _).mpr fun p hp ↦ ?_
  rw [← IsLocalization.height_under M p]
  exact WithBot.coe_le_coe.mpr (hdim (p.under A) inferInstance
    ((IsLocalization.isPrime_iff_isPrime_disjoint M S p).mp hp).2)

end TauCeti
