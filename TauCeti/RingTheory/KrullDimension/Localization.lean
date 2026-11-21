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
`M`, with the same heights (`IsLocalization.height_under`). Thus the dimension of the localization
is bounded by `d` exactly when the heights of these primes are
(`TauCeti.ringKrullDim_localization_le_iff_height_le`).
-/

public section

namespace TauCeti

/-- A localization of `A` at `M` has Krull dimension at most `d` if and only if every prime of `A`
disjoint from `M` has height at most `d`. -/
theorem ringKrullDim_localization_le_iff_height_le {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S] (d : WithBot ℕ∞) :
    ringKrullDim S ≤ d ↔
      ∀ p : Ideal A, p.IsPrime → Disjoint (M : Set A) p → (Ideal.height p : WithBot ℕ∞) ≤ d := by
  rw [ringKrullDim_le_iff_height_le]
  refine ⟨fun h p hp hdisj ↦ ?_, fun h p hp ↦ ?_⟩
  · rw [← IsLocalization.height_map_of_disjoint (S := S) M p hdisj]
    exact h (IsLocalization.isPrime_of_isPrime_disjoint M S p hp hdisj)
  · rw [← IsLocalization.height_under M p]
    exact h (p.under A) inferInstance
      ((IsLocalization.isPrime_iff_isPrime_disjoint M S p).mp hp).2

end TauCeti
