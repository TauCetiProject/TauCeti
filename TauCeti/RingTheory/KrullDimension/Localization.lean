/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height

/-!
# Krull dimension of a basic open

The primes of a localization `A[1/a]` correspond to the primes of `A` avoiding `a`, with the same
heights (`IsLocalization.height_under`). So the Krull dimension of `A[1/a]` is bounded by any
bound on the heights of the primes of the basic open `D(a)` of `Spec A`
(`TauCeti.ringKrullDim_le_of_height_le_on_basicOpen`).
-/

public section

namespace TauCeti

/-- If every prime of `A` avoiding `a` has height at most `n`, then the localization `A[1/a]` has
Krull dimension at most `n`. -/
theorem ringKrullDim_le_of_height_le_on_basicOpen {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] (a : A) [IsLocalization.Away a S] {n : ℕ}
    (hdim : ∀ p : Ideal A, p.IsPrime → a ∉ p → Ideal.height p ≤ n) :
    ringKrullDim S ≤ n := by
  refine (ringKrullDim_le_iff_height_le _).mpr fun p _ ↦ ?_
  rw [← IsLocalization.height_under (Submonoid.powers a) p]
  -- The prime of `A` under `p` avoids `a`, which is a unit in `S`.
  refine WithBot.coe_le_coe.mpr (hdim (p.under A) inferInstance fun ha ↦ ?_)
  exact ‹p.IsPrime›.ne_top
    (p.eq_top_of_isUnit_mem (Ideal.mem_comap.mp ha) (IsLocalization.Away.algebraMap_isUnit a))

end TauCeti
