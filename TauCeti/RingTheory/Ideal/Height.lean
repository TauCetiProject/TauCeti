/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height

/-!
# Primes of maximal height in a local ring

In a local ring of finite Krull dimension `n + 1`, the maximal ideal is the only prime of height
greater than `n`. This complements Mathlib's `Ideal.height_eq_ringKrullDim_iff`.

## Main results

* `Ideal.lt_height_iff_eq_maximalIdeal`: in a local ring of Krull dimension `n + 1`, a prime has
  height greater than `n` iff it is the maximal ideal.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- In a local ring of Krull dimension `n + 1`, a prime has height greater than `n` iff it is the
maximal ideal. -/
theorem lt_height_iff_eq_maximalIdeal {n : ℕ} (hdim : ringKrullDim R = n + 1) {I : Ideal R}
    [I.IsPrime] : n < I.height ↔ I = IsLocalRing.maximalIdeal R := by
  have : FiniteRingKrullDim R := finiteRingKrullDim_iff_ne_bot_and_top.mpr
    ⟨by simp [hdim], by
      rw [hdim, ← WithBot.coe_top]
      exact_mod_cast ENat.natCast_ne_top (n + 1)⟩
  rw [← height_eq_ringKrullDim_iff, hdim]
  refine ⟨fun h ↦ le_antisymm (hdim ▸ height_le_ringKrullDim_of_isPrime) ?_, fun h ↦ ?_⟩
  · exact_mod_cast Order.add_one_le_of_lt h
  · have h' : I.height = (n + 1 : ℕ) := by exact_mod_cast h
    exact h' ▸ by exact_mod_cast n.lt_succ_self

end Ideal
