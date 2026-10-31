/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Height bounds and detection of units

In a local ring of finite Krull dimension `n + 1`, the maximal ideal is the only prime of height
greater than `n`. This complements Mathlib's `Ideal.height_eq_ringKrullDim_iff`.

In a Noetherian ring, an element is a unit if it belongs to no prime of height at most one.
Indeed, a nonunit generates a proper principal ideal, and a minimal prime over that ideal has
height at most one by Krull's principal ideal theorem. Applied to a discriminant, this detects
étaleness of a finite free algebra using only primes of height at most one.

## Main results

* `Ideal.lt_height_iff_eq_maximalIdeal`: in a local ring of Krull dimension `n + 1`, a prime has
  height greater than `n` iff it is the maximal ideal.
* `TauCeti.isUnit_iff_forall_notMem_of_height_le_one`: units in a Noetherian ring are detected
  by primes of height at most one.
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

namespace TauCeti

/-- An element of a Noetherian ring is a unit if and only if it belongs to no prime of height
at most one. -/
theorem isUnit_iff_forall_notMem_of_height_le_one {R : Type*} [CommRing R]
    [IsNoetherianRing R] (x : R) :
    IsUnit x ↔ ∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 → x ∉ p := by
  refine ⟨fun hx p _ _ ↦ p.notMem_of_isUnit hx, fun h ↦ ?_⟩
  by_contra hx
  obtain ⟨p, hp⟩ := (Ideal.span {x}).nonempty_minimalPrimes (by simpa using hx)
  have := hp.isPrime
  exact h p (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp)
    (hp.le (Ideal.subset_span (Set.mem_singleton x)))

end TauCeti
