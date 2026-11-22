/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.WittVector.Big.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Checks for the big Witt ring

Over `ℤ` on the truncation set `Div(2) = {1, 2}`, the sum `1 + 1` has coordinates `(2, -1)`, so
addition of big Witt vectors is not coordinatewise. Over `𝔽₂` the vector with coordinates `(0, 1)`
is nonzero although both of its ghost components vanish, so the ghost map is not injective
without the torsion hypothesis of `BigWittVector.ghostMap_injective`. The big Witt vectors indexed
by the empty truncation set form the zero ring.
-/

open TauCeti BigWitt

-- `1 + 1 = (2, -1)` in `W_{Div(2)}(ℤ)`: its ghost components `(2, 2 ^ 2 + 2 * (-1))` are `(2, 2)`.
example : (1 + 1 : BigWittVector (TruncationSet.divisors 2) ℤ) =
    ⟨fun n ↦ if n = 1 then 2 else if n = 2 then -1 else 0, fun n hn ↦ by
      have h1 : n ≠ 1 := by rintro rfl; exact hn (by simp)
      have h2 : n ≠ 2 := by rintro rfl; exact hn (by simp)
      simp [h1, h2]⟩ := by
  refine BigWittVector.ghostMap_injective
    (fun p _ hp ↦ .of_ne_zero (Int.natCast_ne_zero.2 hp.ne_zero)) (funext fun ⟨n, hn⟩ ↦ ?_)
  rw [map_add, map_one, Pi.add_apply, Pi.one_apply, BigWittVector.ghostMap_apply]
  rcases (Nat.dvd_prime Nat.prime_two).1 (TruncationSet.mem_divisors.1 hn).1 with rfl | rfl
  · simp
  · simp [ghostPolynomial_prime Nat.prime_two]

-- Over `𝔽₂`, the nonzero vector `(0, 1)` has ghost components `(0, 2)`, which vanish.
example : ∃ x : BigWittVector (TruncationSet.divisors 2) (ZMod 2),
    x ≠ 0 ∧ BigWittVector.ghostMap x = 0 := by
  refine ⟨⟨fun n ↦ if n = 2 then 1 else 0, fun n hn ↦ ?_⟩, fun h ↦ ?_, funext fun ⟨n, hn⟩ ↦ ?_⟩
  · have h2 : n ≠ 2 := by rintro rfl; exact hn (by simp)
    simp [h2]
  · simpa using congrArg (BigWittVector.coeff · 2) h
  · rw [BigWittVector.ghostMap_apply]
    rcases (Nat.dvd_prime Nat.prime_two).1 (TruncationSet.mem_divisors.1 hn).1 with rfl | rfl
    · simp
    · simpa [ghostPolynomial_prime Nat.prime_two] using (by decide : (2 : ZMod 2) = 0)

-- The empty truncation set gives the zero ring.
example (R : Type*) [CommRing R] (x : BigWittVector ⊥ R) : x = 0 :=
  Subsingleton.elim x 0
