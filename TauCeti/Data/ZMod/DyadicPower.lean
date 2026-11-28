/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases

/-!
# Powers equal to minus one modulo a power of two

Modulo a power of two, the only unit whose cyclic subgroup contains `-1` is `-1` itself.
For moduli divisible by four, reduction modulo four forces the exponent to be odd.
An odd power is injective on this finite group of order a power of two.
-/

public section

namespace ZMod

/-- If a positive power of a residue modulo `2 ^ (s + 1)` is `-1`, the residue itself is `-1`. -/
theorem eq_neg_one_of_pow_eq_neg_one_two_pow {s k : ℕ} {a : ZMod (2 ^ (s + 1))}
    (hk₀ : k ≠ 0) (h : a ^ k = -1) : a = -1 := by
  have hu : IsUnit a := (isUnit_pow_iff hk₀).mp (h.symm ▸ isUnit_neg_one)
  obtain ⟨u, rfl⟩ := hu
  have he : u ^ k = -1 := Units.ext h
  cases s with
  | zero =>
    have hcard : Fintype.card (ZMod 2)ˣ = 1 := by rw [card_units_eq_totient]; decide
    exact congrArg Units.val ((Fintype.card_le_one_iff.mp hcard.le) u (-1))
  | succ s =>
    have h4 : 4 ∣ 2 ^ (s + 1 + 1) := pow_dvd_pow 2 (by omega : 2 ≤ s + 1 + 1)
    have hm := congrArg (castHom h4 (ZMod 4)) h
    have hm' : (castHom h4 (ZMod 4) (u : ZMod (2 ^ (s + 1 + 1)))) ^ k = -1 := by
      simpa only [map_pow, map_neg, map_one] using hm
    have hk : ¬ Even k := by
      rintro ⟨j, rfl⟩
      rw [← two_mul, pow_mul'] at hm'
      generalize ((castHom h4 (ZMod 4) (u : ZMod (2 ^ (s + 1 + 1)))) ^ j) = b at hm'
      fin_cases b <;> contradiction
    have hcard : Nat.card (ZMod (2 ^ (s + 1 + 1)))ˣ = 2 ^ (s + 1) := by
      rw [Nat.card_eq_fintype_card, card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_two]
      simp
    have hc : (Nat.card (ZMod (2 ^ (s + 1 + 1)))ˣ).Coprime k := by
      rw [hcard]
      have h₂k : ¬ 2 ∣ k := by rwa [← even_iff_two_dvd]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h₂k).pow_left _
    have hu' : u = -1 := (powCoprime hc).injective (by
      rw [powCoprime_apply, powCoprime_apply, he, (Nat.not_even_iff_odd.mp hk).neg_one_pow])
    exact congrArg Units.val hu'

end ZMod
