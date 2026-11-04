/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Nat.Prime.Basic
-- Proof-only: Bernoulli's inequality, the `p`-adic factorisation of a natural number, tactics.
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Divisibility in commutative rings

## Divisibility up to a unit and a multiple of the divisor

In a commutative ring, whether `a` divides an element does not change when a multiple of `a` is
added to it and the result is multiplied by a unit. This combines `IsUnit.dvd_mul_left` with
`dvd_add_left`, in the shape produced by transformation formulas such as those of a change of
variables of a Weierstrass equation, where the new coefficient is a unit times the old one plus a
correction term.

## Divisibility of powers by successive integers

If `p ∣ s ^ (p - 1)` for a prime `p` and every natural number prime to `p` is a unit, then
`n + 1 ∣ sⁿ` for every `n`. This is the condition under which the denominators `n + 1` of a
logarithm `∑ aₙ Tⁿ⁺¹ / (n + 1)` are cancelled after rescaling `T` by `s`. For the ring of integers
of a finite extension of `ℚ_p` with normalised valuation `v`, it asks `v(s) ≥ v(p) / (p - 1)`.

## Main results

* `IsUnit.dvd_iff_of_eq_mul_add`: if `y = v * (x + a * z)` with `v` a unit, then `a ∣ y ↔ a ∣ x`.
* `TauCeti.natCast_add_one_dvd_pow`: a sufficient condition for `n + 1 ∣ sⁿ` for every `n`.
-/

public section

variable {R : Type*} [CommRing R]

/-- Divisibility by `a` is unchanged by adding a multiple of `a` and multiplying by a unit: if
`y = v * (x + a * z)` with `v` a unit, then `a ∣ y ↔ a ∣ x`. -/
theorem IsUnit.dvd_iff_of_eq_mul_add {a x y v : R} (hv : IsUnit v) (z : R)
    (h : y = v * (x + a * z)) : a ∣ y ↔ a ∣ x := by
  rw [h, hv.dvd_mul_left, dvd_add_left (_root_.dvd_mul_right a z)]

namespace TauCeti

/-- **`n + 1` divides `sⁿ` for every `n`**, if `p ∣ s ^ (p - 1)` for a prime `p` and every natural
number prime to `p` is a unit. -/
theorem natCast_add_one_dvd_pow {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime) {s : R}
    (hs : (p : R) ∣ s ^ (p - 1)) (hR : ∀ m : ℕ, p.Coprime m → IsUnit (m : R)) (n : ℕ) :
    (n + 1 : R) ∣ s ^ n := by
  -- Write `n + 1 = pᵏ m` with `m` prime to `p`: then `pᵏ` divides `s ^ (k (p - 1))`, and
  -- `k (p - 1) ≤ pᵏ - 1 ≤ n`.
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd n.succ_ne_zero p hp.one_lt.ne'
  have hm₀ : m ≠ 0 := by rintro rfl; simp at hm
  -- Bernoulli's inequality `1 + k (p - 1) ≤ pᵏ`, so `k (p - 1) ≤ n`
  have hk : k * (p - 1) ≤ n := by
    have h₂ : (-2 : ℤ) ≤ (p - 1 : ℕ) := by omega
    have h := one_add_mul_le_pow h₂ k
    have hp₁ : ((p - 1 : ℕ) : ℤ) + 1 = p := by rw [Nat.cast_sub hp.one_le]; ring
    rw [add_comm (1 : ℤ) ((p - 1 : ℕ) : ℤ), hp₁] at h
    have : p ^ k ≤ n + 1 := by
      rw [← Nat.succ_eq_add_one, hn]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm₀)
    zify at this ⊢
    linarith
  have hcast : (n + 1 : R) = (p : R) ^ k * (m : R) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← hn, Nat.cast_succ]
  rw [hcast, (hR m ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).mul_right_dvd]
  exact (pow_dvd_pow_of_dvd hs k).trans (by rw [← pow_mul]; exact pow_dvd_pow s (by linarith))

end TauCeti
