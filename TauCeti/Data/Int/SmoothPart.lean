/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Data.Nat.Factorization.SmoothPart

/-!
# Signed powers after removing the smooth part

An odd power can absorb the sign of an integer when the complementary prime powers form a power.
-/

public section

/-- If the valuations of `t` at primes at least `k` are divisible by the odd exponent `ℓ`,
then `t` is the smooth part of its absolute value times an `ℓ`-th power. The signed root has
no prime factor below `k`. -/
theorem Int.exists_eq_smoothPart_mul_pow {t : ℤ} {k ℓ : ℕ} (hℓ : Odd ℓ)
    (hval : ∀ p, p.Prime → k ≤ p → ℓ ∣ padicValInt p t) :
    ∃ z : ℤ, t = (t.natAbs.smoothPart k : ℤ) * z ^ ℓ ∧
      ∀ p ∈ z.natAbs.primeFactors, k ≤ p := by
  obtain ⟨u, hu, hlarge⟩ := Nat.exists_eq_smoothPart_mul_pow (m := t.natAbs) hℓ.pos.ne'
    fun p hp hk ↦ by
      simpa only [padicValInt, Nat.multiplicity_eq_factorization hp] using hval p hp hk
  have hcast : (t.natAbs : ℤ) = (t.natAbs.smoothPart k : ℤ) * (u : ℤ) ^ ℓ := by
    exact_mod_cast hu
  rcases t.natAbs_eq with ht | ht
  · exact ⟨u, ht.trans hcast, by simpa using hlarge⟩
  · refine ⟨-(u : ℤ), ht.trans ?_, by simpa using hlarge⟩
    rw [hcast, hℓ.neg_pow, mul_neg]
