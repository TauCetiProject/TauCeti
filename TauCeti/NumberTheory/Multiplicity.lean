/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.LinearCombination

/-!
# Lifting a residue so that `b ^ n - 1` has exact `p`-adic valuation

Let `p` be a prime and `n` a natural number prime to `p`. If `b₀ ^ n ≡ 1 (mod p ^ k)`, then `b₀`
can be moved within its residue class modulo `p ^ k` so that `p ^ k` divides `b ^ n - 1` exactly,
that is, so that `b ^ n - 1` has `p`-adic valuation exactly `k`.

In the computation of the generator rank of the absolute Galois group of a `p`-adic field
(NSW (7.4.1)), this chooses the exponent through which a generator of tame inertia acts on the
`p`-power roots of unity.

## Main statements

* `TauCeti.exists_modEq_pow_sub_one_eq_mul`: the lift with `b ^ n - 1 = p ^ k * c`, `p ∤ c`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.4.1).
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- A lift `b₀` of a unit of order dividing `n` modulo `p ^ k`, with `p ∤ n`, can be moved by a
multiple of `p ^ k` so that `b ^ n - 1` has `p`-adic valuation exactly `k`. -/
theorem exists_modEq_pow_sub_one_eq_mul {k n b₀ : ℕ} (hn : ¬ p ∣ n)
    (hb₀ : b₀ ^ n ≡ 1 [MOD p ^ k]) :
    ∃ b : ℕ, b ≡ b₀ [MOD p ^ k] ∧ ∃ c : ℤ, (b : ℤ) ^ n - 1 = (p : ℤ) ^ k * c ∧ ¬ (p : ℤ) ∣ c := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  rcases k with - | k
  · -- For `k = 0` the congruence is empty, and `b = 0` gives `b ^ n - 1 = -1`.
    refine ⟨0, Nat.modEq_one, -1, by simp [zero_pow hn0], fun h ↦ hpZ.not_dvd_one ?_⟩
    exact (dvd_neg).mp h
  obtain ⟨c₀, hc₀⟩ : (p : ℤ) ^ (k + 1) ∣ (b₀ : ℤ) ^ n - 1 := by
    simpa using (Nat.modEq_iff_dvd.mp hb₀.symm)
  by_cases hc₀p : (p : ℤ) ∣ c₀
  · -- Replace `b₀` by `b₀ + p ^ (k + 1)`: the derivative term `n b₀ ^ (n - 1)` is prime to `p`.
    have hb₀p : ¬ (p : ℤ) ∣ b₀ := by
      intro h
      have h1 : (p : ℤ) ∣ (b₀ : ℤ) ^ n - 1 :=
        hc₀ ▸ dvd_mul_of_dvd_left (dvd_pow_self _ k.succ_ne_zero) _
      exact hpZ.not_dvd_one ((dvd_sub_right (dvd_pow h hn0)).mp h1)
    obtain ⟨m, hm⟩ := sq_dvd_add_pow_sub_sub ((p : ℤ) ^ (k + 1)) (b₀ : ℤ) n
    refine ⟨b₀ + p ^ (k + 1), Nat.add_modEq_right,
      c₀ + (b₀ : ℤ) ^ (n - 1) * n + (p : ℤ) ^ (k + 1) * m, ?_, ?_⟩
    · push_cast
      linear_combination hc₀ + hm
    · intro hdvd
      have hsplit : c₀ + (b₀ : ℤ) ^ (n - 1) * n + (p : ℤ) ^ (k + 1) * m =
          (b₀ : ℤ) ^ (n - 1) * n + (c₀ + (p : ℤ) ^ (k + 1) * m) := by ring
      rw [hsplit, dvd_add_left (dvd_add hc₀p
        (dvd_mul_of_dvd_left (dvd_pow_self _ k.succ_ne_zero) _))] at hdvd
      rcases hpZ.dvd_or_dvd hdvd with h | h
      · exact hb₀p (hpZ.dvd_of_dvd_pow h)
      · exact hn (Int.natCast_dvd_natCast.mp h)
  · exact ⟨b₀, Nat.ModEq.refl _, c₀, hc₀, hc₀p⟩

end TauCeti
