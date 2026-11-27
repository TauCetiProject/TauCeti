/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SmoothNumbers
public import TauCeti.Data.Nat.ExactDivisor
import TauCeti.Data.Nat.Factorization.PowMul

/-!
# The smooth part of a natural number

The `k`-smooth part of `m` retains the full prime powers of `m` at primes strictly below `k`.
If all other prime exponents are multiples of a positive `ℓ`, the complement is an `ℓ`-th
power whose root has no prime factor below `k`.
-/

public section

namespace Nat

/-- The product of the full prime powers of `m` at primes below `k`, with value `1` at `m = 0`. -/
def smoothPart (m k : ℕ) : ℕ :=
  TauCeti.Nat.prodPrimePow m (Finset.range k)

/-- The smooth part is an exact divisor, including at zero where the smooth part is one. -/
theorem isExactDivisor_smoothPart (m k : ℕ) : TauCeti.Nat.IsExactDivisor (m.smoothPart k) m :=
  TauCeti.Nat.isExactDivisor_prodPrimePow (N := m) (s := Finset.range k)

theorem smoothPart_pos (m k : ℕ) : 0 < m.smoothPart k :=
  (isExactDivisor_smoothPart m k).pos

/-- The smooth part is smooth for its cutoff, including when the input is zero. -/
@[simp] theorem smoothPart_mem_smoothNumbers (m k : ℕ) : m.smoothPart k ∈ smoothNumbers k := by
  apply mem_smoothNumbers_of_primeFactors_subset (smoothPart_pos m k).ne'
  rw [smoothPart, TauCeti.Nat.primeFactors_prodPrimePow]
  exact Finset.inter_subset_left

/-- The smooth part has precisely the restriction of the original prime exponents. -/
@[simp] theorem factorization_smoothPart (m k : ℕ) :
    (m.smoothPart k).factorization = m.factorization.filter (· < k) := by
  ext p
  simp only [smoothPart, TauCeti.Nat.factorization_prodPrimePow, Finset.mem_range,
    Finsupp.filter_apply]

@[simp] theorem zero_smoothPart (k : ℕ) : (0 : ℕ).smoothPart k = 1 :=
  eq_of_factorization_eq' (smoothPart_pos 0 k).ne' one_ne_zero (by simp [Finsupp.filter_zero])

@[simp] theorem one_smoothPart (k : ℕ) : (1 : ℕ).smoothPart k = 1 :=
  eq_of_factorization_eq' (smoothPart_pos 1 k).ne' one_ne_zero (by simp [Finsupp.filter_zero])

/-- The smooth part as a product of full prime powers. -/
theorem smoothPart_eq_prod_primeFactors (m k : ℕ) :
    m.smoothPart k = ∏ p ∈ m.primeFactors with p < k, p ^ m.factorization p := by
  calc
    _ = (m.smoothPart k).factorization.prod (· ^ ·) :=
      (prod_factorization_pow_eq_self (smoothPart_pos m k).ne').symm
    _ = _ := by
      rw [factorization_smoothPart, Finsupp.prod_filter_index, Finsupp.support_filter,
        support_factorization]

/-- The prime factors of the smooth part are exactly the prime factors below `k`.
At zero both sets are empty. -/
@[simp] theorem primeFactors_smoothPart (m k : ℕ) :
    (m.smoothPart k).primeFactors = m.primeFactors.filter (· < k) := by
  rw [smoothPart, TauCeti.Nat.primeFactors_prodPrimePow]
  ext p
  simp [and_comm]

/-- The smooth part divides its input, including at zero. -/
theorem smoothPart_dvd (m k : ℕ) : m.smoothPart k ∣ m :=
  (isExactDivisor_smoothPart m k).dvd

/-- Dividing out the smooth part retains exactly the prime exponents at or above the cutoff. -/
@[simp] theorem factorization_div_smoothPart (m k : ℕ) :
    (m / m.smoothPart k).factorization = m.factorization.filter (k ≤ ·) := by
  rw [factorization_div (smoothPart_dvd m k), factorization_smoothPart]
  simpa only [add_tsub_cancel_left, Nat.not_lt] using
    congrArg (· - m.factorization.filter (· < k))
      (Finsupp.filter_add_filter_not m.factorization (· < k)).symm

/-- The smooth part is multiplicative on nonzero natural numbers. -/
theorem smoothPart_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    (a * b).smoothPart k = a.smoothPart k * b.smoothPart k := by
  have ha' := (smoothPart_pos a k).ne'
  have hb' := (smoothPart_pos b k).ne'
  apply eq_of_factorization_eq' (smoothPart_pos ..).ne' (mul_ne_zero ha' hb')
  simp only [factorization_mul ha hb, factorization_mul ha' hb', factorization_smoothPart,
    Finsupp.filter_add]

/-- A number equals its smooth part precisely when it is smooth. -/
@[simp] theorem smoothPart_eq_self_iff {m k : ℕ} : m.smoothPart k = m ↔ m ∈ smoothNumbers k := by
  refine ⟨fun h ↦ h ▸ smoothPart_mem_smoothNumbers m k, fun hm ↦ ?_⟩
  apply eq_of_factorization_eq' (smoothPart_pos ..).ne' (ne_zero_of_mem_smoothNumbers hm)
  rw [factorization_smoothPart, Finsupp.filter_eq_self_iff]
  intro p hp
  have hmem : p ∈ m.primeFactors := support_factorization m ▸ Finsupp.mem_support_iff.mpr hp
  exact (mem_primesBelow.mp (primeFactors_subset_of_mem_smoothNumbers hm hmem)).1

/-- A smooth number divides the smooth part of a nonzero number exactly when it divides
the original number. -/
@[simp] theorem dvd_smoothPart_iff {a m k : ℕ} (hm : m ≠ 0) (ha : a ∈ smoothNumbers k) :
    a ∣ m.smoothPart k ↔ a ∣ m := by
  refine ⟨fun h ↦ h.trans (smoothPart_dvd m k), ?_⟩
  rintro ⟨b, rfl⟩
  rw [smoothPart_mul (ne_zero_of_mem_smoothNumbers ha) (right_ne_zero_of_mul hm) k,
    smoothPart_eq_self_iff.mpr ha]
  exact dvd_mul_right ..

/-- The smooth part is trivial precisely when all prime factors are at least the cutoff. -/
theorem smoothPart_eq_one_iff {m k : ℕ} :
    m.smoothPart k = 1 ↔ ∀ p ∈ m.primeFactors, k ≤ p := by
  have h : (m.smoothPart k).primeFactors = ∅ ↔ m.smoothPart k = 1 := by
    rw [primeFactors_eq_empty, or_iff_right (smoothPart_pos ..).ne']
  rw [← h, primeFactors_smoothPart, Finset.filter_eq_empty_iff]
  simp

/-- For a cutoff of at most two, the smooth part is one. -/
@[simp] theorem smoothPart_eq_one_of_le_two (m : ℕ) {k : ℕ} (hk : k ≤ 2) :
    m.smoothPart k = 1 :=
  smoothPart_eq_one_iff.mpr fun _ hp ↦ hk.trans (prime_of_mem_primeFactors hp).two_le

/-- If the valuations at primes at least `k` are divisible by the positive exponent `ℓ`,
the complement of the smooth part is an `ℓ`-th power with all root primes at least `k`. -/
theorem exists_eq_smoothPart_mul_pow {m k ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hval : ∀ p, p.Prime → k ≤ p → ℓ ∣ m.factorization p) :
    ∃ u : ℕ, m = m.smoothPart k * u ^ ℓ ∧ ∀ p ∈ u.primeFactors, k ≤ p := by
  let b := m / m.smoothPart k
  have hmul : m.smoothPart k * b = m := Nat.mul_div_cancel' (smoothPart_dvd ..)
  obtain ⟨a, u, ha, hu⟩ := exists_dvd_and_eq_mul_pow_of_dvd_factorization
    (m := b) (S := ∅) hℓ fun p _ ↦ by
      simp only [b, factorization_div_smoothPart, Finsupp.filter_apply]
      split_ifs with hp
      · by_cases hprime : p.Prime
        · exact hval p hprime hp
        · simp [factorization_eq_zero_of_not_prime _ hprime]
      · exact dvd_zero _
  have ha' : a = 1 := by simpa using ha
  have hu' : b = u ^ ℓ := by simpa [ha'] using hu
  refine ⟨u, hmul.symm.trans (congrArg (m.smoothPart k * ·) hu'), fun p hp ↦ ?_⟩
  have hpb : p ∈ b.primeFactors := by simpa only [hu', primeFactors_pow _ hℓ] using hp
  dsimp only [b] at hpb
  rw [← support_factorization, factorization_div_smoothPart, Finsupp.support_filter] at hpb
  exact (Finset.mem_filter.mp hpb).2

end Nat
