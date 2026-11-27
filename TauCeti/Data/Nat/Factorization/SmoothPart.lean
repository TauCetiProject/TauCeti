/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.SmoothNumbers
import TauCeti.Data.Nat.ExactDivisor
import TauCeti.Data.Nat.Factorization.PowMul

/-!
# The smooth part of a natural number

The `k`-smooth part of `m` retains the full prime powers of `m` at primes strictly below `k`.
If all other prime exponents are multiples of `ℓ`, the complementary divisor is an `ℓ`-th power
whose root has no prime factor below `k`.
-/

public section

namespace Nat

/-- The product of the full prime powers of `m` at primes below `k`, with value `1` at `m = 0`. -/
def smoothPart (m k : ℕ) : ℕ :=
  TauCeti.Nat.prodPrimePow m (Finset.range k)

theorem smoothPart_pos (m k : ℕ) : 0 < m.smoothPart k :=
  (TauCeti.Nat.isExactDivisor_prodPrimePow (N := m) (s := Finset.range k)).pos

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
theorem smoothPart_def (m k : ℕ) :
    m.smoothPart k = ∏ p ∈ m.primeFactors with p < k, p ^ m.factorization p := by
  calc
    _ = (m.smoothPart k).factorization.prod (· ^ ·) :=
      (prod_factorization_pow_eq_self (smoothPart_pos m k).ne').symm
    _ = _ := by simp [Finsupp.prod_filter_index]

@[simp] theorem primeFactors_smoothPart (m k : ℕ) :
    (m.smoothPart k).primeFactors = m.primeFactors.filter (· < k) := by
  rw [smoothPart, TauCeti.Nat.primeFactors_prodPrimePow]
  ext p
  simp [and_comm]

theorem smoothPart_dvd (m k : ℕ) : m.smoothPart k ∣ m :=
  (TauCeti.Nat.isExactDivisor_prodPrimePow (N := m) (s := Finset.range k)).dvd

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
  apply eq_of_factorization_eq' (smoothPart_pos ..).ne' hm.1
  rw [factorization_smoothPart, Finsupp.filter_eq_self_iff]
  exact fun p hp ↦ hm.2 p (mem_primeFactors_iff_mem_primeFactorsList.mp
    (Finsupp.mem_support_iff.mpr hp))

/-- A smooth number divides the smooth part of a nonzero number exactly when it divides
the original number. -/
@[simp] theorem dvd_smoothPart_iff {a m k : ℕ} (hm : m ≠ 0) (ha : a ∈ smoothNumbers k) :
    a ∣ m.smoothPart k ↔ a ∣ m := by
  refine ⟨fun h ↦ h.trans (smoothPart_dvd m k), ?_⟩
  rintro ⟨b, rfl⟩
  rw [smoothPart_mul ha.1 (right_ne_zero_of_mul hm) k, smoothPart_eq_self_iff.mpr ha]
  exact dvd_mul_right ..

/-- The smooth part is trivial precisely when all prime factors are at least the cutoff. -/
theorem smoothPart_eq_one_iff {m k : ℕ} :
    m.smoothPart k = 1 ↔ ∀ p ∈ m.primeFactors, k ≤ p := by
  have h : (m.smoothPart k).primeFactors = ∅ ↔ m.smoothPart k = 1 := by
    rw [primeFactors_eq_empty, or_iff_right (smoothPart_pos ..).ne']
  rw [← h, primeFactors_smoothPart, Finset.filter_eq_empty_iff]
  simp

/-- There are no primes strictly below a cutoff of at most two. -/
theorem smoothPart_eq_one_of_le_two (m : ℕ) {k : ℕ} (hk : k ≤ 2) : m.smoothPart k = 1 :=
  smoothPart_eq_one_iff.mpr fun _ hp ↦ hk.trans (prime_of_mem_primeFactors hp).two_le

/-- If the valuations at or above the cutoff are divisible by `ℓ`, the complement of the smooth
part is an `ℓ`-th power with all root primes at least `k`. -/
theorem exists_eq_smoothPart_mul_pow {m k ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hval : ∀ p, p.Prime → k ≤ p → ℓ ∣ m.factorization p) :
    ∃ u : ℕ, m = m.smoothPart k * u ^ ℓ ∧ ∀ p ∈ u.primeFactors, k ≤ p := by
  let b := m / m.smoothPart k
  have hmul : m.smoothPart k * b = m := Nat.mul_div_cancel' (smoothPart_dvd ..)
  have hfac (p : ℕ) : b.factorization p = if p < k then 0 else m.factorization p := by
    simp only [b, factorization_div (smoothPart_dvd ..), Finsupp.tsub_apply,
      factorization_smoothPart, Finsupp.filter_apply]
    split <;> simp
  obtain ⟨a, u, ha, hu⟩ := exists_dvd_and_eq_mul_pow_of_dvd_factorization
    (m := b) (S := ∅) hℓ fun p _ ↦ by
      rw [hfac]
      split_ifs with hp
      · exact dvd_zero _
      · by_cases hprime : p.Prime
        · exact hval p hprime (le_of_not_gt hp)
        · simp [factorization_eq_zero_of_not_prime _ hprime]
  have ha' : a = 1 := by simpa using ha
  have hu' : b = u ^ ℓ := by simpa [ha'] using hu
  refine ⟨u, hmul.symm.trans (congrArg (m.smoothPart k * ·) hu'), fun p hp ↦ ?_⟩
  have hpb : p ∈ b.primeFactors := by simpa only [hu', primeFactors_pow _ hℓ] using hp
  by_contra! hpk
  exact (b.factorization.mem_support_iff.mp hpb) (by simp [hfac, hpk])

end Nat

/-- For odd exponent, the sign of an integer can be absorbed into the root after splitting
off the smooth part of its absolute value. -/
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
