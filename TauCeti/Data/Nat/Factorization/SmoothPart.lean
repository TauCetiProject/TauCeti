/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.SmoothNumbers
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
  (m.primeFactorsList.filter (· < k)).prod

@[simp] theorem zero_smoothPart (k : ℕ) : (0 : ℕ).smoothPart k = 1 := by simp [smoothPart]

@[simp] theorem one_smoothPart (k : ℕ) : (1 : ℕ).smoothPart k = 1 := by simp [smoothPart]

@[simp] theorem smoothPart_mem_smoothNumbers (m k : ℕ) : m.smoothPart k ∈ smoothNumbers k :=
  prod_mem_smoothNumbers m k

theorem smoothPart_pos (m k : ℕ) : 0 < m.smoothPart k :=
  pos_of_ne_zero (smoothPart_mem_smoothNumbers m k).1

/-- The smooth part has precisely the restriction of the original prime exponents. -/
@[simp] theorem factorization_smoothPart (m k : ℕ) :
    (m.smoothPart k).factorization = m.factorization.filter (· < k) := by
  have hperm := primeFactorsList_unique (n := m.smoothPart k) rfl fun p hp ↦
    prime_of_mem_primeFactorsList (List.mem_of_mem_filter hp)
  ext p
  rw [← primeFactorsList_count_eq, ← hperm.count_eq, Finsupp.filter_apply]
  by_cases hp : p < k
  · simp [hp, primeFactorsList_count_eq]
  · simp [hp, List.count_eq_zero]

/-- The smooth part as a product of full prime powers. -/
theorem smoothPart_def (m k : ℕ) :
    m.smoothPart k = ∏ p ∈ m.primeFactors with p < k, p ^ m.factorization p := by
  calc
    _ = (m.smoothPart k).factorization.prod (· ^ ·) :=
      (prod_factorization_pow_eq_self (smoothPart_pos m k).ne').symm
    _ = _ := by simp [Finsupp.prod_filter_index]

@[simp] theorem primeFactors_smoothPart (m k : ℕ) :
    (m.smoothPart k).primeFactors = m.primeFactors.filter (· < k) := by
  rw [← support_factorization, factorization_smoothPart,
    Finsupp.support_filter, support_factorization]

theorem smoothPart_dvd (m k : ℕ) : m.smoothPart k ∣ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact dvd_zero _
  apply (factorization_le_iff_dvd (smoothPart_pos ..).ne' hm).mp
  intro p
  by_cases hp : p < k <;> simp [hp]

/-- The smooth part is multiplicative on nonzero natural numbers. -/
theorem smoothPart_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    (a * b).smoothPart k = a.smoothPart k * b.smoothPart k := by
  simpa [smoothPart, List.filter_append] using
    ((perm_primeFactorsList_mul ha hb).filter (fun p ↦ decide (p < k))).prod_eq

/-- A number equals its smooth part precisely when it is smooth. -/
@[simp] theorem smoothPart_eq_self_iff {m k : ℕ} : m.smoothPart k = m ↔ m ∈ smoothNumbers k := by
  refine ⟨fun h ↦ h ▸ smoothPart_mem_smoothNumbers m k, fun hm ↦ ?_⟩
  rw [smoothPart, List.filter_eq_self.mpr, prod_primeFactorsList hm.1]
  simpa using hm.2

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
