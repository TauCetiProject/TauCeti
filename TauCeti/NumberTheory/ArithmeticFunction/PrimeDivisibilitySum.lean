/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Additive

/-!
# Weighted finite prime divisibility sums

For a finite set `P` of natural numbers and weights `a : ℕ → R` in an additive commutative
monoid, `ArithmeticFunction.primeDivisibilitySum P a` is the arithmetic function
`n ↦ ∑ p ∈ P with p ∣ n, a p` at every positive `n`, with value `0` at `n = 0`. The guard at zero
is forced by the arithmetic-function carrier: every `p` divides `0`, so the unguarded sum would be
`∑ p ∈ P, a p` there.

When every member of `P` is prime these are the truncations to the primes of `P` of strongly
additive functions, as used in probabilistic number theory: with `a = f` for a strongly additive
`f`, the value at `n` keeps the terms `f p` of the distinct-prime representation of `f n` with
`p ∈ P`. The value at `n` only sees the primes of `P` dividing `n`
(`ArithmeticFunction.primeDivisibilitySum_eq_sum_inter_primeFactors`), so it is strongly additive
(`ArithmeticFunction.isStronglyAdditive_primeDivisibilitySum`): it adds on coprime inputs and
counts each prime power once. On the prime factors of `n` with unit weights it recovers the number
`ω n` of distinct prime factors, not the number `Ω n` counted with multiplicity
(`ArithmeticFunction.primeDivisibilitySum_primeFactors_one`).

Without primality of `P` the function is still defined, and it is linear in the weights, depends
only on the weights on `P`, and is additive in disjoint unions of `P`.
-/

public section

open scoped ArithmeticFunction.omega

namespace ArithmeticFunction

variable {R : Type*} [AddCommMonoid R]

/-- The weighted divisibility sum `n ↦ ∑ p ∈ P with p ∣ n, a p` over a finite index set `P`,
with value `0` at `n = 0`. -/
def primeDivisibilitySum (P : Finset ℕ) (a : ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else ∑ p ∈ P with p ∣ n, a p
  map_zero' := ite_eq_left rfl

/-- At a positive input the weighted divisibility sum is the sum of the weights of the members of
`P` dividing it. -/
@[simp]
theorem primeDivisibilitySum_apply (P : Finset ℕ) (a : ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    primeDivisibilitySum P a n = ∑ p ∈ P with p ∣ n, a p :=
  ite_eq_right hn

/-- The weighted divisibility sum over the empty set is the zero arithmetic function. -/
@[simp]
theorem primeDivisibilitySum_empty (a : ℕ → R) : primeDivisibilitySum ∅ a = 0 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn <;> simp [*]

/-- The weighted divisibility sum with zero weights is the zero arithmetic function. -/
@[simp]
theorem primeDivisibilitySum_zero (P : Finset ℕ) : primeDivisibilitySum P (0 : ℕ → R) = 0 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn <;> simp [*]

/-- The weighted divisibility sum depends only on the weights of the members of `P`. -/
theorem primeDivisibilitySum_congr {P : Finset ℕ} {a b : ℕ → R} (h : ∀ p ∈ P, a p = b p) :
    primeDivisibilitySum P a = primeDivisibilitySum P b := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [primeDivisibilitySum_apply _ _ hn]
  exact Finset.sum_congr rfl fun p hp => h p (Finset.mem_filter.1 hp).1

/-- The weighted divisibility sum is additive in the weights. -/
theorem primeDivisibilitySum_add (P : Finset ℕ) (a b : ℕ → R) :
    primeDivisibilitySum P (a + b) = primeDivisibilitySum P a + primeDivisibilitySum P b := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn, Finset.sum_add_distrib]

/-- The weighted divisibility sum over a disjoint union of index sets is the sum of the two
weighted divisibility sums. -/
theorem primeDivisibilitySum_union {P Q : Finset ℕ} (h : Disjoint P Q) (a : ℕ → R) :
    primeDivisibilitySum (P ∪ Q) a = primeDivisibilitySum P a + primeDivisibilitySum Q a := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter h)]

section Prime

variable {P : Finset ℕ}

/-- For a set `P` of primes, the weighted divisibility sum at `n` is the sum of the weights of the
primes of `P` dividing `n`, that is of `P ∩ n.primeFactors`. Both sides vanish at `n = 0`. -/
theorem primeDivisibilitySum_eq_sum_inter_primeFactors (hP : ∀ p ∈ P, p.Prime) (a : ℕ → R)
    (n : ℕ) : primeDivisibilitySum P a n = ∑ p ∈ P ∩ n.primeFactors, a p := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [primeDivisibilitySum_apply _ _ hn]
  congr 1
  ext p
  simp +contextual [Nat.mem_primeFactors_of_ne_zero hn, hP p]

/-- For a set `P` of primes, the weighted divisibility sum at a positive power of a prime `q` is
the weight of `q` if `q ∈ P`, and `0` otherwise: each prime power is counted once. -/
theorem primeDivisibilitySum_apply_prime_pow (hP : ∀ p ∈ P, p.Prime) (a : ℕ → R) {q k : ℕ}
    (hq : q.Prime) (hk : k ≠ 0) :
    primeDivisibilitySum P a (q ^ k) = if q ∈ P then a q else 0 := by
  rw [primeDivisibilitySum_eq_sum_inter_primeFactors hP, Nat.primeFactors_prime_pow hk hq]
  split_ifs with h
  · simp [Finset.inter_singleton_of_mem h]
  · simp [Finset.inter_singleton_of_notMem h]

/-- For a set `P` of primes, the weighted divisibility sum is strongly additive. -/
theorem isStronglyAdditive_primeDivisibilitySum (hP : ∀ p ∈ P, p.Prime) (a : ℕ → R) :
    IsStronglyAdditive (primeDivisibilitySum P a) where
  map_one := by simp [primeDivisibilitySum_eq_sum_inter_primeFactors hP]
  map_mul {m n} hm hn hmn := by
    simp only [primeDivisibilitySum_eq_sum_inter_primeFactors hP, Nat.primeFactors_mul hm hn,
      Finset.inter_union_distrib_left]
    exact Finset.sum_union (hmn.disjoint_primeFactors.mono Finset.inter_subset_right
      Finset.inter_subset_right)
  map_prime_pow hq hk := by
    rw [primeDivisibilitySum_apply_prime_pow hP a hq hk,
      ← primeDivisibilitySum_apply_prime_pow hP a hq one_ne_zero, pow_one]

/-- For a set `P` of primes, the weighted divisibility sum adds on coprime inputs, including the
coprime products `0 * 1` and `1 * 0`. -/
theorem primeDivisibilitySum_mul_of_coprime (hP : ∀ p ∈ P, p.Prime) (a : ℕ → R) {m n : ℕ}
    (h : m.Coprime n) :
    primeDivisibilitySum P a (m * n) = primeDivisibilitySum P a m + primeDivisibilitySum P a n :=
  (isStronglyAdditive_primeDivisibilitySum hP a).map_mul_of_coprime h

end Prime

/-- Over the prime factors of `n`, the weighted divisibility sum at `n` is the sum of the weights
of all these prime factors. -/
theorem primeDivisibilitySum_primeFactors (a : ℕ → R) (n : ℕ) :
    primeDivisibilitySum n.primeFactors a n = ∑ p ∈ n.primeFactors, a p := by
  rw [primeDivisibilitySum_eq_sum_inter_primeFactors (fun _ => Nat.prime_of_mem_primeFactors),
    Finset.inter_self]

/-- With unit weights over the prime factors of `n`, the weighted divisibility sum at `n` is the
number `ω n` of distinct prime factors of `n`. -/
theorem primeDivisibilitySum_primeFactors_one {S : Type*} [AddCommMonoidWithOne S] (n : ℕ) :
    primeDivisibilitySum n.primeFactors (1 : ℕ → S) n = ω n := by
  simp [primeDivisibilitySum_primeFactors, cardDistinctFactors_eq_card_primeFactors]

end ArithmeticFunction
