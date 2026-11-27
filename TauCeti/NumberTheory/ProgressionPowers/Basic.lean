/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Data.Int.Progression

/-!
# Perfect powers in primitive arithmetic progressions

For a progression of coprime initial term and common difference, a common divisor of two
terms divides the gap between their indices. Thus a prime at least the length occurs in
at most one term. If the product is a perfect power, the valuation at such a prime
in each term is divisible by the exponent.

See M. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
sums*, Lemma 3.1.
-/

public section

namespace TauCeti.ProgressionPowers

/-- A nontrivial primitive solution of the progression product equation
`∏ i < k, (n + i*d) = y^ℓ` with prime exponent `ℓ` and signed integer parameters. -/
@[mk_iff]
structure PrimitiveSolution (n d : ℤ) (k : ℕ) (y : ℤ) (ℓ : ℕ) : Prop where
  length_pos : 0 < k
  prime : ℓ.Prime
  gcd_eq_one : n.gcd d = 1
  prod_eq_pow : ∏ i ∈ Finset.range k, n.progressionTerm d i = y ^ ℓ
  mul_ne_zero : y * d ≠ 0

variable {n d y : ℤ} {k ℓ i q : ℕ}

/-- Every term of a primitive solution is nonzero. -/
theorem PrimitiveSolution.term_ne_zero (h : PrimitiveSolution n d k y ℓ) (hi : i < k) :
    n.progressionTerm d i ≠ 0 :=
  Finset.prod_ne_zero_iff.mp (h.prod_eq_pow ▸ pow_ne_zero _ (left_ne_zero_of_mul h.mul_ne_zero))
    i (Finset.mem_range.mpr hi)

/-- At a prime at least the progression length, the full exponent divides the valuation of
each term. This also holds for a zero product, using the library's zero valuation at zero. -/
theorem dvd_padicValInt_term (h : n.gcd d = 1)
    (hprod : ∏ j ∈ Finset.range k, n.progressionTerm d j = y ^ ℓ)
    (hp : q.Prime) (hq : k ≤ q) (hi : i < k) : ℓ ∣ padicValInt q (n.progressionTerm d i) := by
  by_cases hqi : (q : ℤ) ∣ n.progressionTerm d i
  · have eq_index (j : ℕ) (hj : j ∈ Finset.range k) (hqj : (q : ℤ) ∣ n.progressionTerm d j) :
        j = i :=
      Int.eq_of_dvd_term_of_length_le h hq (Finset.mem_range.mp hj) hi
        (by simpa only [Int.progressionTerm_def] using hqj)
        (by simpa only [Int.progressionTerm_def] using hqi)
    by_cases hzero : ∏ j ∈ Finset.range k, n.progressionTerm d j = 0
    · obtain ⟨j, hj, hjzero⟩ := Finset.prod_eq_zero_iff.mp hzero
      have hji := eq_index j hj (hjzero ▸ dvd_zero _)
      subst j
      rw [hjzero, padicValInt.zero]
      exact dvd_zero _
    · have hnz := Finset.prod_ne_zero_iff.mp hzero
      have hnat := congrArg Int.natAbs hprod
      rw [Int.natAbs_prod, Int.natAbs_pow] at hnat
      have heq := congrArg (fun m : ℕ ↦ m.factorization q) hnat
      simp only [Nat.factorization_prod_apply (fun j hj ↦ Int.natAbs_ne_zero.mpr (hnz j hj)),
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at heq
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi)] at heq
      · rw [padicValInt, Nat.multiplicity_eq_factorization hp, heq]
        exact dvd_mul_right ..
      · intro j hj hji
        exact Nat.factorization_eq_zero_of_not_dvd fun hd ↦
          hji (eq_index j hj (Int.ofNat_dvd_left.mpr hd))
  · rw [padicValInt.eq_zero_of_not_dvd hqi]
    exact dvd_zero _

end TauCeti.ProgressionPowers
