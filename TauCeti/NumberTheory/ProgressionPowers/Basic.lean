/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.Data.Int.Progression

/-!
# Perfect powers in primitive arithmetic progressions

For a progression of coprime initial term and common difference, a common divisor of two
terms divides the gap between their indices. Thus a prime at least the length occurs in
at most one term. If the product is a nonzero perfect power, the valuation at such a prime
in each term is divisible by the exponent.

See M. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
sums*, Lemma 3.1.
-/

public section

namespace TauCeti.ProgressionPowers

/-- The term with zero-based index `i` of the progression starting at `n` with difference `d`. -/
def term (n d : ℤ) (i : ℕ) : ℤ := n + i * d

theorem term_def (n d : ℤ) (i : ℕ) : term n d i = n + i * d := (rfl)

@[simp] theorem term_zero (n d : ℤ) : term n d 0 = n := by simp [term]

theorem term_succ (n d : ℤ) (i : ℕ) : term n d (i + 1) = term n d i + d := by
  simp [term, add_mul, add_assoc]

/-- A nontrivial primitive solution of the progression product equation
`∏ i < k, (n + i*d) = y^ℓ` with prime exponent `ℓ` and signed integer parameters. -/
@[mk_iff]
structure PrimitiveSolution (n d : ℤ) (k : ℕ) (y : ℤ) (ℓ : ℕ) : Prop where
  length_pos : 0 < k
  prime : ℓ.Prime
  gcd_eq_one : n.gcd d = 1
  prod_eq_pow : ∏ i ∈ Finset.range k, term n d i = y ^ ℓ
  mul_ne_zero : y * d ≠ 0

variable {n d y : ℤ} {k ℓ i q : ℕ}

/-- Every term of a primitive solution is nonzero. -/
theorem PrimitiveSolution.term_ne_zero (h : PrimitiveSolution n d k y ℓ) (hi : i < k) :
    term n d i ≠ 0 :=
  Finset.prod_ne_zero_iff.mp (h.prod_eq_pow ▸ pow_ne_zero _ (left_ne_zero_of_mul h.mul_ne_zero))
    i (Finset.mem_range.mpr hi)

/-- At a prime at least the progression length, the full exponent divides the valuation of
each term. The exponent itself need not be prime. -/
theorem dvd_padicValInt_term (h : n.gcd d = 1) (hy : y ≠ 0)
    (hprod : ∏ j ∈ Finset.range k, term n d j = y ^ ℓ)
    (hp : q.Prime) (hq : k ≤ q) (hi : i < k) : ℓ ∣ padicValInt q (term n d i) := by
  by_cases hqi : (q : ℤ) ∣ term n d i
  · have hnz := Finset.prod_ne_zero_iff.mp (hprod ▸ pow_ne_zero _ hy)
    have hnat := congrArg Int.natAbs hprod
    rw [Int.natAbs_prod, Int.natAbs_pow] at hnat
    have heq := congrArg (fun m : ℕ ↦ m.factorization q) hnat
    simp only [Nat.factorization_prod (fun j hj ↦ Int.natAbs_ne_zero.mpr (hnz j hj)),
      Finset.sum_apply', Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at heq
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi)] at heq
    · rw [padicValInt, Nat.multiplicity_eq_factorization hp, heq]
      exact dvd_mul_right ..
    · intro j hj hji
      apply Nat.factorization_eq_zero_of_not_dvd
      exact fun hd ↦ hji (Int.eq_of_dvd_term_of_length_le h hq (Finset.mem_range.mp hj) hi
        (Int.ofNat_dvd_left.mpr hd) hqi)
  · simp [padicValInt.eq_zero_of_not_dvd hqi]

end TauCeti.ProgressionPowers
