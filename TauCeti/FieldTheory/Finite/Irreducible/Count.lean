/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.RingTheory.Polynomial.Monic.Irreducible
import TauCeti.FieldTheory.Finite.Irreducible
import TauCeti.FieldTheory.Finite.Polynomial
import TauCeti.NumberTheory.Divisors
import TauCeti.RingTheory.Polynomial.Factors

/-!
# The number of monic irreducible polynomials over a finite field

Let `K` be a finite field with `q` elements and let `N_q(n)` be the number of monic irreducible
polynomials of degree `n` over `K` (the set `Polynomial.monicIrreduciblesOfDegree K n`). For
`n ≠ 0`, the normalized factors of `X ^ q ^ n - X` are exactly the monic irreducible polynomials
whose degree divides `n` (`Polynomial.mem_normalizedFactors_X_pow_card_pow_sub_X_iff`), each with
multiplicity one (`Polynomial.separable_X_pow_card_pow_sub_X`), and comparing degrees
(`Polynomial.sum_natDegree_toFinset_normalizedFactors`) gives
**Gauss's formula**

`∑_{d ∣ n} d N_q(d) = q ^ n` for `n ≥ 1`, hence `n N_q(n) = ∑_{d ∣ n} μ(n / d) q ^ d`

by Möbius inversion (Mathlib's `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`, reindexed by
`Nat.sum_divisorsAntidiagonal'`). The same holds for
the count `N*_q(n)` of monic irreducible polynomials of degree `n` other than `X`, which are the
monic irreducible polynomials of degree `n` with nonzero constant term
(`Polynomial.monicIrreduciblesOfDegree_sdiff_singleton_X`): `∑_{d ∣ n} d N*_q(d) = q ^ n - 1` and
`n N*_q(n) = ∑_{d ∣ n} μ(n / d) (q ^ d - 1)`.

Both counts satisfy `q ^ n - 2 q ^ ⌊n / 2⌋ ≤ n N ≤ q ^ n` for every `n`: the terms with `d < n`
of the degree sum have `d ≤ n / 2` and total at most `∑_{d ≤ n / 2} q ^ d < 2 q ^ ⌊n / 2⌋`
(`Nat.pow_sub_two_mul_pow_div_two_le_of_le_sum_divisors`).

## Main results

* `Polynomial.sum_divisors_mul_ncard_monicIrreduciblesOfDegree`: `∑_{d ∣ n} d N_q(d) = q ^ n`
  for `n ≠ 0`.
* `Polynomial.natCast_mul_ncard_monicIrreduciblesOfDegree`:
  `n N_q(n) = ∑_{d ∣ n} μ(n / d) q ^ d` in `ℤ`.
* `Polynomial.sum_divisors_mul_ncard_monicIrreduciblesOfDegree_sdiff_singleton_X`:
  `∑_{d ∣ n} d N*_q(d) = q ^ n - 1` for every `n`, where `N*_q(d)` counts the monic irreducible
  polynomials of degree `d` other than `X`.
* `Polynomial.natCast_mul_ncard_monicIrreduciblesOfDegree_sdiff_singleton_X`:
  `n N*_q(n) = ∑_{d ∣ n} μ(n / d) (q ^ d - 1)` in `ℤ` for every `n`.
* `Polynomial.mul_ncard_monicIrreduciblesOfDegree_le`,
  `Polynomial.pow_sub_two_mul_pow_le_mul_ncard_monicIrreduciblesOfDegree` and their
  `_sdiff_singleton_X` forms: `n N ≤ q ^ n` in `ℕ` and `q ^ n - 2 q ^ ⌊n / 2⌋ ≤ n N` in `ℤ`, for
  every `n`.

## References

* R. Lidl, H. Niederreiter, *Finite fields*, Chapter 3, Theorem 3.25.
-/

public section

open Finset UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

namespace Polynomial

variable {K : Type*} [Field K] [Finite K]

/-- **Gauss's formula.** Over a field with `q` elements, `∑_{d ∣ n} d N_q(d) = q ^ n` for
`n ≠ 0`, where `N_q(d)` is the number of monic irreducible polynomials of degree `d`. -/
theorem sum_divisors_mul_ncard_monicIrreduciblesOfDegree {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, d * (monicIrreduciblesOfDegree K d).ncard = Nat.card K ^ n := by
  classical
  have hq : 1 < Nat.card K ^ n := Nat.one_lt_pow hn Finite.one_lt_card
  set S := (normalizedFactors (X ^ Nat.card K ^ n - X : K[X])).toFinset
  -- The distinct normalized factors have degrees summing to `q ^ n`, by separability.
  have hdeg : ∑ g ∈ S, g.natDegree = Nat.card K ^ n := by
    rw [sum_natDegree_toFinset_normalizedFactors (separable_X_pow_card_pow_sub_X hn).squarefree,
      natDegree_X_pow_sub_X hq]
  have hS : ∀ d ∈ n.divisors, monicIrreduciblesOfDegree K d = ↑{g ∈ S | g.natDegree = d} := by
    intro d hd
    ext g
    simp only [mem_monicIrreduciblesOfDegree_iff, coe_filter, Set.mem_ofPred_eq, S,
      Multiset.mem_toFinset, mem_normalizedFactors_X_pow_card_pow_sub_X_iff hn]
    exact ⟨fun ⟨hm, hi, hg⟩ ↦ ⟨⟨hm, hi, hg ▸ Nat.dvd_of_mem_divisors hd⟩, hg⟩,
      fun ⟨⟨hm, hi, _⟩, hg⟩ ↦ ⟨hm, hi, hg⟩⟩
  rw [← hdeg, ← sum_fiberwise_of_maps_to (t := n.divisors)
    (g := natDegree) fun g hg ↦ Nat.mem_divisors.mpr
      ⟨((mem_normalizedFactors_X_pow_card_pow_sub_X_iff hn).mp (Multiset.mem_toFinset.mp hg)).2.2,
        hn⟩]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [hS d hd, Set.ncard_coe_finset, sum_const_nat fun g hg ↦ (mem_filter.mp hg).2, mul_comm]

/-- The degree sum for `N*_q`, in the form `∑_{d ∣ n} d N*_q(d) + 1 = q ^ n`. -/
private theorem sum_divisors_mul_ncard_sdiff_singleton_X_add_one (n : ℕ) :
    ∑ d ∈ n.divisors, d * (monicIrreduciblesOfDegree K d \ {X}).ncard + 1 = Nat.card K ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- Removing `X` changes only the term of the divisor `1`, by one.
  have hcorr : ∑ d ∈ n.divisors, d * (if d = 1 then 1 else 0) = 1 := by
    simp [mul_ite, sum_ite_eq', Nat.one_mem_divisors.mpr hn]
  rw [← sum_divisors_mul_ncard_monicIrreduciblesOfDegree hn, ← hcorr, ← sum_add_distrib]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [← mul_add, ncard_monicIrreduciblesOfDegree_sdiff_singleton_X_add]

/-- Over a field with `q` elements, `∑_{d ∣ n} d N*_q(d) = q ^ n - 1`, where `N*_q(d)` is the
number of monic irreducible polynomials of degree `d` other than `X`. At `n = 0` both sides
are `0`. -/
theorem sum_divisors_mul_ncard_monicIrreduciblesOfDegree_sdiff_singleton_X (n : ℕ) :
    ∑ d ∈ n.divisors, d * (monicIrreduciblesOfDegree K d \ {X}).ncard = Nat.card K ^ n - 1 :=
  Nat.eq_sub_of_add_eq (sum_divisors_mul_ncard_sdiff_singleton_X_add_one n)

/-- **Gauss's formula**, inverted: over a field with `q` elements,
`n N_q(n) = ∑_{d ∣ n} μ(n / d) q ^ d` in `ℤ` for every `n`. -/
theorem natCast_mul_ncard_monicIrreduciblesOfDegree (n : ℕ) :
    (n * (monicIrreduciblesOfDegree K n).ncard : ℤ) =
      ∑ d ∈ n.divisors, μ (n / d) * (Nat.card K : ℤ) ^ d := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- Mathlib's inversion sums over the factor pairs `(n / d, d)` of `n`.
  simp only [← Nat.sum_divisorsAntidiagonal' fun i j ↦ μ i * (Nat.card K : ℤ) ^ j]
  have := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun d ↦ (d : ℤ) * (monicIrreduciblesOfDegree K d).ncard)
    (g := fun d ↦ (Nat.card K : ℤ) ^ d)).mp (fun m hm ↦ by
      exact_mod_cast sum_divisors_mul_ncard_monicIrreduciblesOfDegree (K := K) hm.ne') n
    (Nat.pos_of_ne_zero hn)
  simpa only [Int.cast_id] using this.symm

/-- Over a field with `q` elements, `n N*_q(n) = ∑_{d ∣ n} μ(n / d) (q ^ d - 1)` in `ℤ` for every
`n`, where `N*_q(n)` counts the monic irreducible polynomials of degree `n` other than `X`. -/
theorem natCast_mul_ncard_monicIrreduciblesOfDegree_sdiff_singleton_X (n : ℕ) :
    (n * (monicIrreduciblesOfDegree K n \ {X}).ncard : ℤ) =
      ∑ d ∈ n.divisors, μ (n / d) * ((Nat.card K : ℤ) ^ d - 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [← Nat.sum_divisorsAntidiagonal' fun i j ↦ μ i * ((Nat.card K : ℤ) ^ j - 1)]
  have := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun d ↦ (d : ℤ) * (monicIrreduciblesOfDegree K d \ {X}).ncard)
    (g := fun d ↦ (Nat.card K : ℤ) ^ d - 1)).mp (fun m _ ↦ by
      rw [eq_sub_iff_add_eq]
      exact_mod_cast sum_divisors_mul_ncard_sdiff_singleton_X_add_one (K := K) m) n
    (Nat.pos_of_ne_zero hn)
  simpa only [Int.cast_id] using this.symm

/-- Over a field with `q` elements, `n N_q(n) ≤ q ^ n` for every `n`. -/
theorem mul_ncard_monicIrreduciblesOfDegree_le (n : ℕ) :
    n * (monicIrreduciblesOfDegree K n).ncard ≤ Nat.card K ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (single_le_sum (f := fun d ↦ d * (monicIrreduciblesOfDegree K d).ncard)
    (fun _ _ ↦ Nat.zero_le _) (Nat.mem_divisors_self n hn)).trans
      (sum_divisors_mul_ncard_monicIrreduciblesOfDegree hn).le

/-- Over a field with `q` elements, `n N*_q(n) ≤ q ^ n` for every `n`, where `N*_q(n)` counts the
monic irreducible polynomials of degree `n` other than `X`. -/
theorem mul_ncard_monicIrreduciblesOfDegree_sdiff_singleton_X_le (n : ℕ) :
    n * (monicIrreduciblesOfDegree K n \ {X}).ncard ≤ Nat.card K ^ n :=
  (Nat.mul_le_mul_left n (Set.ncard_sdiff_singleton_le _ X)).trans
    (mul_ncard_monicIrreduciblesOfDegree_le n)

/-- Over a field with `q` elements, `q ^ n - 2 q ^ (n / 2) ≤ n N_q(n)` in `ℤ` for every `n`, with
`n / 2` the natural-number quotient. -/
theorem pow_sub_two_mul_pow_le_mul_ncard_monicIrreduciblesOfDegree (n : ℕ) :
    ((Nat.card K : ℤ) ^ n - 2 * (Nat.card K : ℤ) ^ (n / 2)) ≤
      n * (monicIrreduciblesOfDegree K n).ncard := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact_mod_cast Nat.pow_sub_two_mul_pow_div_two_le_of_le_sum_divisors
    (f := fun d ↦ d * (monicIrreduciblesOfDegree K d).ncard)
    (fun d _ ↦ mul_ncard_monicIrreduciblesOfDegree_le d)
    (Nat.le_succ_of_le (sum_divisors_mul_ncard_monicIrreduciblesOfDegree hn).ge)

/-- Over a field with `q` elements, `q ^ n - 2 q ^ (n / 2) ≤ n N*_q(n)` in `ℤ` for every `n`, with
`n / 2` the natural-number quotient, where `N*_q(n)` counts the monic irreducible polynomials of
degree `n` other than `X`. -/
theorem pow_sub_two_mul_pow_le_mul_ncard_monicIrreduciblesOfDegree_sdiff_singleton_X (n : ℕ) :
    ((Nat.card K : ℤ) ^ n - 2 * (Nat.card K : ℤ) ^ (n / 2)) ≤
      n * (monicIrreduciblesOfDegree K n \ {X}).ncard := by
  exact_mod_cast Nat.pow_sub_two_mul_pow_div_two_le_of_le_sum_divisors
    (f := fun d ↦ d * (monicIrreduciblesOfDegree K d \ {X}).ncard)
    (fun d _ ↦ mul_ncard_monicIrreduciblesOfDegree_sdiff_singleton_X_le d)
    (sum_divisors_mul_ncard_sdiff_singleton_X_add_one (K := K) n).ge

end Polynomial
