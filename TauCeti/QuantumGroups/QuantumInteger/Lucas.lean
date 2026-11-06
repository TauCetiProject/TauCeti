/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Binomial
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic

/-!
# The quantum Lucas theorem

This file proves the quantum Lucas theorem for the symmetric quantum binomial coefficients
`[n choose k]_q` of `TauCeti.quantumBinomial` at a root of unity: if `q²` is a primitive `l`-th
root of unity in a field and `n₀, k₀ < l`, then `[n₁ l + n₀ choose k₁ l + k₀]_q` equals

`q^(l(k₁ n₀ - n₁ k₀) + (n₁ + 1) k₁ l²) [n₀ choose k₀]_q (n₁ choose k₁)`.

The power of `q` is a sign `±1`, which cannot be dropped: at `q = i` it is `-1` for
`[3 choose 2]_i`. The theorem reduces every quantum binomial at a root of unity to one with
arguments below `l` times an ordinary binomial coefficient, which is what controls divided powers
specialized at a root of unity in the construction of quantum Frobenius. As a corollary,
`[n choose k]_q = 0` when `l ∣ n` and `l ∤ k`.

The proof goes through the generating polynomial of a row. By Cauchy's binomial theorem, the
coefficient of `X ^ k` in `∏_{j < n} (1 + q^(2j) X)` is `q^(k(n-1)) [n choose k]_q`. When `q²` is a
primitive `l`-th root of unity the row `l` collapses to `1 + q^(l(l-1)) X^l`, the factors are
periodic of period `l`, and comparing coefficients in
`(1 + q^(l(l-1)) X^l)^n₁ ∏_{j < n₀} (1 + q^(2j) X)` gives the theorem.

## Main results

* `TauCeti.coeff_prod_range_one_add_C_mul_X`: Cauchy's binomial theorem, in coefficient form.
* `TauCeti.quantumBinomial_mul_add_mul_add`: the quantum Lucas theorem.
* `TauCeti.quantumBinomial_eq_zero_of_dvd_of_not_dvd`: the vanishing of `[n choose k]_q` for
  `l ∣ n` and `l ∤ k`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Chapter 34, for the
  Gaussian binomials at roots of unity.
* K. McGerty, *Hall algebras and quantum Frobenius*, arXiv math/0601150, Lemma 2.7, for the
  quantum Lucas theorem.
* V. Kac and P. Cheung, *Quantum Calculus*, Universitext, Chapter 5, for Gauss's (Cauchy's)
  binomial formula.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {K : Type*} [Field K]

/-- The defining Pascal rule of `quantumBinomial` with integer exponents,
`[n+1 choose k+1]_q = q^(n-k) [n choose k]_q + q^(-(k+1)) [n choose k+1]_q`; for `n < k` both
sides vanish. -/
private theorem quantumBinomial_succ_succ_zpow {q : K} (n k : ℕ) :
    quantumBinomial q (n + 1) (k + 1) =
      q ^ ((n : ℤ) - k) * quantumBinomial q n k +
        q ^ (-((k : ℤ) + 1)) * quantumBinomial q n (k + 1) := by
  rcases le_or_gt k n with hk | hk
  · rw [quantumBinomial_succ_succ, ← zpow_natCast, Nat.cast_sub hk, zpow_neg, ← inv_zpow,
      ← zpow_natCast, Nat.cast_add_one]
  · simp [quantumBinomial_eq_zero_of_lt q hk,
      quantumBinomial_eq_zero_of_lt q (hk.trans k.lt_succ_self),
      quantumBinomial_eq_zero_of_lt q (Nat.succ_lt_succ hk)]

/-- **Cauchy's binomial theorem**, in coefficient form: for `q ≠ 0`, the coefficient of `X ^ k`
in `∏_{j < n} (1 + q^(2j) X)` is `q^(k(n-1)) [n choose k]_q`. -/
theorem coeff_prod_range_one_add_C_mul_X {q : K} (hq : q ≠ 0) (n k : ℕ) :
    (∏ j ∈ range n, (1 + C ((q ^ 2) ^ j) * X)).coeff k =
      q ^ ((k : ℤ) * (n - 1)) * quantumBinomial q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [coeff_one]
  | succ n ih =>
    rw [prod_range_succ, mul_add, mul_one, ← mul_assoc, mul_comm _ (C _), coeff_add]
    cases k with
    | zero => rw [coeff_mul_X_zero, ih]; simp
    | succ k =>
      rw [coeff_mul_X, coeff_C_mul, ih, ih, quantumBinomial_succ_succ_zpow]
      have h₁ : q ^ (((k + 1 : ℕ) : ℤ) * ((n + 1 : ℕ) - 1)) * q ^ ((n : ℤ) - k) =
          (q ^ 2) ^ n * q ^ ((k : ℤ) * (n - 1)) := by
        rw [← zpow_add₀ hq, ← pow_mul, ← zpow_natCast _ (2 * n), ← zpow_add₀ hq]
        push_cast
        ring_nf
      have h₂ : q ^ (((k + 1 : ℕ) : ℤ) * ((n + 1 : ℕ) - 1)) * q ^ (-((k : ℤ) + 1)) =
          q ^ (((k + 1 : ℕ) : ℤ) * (n - 1)) := by
        rw [← zpow_add₀ hq]
        push_cast
        ring_nf
      linear_combination -quantumBinomial q n k * h₁ - quantumBinomial q n (k + 1) * h₂

/-- If `q²` is a primitive `l`-th root of unity, the generating polynomial of the `l`-th row is
`∏_{j < l} (1 + q^(2j) X) = 1 + q^(l(l-1)) X^l`. -/
private theorem prod_range_one_add_C_mul_X_of_isPrimitiveRoot {q : K} {l : ℕ}
    (hq : IsPrimitiveRoot (q ^ 2) l) (hl : 0 < l) :
    ∏ j ∈ range l, (1 + C ((q ^ 2) ^ j) * X) = 1 + C (q ^ ((l : ℤ) * (l - 1))) * X ^ l := by
  have hq₀ := ne_zero_pow two_ne_zero (hq.ne_zero hl.ne')
  -- The factors `1 + q^(2j) X` are, up to the scalars `q^(2j)`, the linear factors of `X^l ± 1`.
  have hfac : ∏ j ∈ range l, (1 + C ((q ^ 2) ^ j) * X) =
      C (∏ j ∈ range l, (q ^ 2) ^ j) * (X ^ l - C ((-1) ^ l)) := by
    rw [X_pow_sub_C_eq_prod hq.inv hl rfl, map_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    have hj : (q ^ 2) ^ j ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hq₀)
    rw [inv_pow, mul_neg_one, map_neg, sub_neg_eq_add, mul_add, ← C_mul, mul_inv_cancel₀ hj, C_1]
    ring
  ext k
  rw [coeff_add, coeff_one, coeff_C_mul_X_pow]
  rcases Nat.lt_trichotomy k l with hk | rfl | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · rw [coeff_prod_range_one_add_C_mul_X hq₀]
      simp [hl.ne]
    · rw [hfac, coeff_C_mul, coeff_sub, coeff_X_pow, coeff_C]
      simp [hk.ne, hk₀.ne']
  · rw [coeff_prod_range_one_add_C_mul_X hq₀]
    simp [hl.ne']
  · rw [coeff_prod_range_one_add_C_mul_X hq₀, quantumBinomial_eq_zero_of_lt q hk]
    simp [hk.ne', (hl.trans hk).ne']

/-- If `q^(2l) = 1`, the generating polynomial of the row `n₁ l + n₀` factors as the `n₁`-th power
of that of the row `l` times that of the row `n₀`. -/
private theorem prod_range_mul_add_of_pow_eq_one {q : K} {l : ℕ} (hq : (q ^ 2) ^ l = 1)
    (n₁ n₀ : ℕ) :
    ∏ j ∈ range (n₁ * l + n₀), (1 + C ((q ^ 2) ^ j) * X) =
      (∏ j ∈ range l, (1 + C ((q ^ 2) ^ j) * X)) ^ n₁ *
        ∏ j ∈ range n₀, (1 + C ((q ^ 2) ^ j) * X) := by
  induction n₁ with
  | zero => simp
  | succ n₁ ih =>
    rw [add_mul, one_mul, add_comm (n₁ * l) l, add_assoc, prod_range_add]
    simp only [pow_add, hq, one_mul]
    rw [ih, pow_succ]
    ring

/-- The exponent of `q` in the quantum Lucas theorem: if `q^(2l) = 1`, multiplying
`q^((k₁ l + k₀)(n₁ l + n₀ - 1))` by `q^(l(k₁ n₀ - n₁ k₀) + (n₁ + 1) k₁ l²)` gives
`q^(l(l-1)k₁) q^(k₀(n₀-1))`, since the two exponents differ by a multiple of `2l`. -/
private theorem zpow_mul_zpow_lucas {q : K} (hq₀ : q ≠ 0) {l : ℕ} (hq : (q ^ 2) ^ l = 1)
    (n₁ n₀ k₁ k₀ : ℕ) :
    q ^ (((k₁ * l + k₀ : ℕ) : ℤ) * ((n₁ * l + n₀ : ℕ) - 1)) *
        q ^ ((l : ℤ) * (k₁ * n₀ - n₁ * k₀) + (n₁ + 1) * k₁ * l ^ 2) =
      (q ^ ((l : ℤ) * (l - 1))) ^ k₁ * q ^ ((k₀ : ℤ) * (n₀ - 1)) := by
  have h2l : q ^ (2 * l : ℤ) = 1 := by
    rw [show (2 * l : ℤ) = ((2 * l : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, hq]
  rw [← zpow_natCast (q ^ ((l : ℤ) * (l - 1))) k₁, ← zpow_mul, ← zpow_add₀ hq₀, ← zpow_add₀ hq₀,
    show ((k₁ * l + k₀ : ℕ) : ℤ) * ((n₁ * l + n₀ : ℕ) - 1) +
        ((l : ℤ) * (k₁ * n₀ - n₁ * k₀) + (n₁ + 1) * k₁ * l ^ 2) =
      2 * l * (k₁ * n₀ + n₁ * k₁ * l) + ((l : ℤ) * (l - 1) * k₁ + k₀ * (n₀ - 1)) by
        push_cast; ring,
    zpow_add₀ hq₀, zpow_mul, h2l, one_zpow, one_mul]

/-- **The quantum Lucas theorem**. If `q²` is a primitive `l`-th root of unity, `n₀ < l` and
`k₀ < l`, then `[n₁ l + n₀ choose k₁ l + k₀]_q` equals
`q^(l(k₁ n₀ - n₁ k₀) + (n₁ + 1) k₁ l²) [n₀ choose k₀]_q (n₁ choose k₁)`.
The power of `q` is a sign `±1`, and it is `1` when `q` has odd order. -/
theorem quantumBinomial_mul_add_mul_add {q : K} {l : ℕ} (hq : IsPrimitiveRoot (q ^ 2) l)
    (n₁ k₁ : ℕ) {n₀ k₀ : ℕ} (hn₀ : n₀ < l) (hk₀ : k₀ < l) :
    quantumBinomial q (n₁ * l + n₀) (k₁ * l + k₀) =
      q ^ ((l : ℤ) * (k₁ * n₀ - n₁ * k₀) + (n₁ + 1) * k₁ * l ^ 2) *
        quantumBinomial q n₀ k₀ * n₁.choose k₁ := by
  have hl : 0 < l := by omega
  have hq₀ := ne_zero_pow two_ne_zero (hq.ne_zero hl.ne')
  -- Compare the coefficients of `X ^ (k₁ l + k₀)` in `(1 + c X^l)^n₁ * g`: only the term
  -- `c^k₁ (n₁ choose k₁) X^(k₁ l)` of the binomial expansion contributes, since `g` has degree
  -- at most `n₀ < l`.
  have key := coeff_prod_range_one_add_C_mul_X hq₀ (n₁ * l + n₀) (k₁ * l + k₀)
  rw [prod_range_mul_add_of_pow_eq_one hq.pow_eq_one,
    prod_range_one_add_C_mul_X_of_isPrimitiveRoot hq hl, add_comm (1 : K[X]), add_pow, sum_mul,
    finsetSum_coeff] at key
  have hexp := zpow_mul_zpow_lucas hq₀ hq.pow_eq_one n₁ n₀ k₁ k₀
  set c : K := q ^ ((l : ℤ) * (l - 1))
  set g : K[X] := ∏ j ∈ range n₀, (1 + C ((q ^ 2) ^ j) * X)
  have hg : ∀ j, n₀ < j → g.coeff j = 0 := fun j hj => by
    rw [coeff_prod_range_one_add_C_mul_X hq₀, quantumBinomial_eq_zero_of_lt q hj, mul_zero]
  have hterm (m : ℕ) : (C c * X ^ l) ^ m * 1 ^ (n₁ - m) * (n₁.choose m : K[X]) * g =
      C (c ^ m * n₁.choose m) * (X ^ (l * m) * g) := by
    rw [one_pow, mul_one, mul_pow, ← C_pow, ← pow_mul, ← C_eq_natCast, C_mul]
    ring
  simp only [hterm, coeff_C_mul, coeff_X_pow_mul'] at key
  rw [sum_eq_single k₁, mul_comm l k₁, ite_eq_left (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, coeff_prod_range_one_add_C_mul_X hq₀] at key
  · -- Solve `key` for `[n₁ l + n₀ choose k₁ l + k₀]_q`.
    refine mul_left_cancel₀ (zpow_ne_zero (((k₁ * l + k₀ : ℕ) : ℤ) * ((n₁ * l + n₀ : ℕ) - 1)) hq₀)
      ?_
    linear_combination -key - quantumBinomial q n₀ k₀ * (n₁.choose k₁ : K) * hexp
  · intro m _ hm
    rcases Nat.lt_or_gt_of_ne hm with hm | hm
    · have : l * (m + 1) ≤ l * k₁ := Nat.mul_le_mul_left l hm
      rw [mul_comm k₁ l, ite_eq_left (by nlinarith), hg _ (by rw [mul_add] at this; omega),
        mul_zero]
    · have : l * (k₁ + 1) ≤ l * m := Nat.mul_le_mul_left l hm
      rw [mul_comm k₁ l, ite_eq_right (by rw [mul_add] at this; omega), mul_zero]
  · intro hk
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk), Nat.cast_zero, mul_zero, zero_mul]

/-- If `q²` is a primitive `l`-th root of unity, then `[n choose k]_q = 0` whenever `l ∣ n` and
`l ∤ k`. -/
theorem quantumBinomial_eq_zero_of_dvd_of_not_dvd {q : K} {l : ℕ}
    (hq : IsPrimitiveRoot (q ^ 2) l) {n k : ℕ} (hn : l ∣ n) (hk : ¬l ∣ k) :
    quantumBinomial q n k = 0 := by
  obtain ⟨n₁, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · exact quantumBinomial_eq_zero_of_lt q (by simp_all [Nat.pos_iff_ne_zero])
  have hk₀ : 0 < k % l := Nat.pos_of_ne_zero fun h => hk (Nat.dvd_of_mod_eq_zero h)
  rw [← Nat.div_add_mod' k l, mul_comm l n₁, ← add_zero (n₁ * l),
    quantumBinomial_mul_add_mul_add hq n₁ (k / l) hl (Nat.mod_lt k hl),
    quantumBinomial_eq_zero_of_lt q hk₀]
  simp

/-- At `q = i`, where `q² = -1` has order `2`, the quantum Lucas theorem gives
`[3 choose 2]_i = i^10 [1 choose 0]_i (1 choose 1) = -1`; a sign-free formula would give `1`. -/
example : quantumBinomial Complex.I 3 2 = -1 := by
  have hq : IsPrimitiveRoot (Complex.I ^ 2) 2 := by
    simpa using IsPrimitiveRoot.neg_one (R := ℂ) 0 (by norm_num)
  have := quantumBinomial_mul_add_mul_add hq 1 1 (n₀ := 1) (k₀ := 0) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- At `q = -1`, where `q² = 1` has order `1`, `[2 choose 1]_{-1} = (-1)^3 (2 choose 1) = -2`. -/
example : quantumBinomial (-1 : ℚ) 2 1 = -2 := by
  have hq : IsPrimitiveRoot ((-1 : ℚ) ^ 2) 1 := by simp
  have := quantumBinomial_mul_add_mul_add hq 2 1 (n₀ := 0) (k₀ := 0) (by norm_num) (by norm_num)
  norm_num at this
  exact this

end TauCeti
