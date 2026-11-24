/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Finite products and sums in a field

## Factoring the leading power out of a product

For `q ≠ 0` in a field,
`∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹)`. This is how the orders
of the finite classical groups, which are products of factors `q ^ k - 1`, become the normalized
values `∏ (1 - q^{-k})` of local densities.

Likewise, for `w ≠ 0` a product of powers of `w - z` is `w` to the total exponent times the
product of the corresponding powers of `1 - z * w⁻¹`; in a normed field the latter product tends to
one as `w` tends to infinity (`Finset.tendsto_prod_one_sub_mul_inv_pow`).

## Main results

* `Finset.sum_range_natCast`, `Finset.sum_range_natCast_sq`: sums of naturals and their squares in
  a division ring where `2 ≠ 0` (and, for the squares, also `3 ≠ 0`).
* `Finset.prod_pow_sub_one`: factoring `q ^ (∑ i ∈ s, f i)` out of `∏ i ∈ s, (q ^ f i - 1)`.
* `Finset.prod_sub_pow_eq_pow_sum_mul_prod_one_sub_mul_inv_pow`: factoring `w ^ (∑ z ∈ s, n z)`
  out of `∏ z ∈ s, (w - z) ^ n z`.
* `Finset.sum_range_add_mul_add_div_two`: the increments of a quadratic along a uniform grid sum to
  the increment of the quadratic from `0` to the end of the grid.
* `Finset.sum_sum_sum_erase_sub_inv_mul_sub_inv_eq_zero`: cyclic cancellation of off-diagonal
  products `(x i - x j)⁻¹ * (x i - x k)⁻¹` (`k ≠ j`) over an injective family on a finite set in any
  field.
* `Finset.sum_sum_erase_sub_inv_sq`: summing `(x i - x j)⁻¹ ^ 2` over ordered pairs of distinct
  indices counts every unordered pair twice.
-/

public section

namespace Finset

/-- **Factoring the leading power out of a product of `q ^ k - 1`.** For `q ≠ 0` in a field,
`∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹)`. -/
theorem prod_pow_sub_one {K ι : Type*} [Field K] {q : K} (hq : q ≠ 0) (s : Finset ι)
    (f : ι → ℕ) :
    ∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹) := by
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hq)]

/-- **Factoring the leading power out of a product of powers of `w - z`.** For `w ≠ 0` in a field,
`∏ z ∈ s, (w - z) ^ n z = w ^ (∑ z ∈ s, n z) * ∏ z ∈ s, (1 - z * w⁻¹) ^ n z`. -/
theorem prod_sub_pow_eq_pow_sum_mul_prod_one_sub_mul_inv_pow {K : Type*} [Field K] (s : Finset K)
    (n : K → ℕ) {w : K} (hw : w ≠ 0) :
    ∏ z ∈ s, (w - z) ^ n z = w ^ (∑ z ∈ s, n z) * ∏ z ∈ s, (1 - z * w⁻¹) ^ n z := by
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun z _ ↦ ?_
  rw [← mul_pow]
  congr 1
  field_simp

/-- The expected increments `a * u + (k * a + a / 2) * a * X` of the quadratic
`t ↦ t * u + t ^ 2 * X / 2` along the grid `k * a` sum, over `k < n`, to the increment
`n * a * u + (n * a) ^ 2 * X / 2` of the quadratic from `0` to `n * a`. -/
theorem sum_range_add_mul_add_div_two {K : Type*} [Field K] [CharZero K] (a u X : K) (n : ℕ) :
    ∑ k ∈ Finset.range n, (a * u + (k * a + a / 2) * a * X) =
      n * a * u + (n * a) ^ 2 * X / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The sum of the natural numbers below `n`, cast into a division ring where `2 ≠ 0`. -/
theorem sum_range_natCast {K : Type*} [DivisionRing K] [NeZero (2 : K)] (n : ℕ) :
    ∑ r ∈ range n, (r : K) = n * (n - 1) / 2 :=
  (eq_div_iff two_ne_zero).2 (sum_range_natCast_mul_two n)

/-- The sum of the squares of natural numbers below `n`, in a division ring where `2 ≠ 0` and
`3 ≠ 0`. -/
theorem sum_range_natCast_sq {K : Type*} [DivisionRing K] [NeZero (2 : K)] [NeZero (3 : K)]
    (n : ℕ) : ∑ r ∈ range n, (r : K) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero two_ne_zero three_ne_zero
  exact (eq_div_iff h6).2 (sum_range_natCast_sq_mul_six n)

/-- **Cyclic partial-fraction cancellation over distinct points in a field.** For an injective
family `x` on a finite set `s`, all off-diagonal products `(x i - x j)⁻¹ * (x i - x k)⁻¹` (`k ≠ j`)
cancel in triples `(i, j, k)`, in every characteristic. -/
theorem sum_sum_sum_erase_sub_inv_mul_sub_inv_eq_zero {ι K : Type*} [DecidableEq ι] [Field K]
    (s : Finset ι) {x : ι → K} (hx : Set.InjOn x s) :
    (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s.erase j, (x i - x j)⁻¹ * (x i - x k)⁻¹) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    have hstep (f : ι → ι → K) : (∑ j ∈ insert a t, ∑ k ∈ (insert a t).erase j, f j k) =
        (∑ k ∈ t, f a k) + (∑ j ∈ t, f j a) + ∑ j ∈ t, ∑ k ∈ t.erase j, f j k := by
      rw [sum_insert hat, erase_insert hat, add_assoc]
      refine congrArg _ ((sum_congr rfl fun j hj ↦ ?_).trans sum_add_distrib)
      rw [erase_insert_of_ne (ne_of_mem_of_not_mem hj hat).symm,
        sum_insert fun ha ↦ hat (mem_of_mem_erase ha)]
    rw [sum_insert hat]
    simp_rw [hstep]
    simp only [sub_self, inv_zero, zero_mul, mul_zero, sum_const_zero, zero_add, sum_add_distrib]
    rw [ih (hx.mono (subset_insert a t)), add_zero]
    have h1 : (∑ j ∈ t, ∑ k ∈ t, (x j - x a)⁻¹ * (x j - x k)⁻¹) =
        ∑ j ∈ t, ∑ k ∈ t.erase j, (x j - x a)⁻¹ * (x j - x k)⁻¹ :=
      sum_congr rfl fun j hj ↦ by rw [← add_sum_erase t _ hj]; simp
    have h2 : (∑ i ∈ t, ∑ j ∈ t, (x i - x j)⁻¹ * (x i - x a)⁻¹) =
        ∑ j ∈ t, ∑ k ∈ t.erase j, (x k - x j)⁻¹ * (x k - x a)⁻¹ :=
      sum_comm.trans <| sum_congr rfl fun j hj ↦ by rw [← add_sum_erase t _ hj]; simp
    rw [h1, h2, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun j hj ↦ ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun k hk ↦ ?_
    have hkt : k ∈ t := mem_of_mem_erase hk
    have hne {u v} (hu : u ∈ insert a t) (hv : v ∈ insert a t) (h : u ≠ v) : x u - x v ≠ 0 :=
      sub_ne_zero.2 (hx.ne hu hv h)
    have h_aj := hne (mem_insert_self a t) (mem_insert_of_mem hj) (ne_of_mem_of_not_mem hj hat).symm
    have h_ak := hne (mem_insert_self a t) (mem_insert_of_mem hkt)
      (ne_of_mem_of_not_mem hkt hat).symm
    have h_jk := hne (mem_insert_of_mem hj) (mem_insert_of_mem hkt) (ne_of_mem_erase hk).symm
    rw [← neg_sub (x a) (x j), ← neg_sub (x a) (x k), ← neg_sub (x j) (x k)]
    field_simp [h_aj, h_ak, h_jk]; ring

/-- **Symmetrizing the squared inverse gaps.** Summing `(x i - x j)⁻¹ ^ 2` over all ordered pairs
of distinct indices counts every unordered pair twice. -/
theorem sum_sum_erase_sub_inv_sq {ι K : Type*} [LinearOrder ι] [Fintype ι]
    [LocallyFiniteOrderTop ι] [LocallyFiniteOrderBot ι] [Field K] (x : ι → K) :
    ∑ i, ∑ j ∈ univ.erase i, (x i - x j)⁻¹ ^ 2 = 2 * ∑ i, ∑ j ∈ Ioi i, (x i - x j)⁻¹ ^ 2 :=
  calc ∑ i, ∑ j ∈ univ.erase i, (x i - x j)⁻¹ ^ 2
      = ∑ i, ∑ j ∈ ({i}ᶜ : Finset ι), (x i - x j)⁻¹ ^ 2 := by
        simp_rw [compl_singleton]
    _ = ∑ i, ∑ j ∈ Ioi i, ((x i - x j)⁻¹ ^ 2 + (x j - x i)⁻¹ ^ 2) :=
        (sum_sum_Ioi_add_eq_sum_sum_off_diag (fun j i : ι ↦ (x i - x j)⁻¹ ^ 2)).symm
    _ = 2 * ∑ i, ∑ j ∈ Ioi i, (x i - x j)⁻¹ ^ 2 := by
        have hsym (i j : ι) : (x j - x i)⁻¹ ^ 2 = (x i - x j)⁻¹ ^ 2 := by
          rw [← neg_sub (x i) (x j), inv_neg, neg_sq]
        simp_rw [hsym, ← two_mul, ← mul_sum]

end Finset
