/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

/-!
# Finite products and sums in a field

## Factoring the leading power out of a product of `q ^ k - 1`

For `q ≠ 0` in a field,
`∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹)`. This is how the orders
of the finite classical groups, which are products of factors `q ^ k - 1`, become the normalized
values `∏ (1 - q^{-k})` of local densities.

## Main results

* `Finset.prod_pow_sub_one`: factoring `q ^ (∑ i ∈ s, f i)` out of `∏ i ∈ s, (q ^ f i - 1)`.
* `Finset.sum_range_add_mul_add_div_two`: the increments of a quadratic along a uniform grid sum to
  the increment of the quadratic from `0` to the end of the grid.
* `Finset.sum_sum_erase_sub_inv_mul_sub_inv_eq_zero`: cyclic cancellation of off-diagonal products
  `(x i - x j)⁻¹ * (x i - x k)⁻¹` (`k ≠ j`) over an injective family on a finite set in any field.
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

/-- The expected increments `a * u + (k * a + a / 2) * a * X` of the quadratic
`t ↦ t * u + t ^ 2 * X / 2` along the grid `k * a` sum, over `k < n`, to the increment
`n * a * u + (n * a) ^ 2 * X / 2` of the quadratic from `0` to `n * a`. -/
theorem sum_range_add_mul_add_div_two {K : Type*} [Field K] [CharZero K] (a u X : K) (n : ℕ) :
    ∑ k ∈ Finset.range n, (a * u + (k * a + a / 2) * a * X) =
      n * a * u + (n * a) ^ 2 * X / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **Cyclic partial-fraction cancellation over distinct points in a field.** For an injective
family `x` on a finite set `s`, all off-diagonal products `(x i - x j)⁻¹ * (x i - x k)⁻¹` (`k ≠ j`)
cancel in triples `(i, j, k)`, in every characteristic. -/
theorem sum_sum_erase_sub_inv_mul_sub_inv_eq_zero {ι K : Type*} [DecidableEq ι] [Field K]
    (s : Finset ι) {x : ι → K} (hx : Set.InjOn x s) :
    (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s.erase j, (x i - x j)⁻¹ * (x i - x k)⁻¹) = 0 := by
  let g : ι → ι → ι → K := fun i j k ↦ (x i - x j)⁻¹ * (x i - x k)⁻¹
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    have hstep (i : ι) : (∑ j ∈ insert a t, ∑ k ∈ (insert a t).erase j, g i j k) =
        (∑ k ∈ t, g i a k) + (∑ j ∈ t, g i j a) + ∑ j ∈ t, ∑ k ∈ t.erase j, g i j k := by
      rw [sum_insert hat, erase_insert hat, add_assoc]
      congr 1
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [erase_insert_of_ne (ne_of_mem_of_not_mem hj hat).symm,
        sum_insert fun ha ↦ hat (mem_of_mem_erase ha)]
    change (∑ i ∈ insert a t, ∑ j ∈ insert a t, ∑ k ∈ (insert a t).erase j, g i j k) = 0
    rw [sum_insert hat]
    simp_rw [hstep]
    simp only [g, sub_self, inv_zero, zero_mul, mul_zero, sum_const_zero, zero_add, sum_add_distrib]
    rw [ih (hx.mono (subset_insert a t)), add_zero]
    have h1 : (∑ j ∈ t, ∑ k ∈ t, g j a k) = ∑ j ∈ t, ∑ k ∈ t.erase j, g j a k :=
      sum_congr rfl fun j hj ↦ by rw [← add_sum_erase t _ hj]; simp [g]
    have h2 : (∑ i ∈ t, ∑ j ∈ t, g i j a) = ∑ j ∈ t, ∑ k ∈ t.erase j, g k j a :=
      sum_comm.trans <| sum_congr rfl fun j hj ↦ by rw [← add_sum_erase t _ hj]; simp [g]
    dsimp only [g] at h1 h2
    rw [h1, h2, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun j hj ↦ ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun k hk ↦ ?_
    have hkt : k ∈ t := mem_of_mem_erase hk
    have h_aj : x a - x j ≠ 0 :=
      sub_ne_zero.2 (hx.ne (mem_insert_self a t) (mem_insert_of_mem hj)
        (ne_of_mem_of_not_mem hj hat).symm)
    have h_ak : x a - x k ≠ 0 :=
      sub_ne_zero.2 (hx.ne (mem_insert_self a t) (mem_insert_of_mem hkt)
        (ne_of_mem_of_not_mem hkt hat).symm)
    have h_jk : x j - x k ≠ 0 :=
      sub_ne_zero.2 (hx.ne (mem_insert_of_mem hj) (mem_insert_of_mem hkt) (ne_of_mem_erase hk).symm)
    rw [← neg_sub (x a) (x j), ← neg_sub (x a) (x k), ← neg_sub (x j) (x k)]
    field_simp [h_aj, h_ak, h_jk]
    ring

end Finset
