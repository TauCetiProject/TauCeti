/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring

/-!
# The sawtooth sum at a root of unity

For an `N`-th root of unity `ζ` in a field in which `2` and `N` are invertible, the finite sum
of the sawtooth weights `j / N - 1 / 2` against the powers of `ζ` is

`∑_{1 ≤ j < N} (j / N - 1 / 2) ζ ^ j = (ζ + 1) / (2 (ζ - 1))`  if `ζ ≠ 1`,

and `0` if `ζ = 1`. For `ζ = e^{2π i t}` the right-hand side is `cot (π t) / (2 i)`, so the
sum is the finite Fourier expansion of the cotangent at a division point. This is the identity
behind the first trigonometric Eisenstein functions of the rational torsion group algebra
`ℚ[ℚ/ℤ]` (Connes–Marcolli, *Noncommutative geometry, quantum fields and motives*, Ch. 3,
Lemma 3.28).

The nontrivial value comes from the arithmetico-geometric sum `∑_{j < N} j ζ ^ j = N / (ζ - 1)`
(Mathlib's `sum_range_mul_geometric_add`); at `ζ = 1` the weights themselves sum to zero.

## Main results

* `TauCeti.sum_range_natCast_mul_pow_of_pow_eq_one`: `∑_{j < N} j ζ ^ j = N / (ζ - 1)` for
  `ζ ^ N = 1`, `ζ ≠ 1`.
* `TauCeti.sum_Ico_div_sub_half`: the sawtooth weights sum to zero.
* `TauCeti.sum_Ico_div_sub_half_mul_pow_of_pow_eq_one`: the sawtooth sum at a nontrivial root of
  unity.
-/

public section

namespace TauCeti

open Finset

variable {K : Type*} [Field K]

/-- The arithmetico-geometric sum at a nontrivial `N`-th root of unity:
`∑_{j < N} j ζ ^ j = N / (ζ - 1)`. -/
theorem sum_range_natCast_mul_pow_of_pow_eq_one {N : ℕ} {ζ : K} (hζN : ζ ^ N = 1)
    (hζ : ζ ≠ 1) : ∑ j ∈ range N, (j : K) * ζ ^ j = N / (ζ - 1) := by
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ
  -- the geometric sums over `[0, N)` and `[1, N]` vanish
  have hgeom : ∑ j ∈ range N, ζ ^ j = 0 := by
    have h := mul_geom_sum ζ N
    rw [hζN, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left hsub
  have hgeom' : ∑ j ∈ Icc 1 N, ζ ^ j = 0 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    simp_rw [pow_add, pow_one, ← mul_sum, hgeom, mul_zero]
  have h := sum_range_mul_geometric_add ζ N
  rw [hgeom', hζN, mul_one] at h
  rw [eq_div_iff hsub]
  have hmul : (∑ j ∈ range N, (j : K) * ζ ^ j) * (1 - ζ) =
      ∑ j ∈ range N, (j : K) * (ζ ^ j * (1 - ζ)) := by
    rw [sum_mul]
    exact sum_congr rfl fun j _ ↦ by ring
  linear_combination (-1 : K) * h + (-1 : K) * hmul

/-- The sawtooth weights `j / N - 1 / 2`, `1 ≤ j < N`, sum to zero, provided `2` is invertible
and `N` is either `0` or invertible in `K`. -/
theorem sum_Ico_div_sub_half (h2 : (2 : K) ≠ 0) {N : ℕ} (hN : (N : K) = 0 → N = 0) :
    ∑ j ∈ Ico 1 N, ((j : K) / N - 1 / 2) = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp
  have hN' : (N : K) ≠ 0 := fun h ↦ hN0.ne' (hN h)
  have hsum := sum_range_eq_add_Ico (fun j : ℕ ↦ (j : K) / N - 1 / 2) hN0
  have hid : ∑ j ∈ range N, (j : K) = N * (N - 1) / 2 := by
    have h := sum_range_id_mul_two N
    rw [eq_div_iff h2, ← Nat.cast_sum]
    exact_mod_cast (by rw [h, Nat.cast_mul, Nat.cast_sub hN0, Nat.cast_one] :
      ((∑ i ∈ range N, i) * 2 : ℕ) = (N : K) * (N - 1))
  rw [sum_sub_distrib, ← sum_div, hid, sum_const, card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  set S := ∑ j ∈ Ico 1 N, ((j : K) / N - 1 / 2)
  field_simp at hsum
  have h2NS : (2 * N : K) * S = 0 := by linear_combination -hsum
  exact (mul_eq_zero.mp h2NS).resolve_left (mul_ne_zero h2 hN')

/-- **The sawtooth sum at a nontrivial root of unity.** If `2` and `N` are invertible in `K` and
`ζ ^ N = 1`, `ζ ≠ 1`, then `∑_{1 ≤ j < N} (j / N - 1 / 2) ζ ^ j = (ζ + 1) / (2 (ζ - 1))`.
For `ζ = e^{2π i t}` the right-hand side is `cot (π t) / (2 i)`. -/
theorem sum_Ico_div_sub_half_mul_pow_of_pow_eq_one (h2 : (2 : K) ≠ 0) {N : ℕ}
    (hN' : (N : K) ≠ 0) {ζ : K} (hζN : ζ ^ N = 1) (hζ : ζ ≠ 1) :
    ∑ j ∈ Ico 1 N, ((j : K) / N - 1 / 2) * ζ ^ j = (ζ + 1) / (2 * (ζ - 1)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h ↦ hN' (by rw [h, Nat.cast_zero])
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ
  have hgeom : ∑ j ∈ range N, ζ ^ j = 0 := by
    have h := mul_geom_sum ζ N
    rw [hζN, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left hsub
  have hsum := sum_range_eq_add_Ico (fun j : ℕ ↦ ((j : K) / N - 1 / 2) * ζ ^ j) hN
  have hsplit : ∑ j ∈ range N, ((j : K) / N - 1 / 2) * ζ ^ j =
      (∑ j ∈ range N, (j : K) * ζ ^ j) / N - (∑ j ∈ range N, ζ ^ j) / 2 := by
    rw [sum_div, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hsplit, sum_range_natCast_mul_pow_of_pow_eq_one hζN hζ, hgeom] at hsum
  set S := ∑ j ∈ Ico 1 N, ((j : K) / N - 1 / 2) * ζ ^ j
  push_cast at hsum
  rw [eq_div_iff (mul_ne_zero h2 hsub)]
  field_simp at hsum
  refine mul_left_cancel₀ hN' ?_
  linear_combination -hsum

end TauCeti
