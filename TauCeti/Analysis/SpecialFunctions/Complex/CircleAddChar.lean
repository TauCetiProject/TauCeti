/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.NumberTheory.Harmonic.Defs

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.Algebra.Group.AddChar.Basic
import TauCeti.Data.ZMod.Count

/-!
# Values of the standard circle character of `ZMod N`

Mathlib's `ZMod.toCircle` sends `j : ZMod N` to `exp (2πij/N)`. At level `2n` it sends `n`
to `exp (πi) = -1`, giving conversions between products of `{±1}`-signs and `ZMod (2 * n)`
half-level shifts under `ZMod.stdAddChar`. The distance from `1` to a character value is bounded
below using the distance of the corresponding residue to zero around the circle. The resulting
reciprocal-chord and geometric-sum bounds give `N` times the harmonic number `H_{N-1}`, and hence a
logarithmic estimate, after summing over nonzero frequencies.

## Main results

* `ZMod.coe_toCircle_natCast_self`: `ZMod.toCircle (n : ZMod (2n)) = -1`.
* `ZMod.stdAddChar_natCast_self`: `ZMod.stdAddChar (n : ZMod (2n)) = -1`.
* `ZMod.prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite`: absorbing a product of `{±1}` powers into
  a `ZMod (2n)` shift inside `stdAddChar`.
* `ZMod.stdAddChar_sum_add_ite_eq_prod_pow_mul_stdAddChar`: expanding a sum of conditional `n`
  shifts inside `stdAddChar` into a product of `{±1}` powers.
* `ZMod.le_norm_stdAddChar_sub_one`: a lower bound for the distance to `1`.
* `ZMod.two_div_norm_stdAddChar_sub_one_le`: an upper bound for the reciprocal chord length.
* `ZMod.norm_sum_range_stdAddChar_mul_add_le`: a geometric-sum bound at nonzero frequency.
* `ZMod.sum_norm_sum_range_stdAddChar_mul_add_le_harmonic`: the summed geometric-sum bound,
  in terms of the harmonic number `H_{N-1}`.
* `ZMod.sum_norm_sum_range_stdAddChar_mul_add_le`: the summed geometric-sum bound, in terms of
  the logarithm of the modulus.
-/

public section

namespace ZMod

open Finset
open scoped Real

/-- The standard circle character of `ZMod (2n)` sends `n` to `exp (πi) = -1`. -/
theorem coe_toCircle_natCast_self (n : ℕ) [NeZero n] :
    ((toCircle ((n : ℕ) : ZMod (2 * n)) : Circle) : ℂ) = -1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [toCircle_natCast, Nat.cast_mul, Nat.cast_two]
  have : 2 * π * Complex.I * n / (2 * n) = π * Complex.I := by
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- The standard additive character of `ZMod (2 * n)` sends `n` to `-1`. -/
theorem stdAddChar_natCast_self (n : ℕ) [NeZero n] :
    stdAddChar ((n : ℕ) : ZMod (2 * n)) = -1 := by
  rw [stdAddChar_apply, coe_toCircle_natCast_self]

/-- Multiplying `stdAddChar x` on `ZMod (2 * n)` by a product of `{±1}` powers shifts `x` by `n`
whenever the product is `-1`. -/
theorem prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite {ι : Type*} {n : ℕ} [NeZero n]
    {u : Finset ι} {s : ι → ℤ} (hs : ∀ i ∈ u, s i = 1 ∨ s i = -1)
    (x : ZMod (2 * n)) (e : ι → ℕ) :
    (∏ i ∈ u, (s i : ℂ) ^ e i) * stdAddChar x =
      stdAddChar (x + if ∏ i ∈ u, s i ^ e i = -1 then (n : ZMod (2 * n)) else 0) := by
  have hprod : (∏ i ∈ u, s i ^ e i) = 1 ∨ (∏ i ∈ u, s i ^ e i) = -1 :=
    Finset.prod_eq_one_or_neg_one u fun i hi ↦
      (hs i hi).elim (fun h ↦ .inl (by rw [h, one_pow]))
        (fun h ↦ by rw [h]; exact neg_one_pow_eq_or ℤ (e i))
  have hcast : (∏ i ∈ u, (s i : ℂ) ^ e i) = ((∏ i ∈ u, s i ^ e i : ℤ) : ℂ) := by
    simp only [Int.cast_prod, Int.cast_pow]
  rw [hcast]
  rcases hprod with h | h <;> simp [h, AddChar.map_add_eq_mul, stdAddChar_natCast_self]

/-- Evaluating `stdAddChar` on a sum of `ZMod (2 * n)` terms shifted by `n` when `Odd (e i)` and
`s i = -1` factors out the product of `(s i : ℂ) ^ e i`. -/
theorem stdAddChar_sum_add_ite_eq_prod_pow_mul_stdAddChar {ι : Type*} {n : ℕ} [NeZero n]
    {u : Finset ι} {s : ι → ℤ} (hs : ∀ i ∈ u, s i = 1 ∨ s i = -1)
    (t : ι → ZMod (2 * n)) (e : ι → ℕ) :
    stdAddChar (∑ i ∈ u, (t i + if Odd (e i) ∧ s i = -1 then (n : ZMod (2 * n)) else 0)) =
      (∏ i ∈ u, (s i : ℂ) ^ e i) * stdAddChar (∑ i ∈ u, t i) := by
  rw [Finset.sum_add_distrib, AddChar.map_add_eq_mul, mul_comm, AddChar.map_sum_eq_prod]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rcases hs i hi with hsi | hsi
  · simp [hsi]
  · rcases Nat.even_or_odd (e i) with hm | hm
    · simp [hsi, hm.neg_one_pow, Nat.not_odd_iff_even.mpr hm]
    · simp only [hsi, hm, hm.neg_one_pow, and_self, ↓reduceIte, Int.cast_neg, Int.cast_one]
      exact stdAddChar_natCast_self n

/-- The chord from `1` to the standard character at `k` has length at least four times
the absolute value of the centered residue divided by the modulus. -/
theorem le_norm_stdAddChar_sub_one {N : ℕ} [NeZero N] (k : ZMod N) :
    4 * (k.valMinAbs.natAbs : ℝ) / N ≤ ‖stdAddChar k - 1‖ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hk : (k.valMinAbs.natAbs : ℝ) * 2 ≤ N := by
    exact_mod_cast Nat.le_div_two_iff_mul_two_le.mp k.natAbs_valMinAbs_le
  have habs : |(k.valMinAbs : ℝ)| = k.valMinAbs.natAbs := by
    simp only [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hchar : stdAddChar k = Complex.exp (Complex.I * (↑(2 * (π *
      ((k.valMinAbs : ℝ) / N))) : ℂ)) := by
    calc
      stdAddChar k = stdAddChar (k.valMinAbs : ZMod N) := by rw [coe_valMinAbs]
      _ = _ := by
        rw [stdAddChar_coe]
        push_cast
        congr 1
        ring
  have harg : |π * ((k.valMinAbs : ℝ) / N)| = π * ((k.valMinAbs.natAbs : ℝ) / N) := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_div, habs, abs_of_pos hN]
  have hhalf : |π * ((k.valMinAbs : ℝ) / N)| ≤ π / 2 := by
    rw [harg, div_eq_mul_inv π 2]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hN).mpr (by linarith)) Real.pi_pos.le
  rw [hchar, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    mul_div_cancel_left₀ _ two_ne_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = 2 * (2 / π * |π * ((k.valMinAbs : ℝ) / N)|) := by
      rw [harg]
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.mul_abs_le_abs_sin hhalf) (by norm_num)

variable {N : ℕ} [NeZero N]

/-- The reciprocal chord bound in terms of the least nonnegative representatives of a
nonzero residue and its negative. -/
theorem two_div_norm_stdAddChar_sub_one_le (k : ZMod N) (hk : k ≠ 0) :
    2 / ‖ZMod.stdAddChar k - 1‖ ≤
      (N : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
  have : NeZero k := ⟨hk⟩
  have hkpos : (0 : ℝ) < k.val := Nat.cast_pos.mpr (ZMod.val_pos.mpr hk)
  have hnegpos : (0 : ℝ) < (-k).val := Nat.cast_pos.mpr (ZMod.val_pos.mpr (neg_ne_zero.mpr hk))
  have hm : (0 : ℝ) < min (k.val : ℝ) ((-k).val : ℝ) := lt_min hkpos hnegpos
  have hc := ZMod.le_norm_stdAddChar_sub_one k
  rw [ZMod.valMinAbs_natAbs_eq_min, ← ZMod.val_neg_of_ne_zero k, Nat.cast_min] at hc
  calc
    2 / ‖ZMod.stdAddChar k - 1‖ ≤
        2 / (4 * min (k.val : ℝ) ((-k).val : ℝ) / N) :=
      div_le_div_of_nonneg_left (by norm_num)
        (div_pos (mul_pos (by norm_num) hm) (Nat.cast_pos.mpr (NeZero.pos N))) hc
    _ = (N : ℝ) / 2 * (min (k.val : ℝ) ((-k).val : ℝ))⁻¹ := by
      field_simp
      ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rcases le_total (k.val : ℝ) ((-k).val : ℝ) with h | h
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
      · rw [min_eq_right h]
        exact le_add_of_nonneg_left (by positivity)

/-- A geometric sum of standard additive-character values on an interval is bounded by
the reciprocal chord length of its nonzero frequency. -/
theorem norm_sum_range_stdAddChar_mul_add_le (a k : ZMod N) (H : ℕ)
    (hk : k ≠ 0) :
    ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      2 / ‖stdAddChar k - 1‖ := by
  have hz : stdAddChar k ≠ 1 := by
    intro h
    apply hk
    apply injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using h
  have heq : ∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N))) =
      stdAddChar (k * a) * ∑ j ∈ range H, (stdAddChar k) ^ j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [mul_add, AddChar.map_add_eq_mul]
    congr 1
    simpa only [nsmul_eq_mul, mul_comm] using
      (stdAddChar (N := N)).map_nsmul_eq_pow j k
  rw [heq, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, geom_sum_eq hz, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖stdAddChar k ^ H - 1‖ ≤ ‖stdAddChar k ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      simp only [norm_pow, ZMod.stdAddChar_apply, Circle.norm_coe, one_pow, norm_one]
      norm_num

/-- Summing the norms of interval sums of the standard additive character over nonzero
frequencies is bounded by the modulus times the harmonic number `H_{N-1}`. -/
theorem sum_norm_sum_range_stdAddChar_mul_add_le_harmonic (a : ZMod N) (H : ℕ) :
    ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      N * (harmonic (N - 1) : ℝ) := by
  have hneg : ∑ k ∈ univ.erase (0 : ZMod N), ((-k).val : ℝ)⁻¹ =
      ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ := by
    apply sum_equiv (Equiv.neg (ZMod N))
    · intro k
      simp only [mem_erase, mem_univ, and_true, Equiv.neg_apply, neg_ne_zero]
    · intro k _
      rfl
  calc
    _ ≤ ∑ k ∈ univ.erase (0 : ZMod N),
        (N : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
      apply sum_le_sum
      intro k hk
      exact (norm_sum_range_stdAddChar_mul_add_le a k H (mem_erase.mp hk).1).trans
        (two_div_norm_stdAddChar_sub_one_le k (mem_erase.mp hk).1)
    _ = (N : ℝ) * ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ := by
      rw [← mul_sum, sum_add_distrib, hneg]
      ring
    _ = _ := by rw [sum_erase _ (by simp), sum_inv_val_eq_harmonic]

/-- Summing the norms of interval sums of the standard additive character over nonzero
frequencies is bounded by the modulus times one plus its logarithm. -/
theorem sum_norm_sum_range_stdAddChar_mul_add_le (a : ZMod N) (H : ℕ) :
    ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      N * (1 + Real.log N) := by
  refine (sum_norm_sum_range_stdAddChar_mul_add_le_harmonic a H).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N))
  rw [← sum_inv_val_eq_harmonic (n := N),
    ← sum_erase (f := fun k : ZMod N ↦ (k.val : ℝ)⁻¹) (a := 0) _ (by simp)]
  exact sum_inv_val_le_one_add_log

end ZMod
