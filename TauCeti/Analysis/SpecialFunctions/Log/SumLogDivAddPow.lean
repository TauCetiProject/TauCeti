/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite sums of shifted logarithmic powers

`TauCeti.sum_Ioc_log_div_add_pow_div_le` bounds the sum of
`(log (x / d) + k)^k / d` over positive integers `d ≤ x` for `x ≥ 1`.
It supplies the logarithmic estimate in the Nicolas–Tenenbaum bound for summatory ordered
divisor functions. The estimate uses Mathlib's `AntitoneOn.sum_le_integral_Ico` and
`pow_add_mul_le_add_pow`.
-/

public section

namespace TauCeti

open Finset

/-- For `x ≥ 1`, the sum of `(log (x / d) + k)^k / d` over positive integers `d ≤ x` is at
most `(log x + k + 1)^(k + 1) / (k + 1)`. This is the logarithmic sum in the induction for the
Nicolas–Tenenbaum bound, stated in Bordellès (2002), equation (1.2). -/
theorem sum_Ioc_log_div_add_pow_div_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ d ∈ Ioc 0 ⌊x⌋₊, (Real.log (x / d) + k) ^ k / d) ≤
      (Real.log x + (k + 1 : ℕ)) ^ (k + 1) / (k + 1 : ℕ) := by
  let f (t : ℝ) := (Real.log (x / t) + k) ^ k / t
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  have hN₁ : (1 : ℝ) ≤ ⌊x⌋₊ := Nat.one_le_cast.mpr hN
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx₀.le
  have hbase {t : ℝ} (ht₀ : 0 < t) (ht : t ≤ x) : 0 ≤ Real.log (x / t) + k :=
    add_nonneg (Real.log_nonneg ((le_div_iff₀ ht₀).2 (by simpa only [one_mul] using ht)))
      (Nat.cast_nonneg k)
  have ha : AntitoneOn f (Set.Icc 1 (⌊x⌋₊ : ℝ)) := by
    intro a ha b hb hab
    have ha₀ := zero_lt_one.trans_le ha.1
    have hb₀ := ha₀.trans_le hab
    have ha₁ := hbase ha₀ (ha.2.trans hNx)
    have hb₁ := hbase hb₀ (hb.2.trans hNx)
    dsimp only [f]
    gcongr
  have hsum : (∑ d ∈ Ioc 1 ⌊x⌋₊, f d) ≤ ∫ t in (1 : ℝ)..(⌊x⌋₊ : ℝ), f t := by
    have h := AntitoneOn.sum_le_integral_Ico hN (by simpa only [Nat.cast_one] using ha)
    rwa [Finset.sum_Ico_add' (fun d : ℕ ↦ f d) 1 ⌊x⌋₊ 1,
      Finset.Ico_add_one_add_one_eq_Ioc, Nat.cast_one] at h
  let F (t : ℝ) := -(Real.log x - Real.log t + k) ^ (k + 1) / (k + 1 : ℕ)
  have hint : (∫ t in (1 : ℝ)..(⌊x⌋₊ : ℝ), f t) = F ⌊x⌋₊ - F 1 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
      (Set.uIcc_of_le hN₁ ▸ ha).intervalIntegrable
    have ht₀ : 0 < t := zero_lt_one.trans_le ((Set.uIcc_of_le hN₁ ▸ ht).1)
    have hd := ((((Real.hasDerivAt_log ht₀.ne').const_sub (Real.log x)).add_const
      (k : ℝ)).pow (k + 1)).neg.div_const ((k + 1 : ℕ) : ℝ)
    refine hd.congr_deriv ?_
    simp only [f, Real.log_div hx₀.ne' ht₀.ne', Nat.add_sub_cancel]
    push_cast
    field_simp
  have hF : F ⌊x⌋₊ ≤ 0 := by
    have hpos := zero_lt_one.trans_le hN₁
    have hlog := hbase hpos hNx
    rw [Real.log_div hx₀.ne' hpos.ne'] at hlog
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg hlog _)) (by positivity)
  have hlog : 0 ≤ Real.log x + k := add_nonneg (Real.log_nonneg hx) (Nat.cast_nonneg k)
  have hpow := pow_add_mul_le_add_pow (b := 1) hlog (by positivity) (k + 1)
  rw [← insert_Ioc_add_one_left_eq_Ioc (a := 0) hN, zero_add, sum_insert (by simp), Nat.cast_one]
  calc
    _ ≤ f 1 + (F ⌊x⌋₊ - F 1) := hint ▸ add_le_add_right hsum _
    _ ≤ f 1 - F 1 := by linarith only [hF]
    _ = (Real.log x + k) ^ k + (Real.log x + k) ^ (k + 1) / (k + 1 : ℕ) := by
      simp only [f, F, Real.log_one, sub_zero, div_one, neg_div, sub_neg_eq_add]
    _ ≤ _ := by
      rw [le_div_iff₀ (by positivity)]
      push_cast at hpow ⊢
      rw [← add_assoc]
      field_simp
      simpa only [mul_one, one_mul, add_comm, mul_comm] using hpow

end TauCeti
