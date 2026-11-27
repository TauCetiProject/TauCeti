/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Conductor

/-!
# Cancellation in sums of Jacobi symbols

For a nonsquare odd denominator `m`, sums of `J(-v | m)` over initial intervals satisfy the
Pólya–Vinogradov bound. Allowing a small loss in the exponent gives a bound in terms of `n`
when `m` is the odd part of `n`. This is the off-diagonal character sum in a second-moment
estimate for theta series of quadratic twists.

The statements are those of `New.norm_sum_jacobiSym_le` and
`New.norm_sum_jacobiSym_ordCompl_le` in `Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open Finset
open scoped Nat

namespace TauCeti

/-- Pólya–Vinogradov for Jacobi symbols with nonsquare odd denominator. -/
theorem norm_sum_Icc_jacobiSym_neg_le {m : ℕ} (hm : Odd m) (hns : ¬IsSquare m) (X : ℕ) :
    ‖∑ v ∈ Icc 1 X, (jacobiSym (-(v : ℤ)) m : ℂ)‖ ≤ 2 * Real.sqrt m * (1 + Real.log m) := by
  let : NeZero m := ⟨hm.pos.ne'⟩
  let χ := jacobiChar ℂ m
  have hχ : χ ≠ 1 := fun h ↦ hns ((jacobiChar_eq_one_iff_isSquare (by norm_num) hm).mp h)
  have hneg : χ (-1) = (jacobiSym (-1) m : ℂ) := by
    simpa only [Int.cast_neg, Int.cast_one] using jacobiChar_intCast (R := ℂ) (b := m) (-1)
  have hval (v : ℕ) : (jacobiSym (-(v : ℤ)) m : ℂ) = χ (-1) * χ v := by
    rw [neg_eq_neg_one_mul, jacobiSym.mul_left, Int.cast_mul, hneg]
    simp [χ]
  calc
    _ = ‖χ (-1)‖ * ‖∑ v ∈ Icc 1 X, χ v‖ := by simp_rw [hval, ← mul_sum, norm_mul]
    _ ≤ ‖∑ v ∈ Icc 1 X, χ v‖ := mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    _ ≤ _ := χ.norm_sum_Icc_le_of_ne_one hχ X

/-- If the odd part of `n` is not a square, partial sums of its Jacobi symbol grow at most
as `n ^ (1/2 + ε)` for every `ε > 0`, uniformly in the length of the sum. -/
theorem norm_sum_Icc_jacobiSym_neg_ordCompl_two_le {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hns : ¬IsSquare (ordCompl[2] n)) (X : ℕ) :
    ‖∑ v ∈ Icc 1 X, (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)‖ ≤
      2 * (1 + 1 / ε) * (n : ℝ) ^ (1 / 2 + ε) := by
  have hn : n ≠ 0 := by rintro rfl; exact hns ⟨0, by simp⟩
  have hm : Odd (ordCompl[2] n) := Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hn)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hmn : ((ordCompl[2] n : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr (Nat.ordCompl_le n 2)
  have hlog : 1 + Real.log n ≤ (1 + 1 / ε) * (n : ℝ) ^ ε := by
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    calc
      _ ≤ (n : ℝ) ^ ε + (n : ℝ) ^ ε / ε :=
        add_le_add (Real.one_le_rpow hn₁ hε.le) (Real.log_le_rpow_div hnR.le hε)
      _ = _ := by ring
  calc
    _ ≤ 2 * Real.sqrt (↑(ordCompl[2] n : ℕ)) * (1 + Real.log (↑(ordCompl[2] n : ℕ))) :=
      norm_sum_Icc_jacobiSym_neg_le hm hns X
    _ ≤ 2 * Real.sqrt n * (1 + Real.log n) := by
      have hmR : 0 < ((ordCompl[2] n : ℕ) : ℝ) := Nat.cast_pos.mpr hm.pos
      have hm₁ : (1 : ℝ) ≤ ↑(ordCompl[2] n : ℕ) := Nat.one_le_cast.mpr hm.pos
      exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmn) (by norm_num))
        (add_le_add_right (Real.log_le_log hmR hmn) 1)
        (by linarith [Real.log_nonneg hm₁]) (by positivity)
    _ ≤ 2 * Real.sqrt n * ((1 + 1 / ε) * (n : ℝ) ^ ε) := by gcongr
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_add hnR]; ring

end TauCeti
