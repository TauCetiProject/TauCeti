/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# Replacing caps in Frobenius averages of Riesz remainders

In the character expansion of a Frobenius-restricted Riesz sum, a cap `w` contributes a
remainder at `a / w`, multiplied by `w` and by a character value. Where the cap is small,
a linear bound for the remainder at large arguments makes the contribution negligible.
Where the cap is close to `b`, a Lipschitz bound allows replacement by `b`. The latter
terms, unlike the original ones, can then be averaged by character orthogonality.

This is the cap-replacement step of Levent Alpöge's `Deduction.CharacterBalanceMoves.core`
in [`ChCore.lean`][ch-core]. The estimate uses the maximum of the two costs, since each
summand is subject to only one of them.

[ch-core]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean
-/

public section

open Finset
open scoped BigOperators

namespace TauCeti

/-- In an average of scaled character remainders, discard the terms outside `T` and replace
all caps in `T` by `b`. A thin argument above `X` costs at most `S * a`, and a thick cap within
`D` of `b` costs at most `3 * (a / b) * D`, per character. Both averages use the original
normalization, not the size of `T`. -/
theorem norm_expect_sum_scaledRemainder_sub_thick_le
    {ι χ : Type*} [DecidableEq ι] (J T : Finset ι) (C : Finset χ)
    (phase : ι → χ → ℂ) (R : χ → ℝ → ℂ) (w : ι → ℝ)
    {a b D X S : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hphase : ∀ g ∈ J, ∀ i ∈ C, ‖phase g i‖ ≤ 1)
    (hthick : ∀ g ∈ J, g ∈ T → w g ∈ Set.Icc b (b + D))
    (hthin : ∀ g ∈ J, g ∉ T → 0 ≤ w g ∧ (0 < w g → X ≤ a / w g))
    (hsaving : ∀ i ∈ C, ∀ y ≥ X, ‖R i y‖ ≤ S * y)
    (hvariation : ∀ i ∈ C, ∀ v ∈ Set.Icc b (b + D),
      ‖(v : ℂ) * R i (a / v) - (b : ℂ) * R i (a / b)‖ ≤ 3 * (a / b) * (v - b)) :
    ‖(𝔼 g ∈ J, ∑ i ∈ C, phase g i * ((w g : ℂ) * R i (a / w g))) -
      (𝔼 g ∈ J, if g ∈ T then ∑ i ∈ C, phase g i * ((b : ℂ) * R i (a / b)) else 0)‖ ≤
      (C.card : ℝ) * max (3 * (a / b) * D) (S * a) := by
  let B := max (3 * (a / b) * D) (S * a)
  have hB : 0 ≤ B := le_max_of_le_left (by positivity)
  have hterm (g) (hg : g ∈ J) (i) (hi : i ∈ C) :
      ‖phase g i * ((w g : ℂ) * R i (a / w g)) -
        (if g ∈ T then phase g i * ((b : ℂ) * R i (a / b)) else 0)‖ ≤ B := by
    by_cases hgt : g ∈ T
    · simp only [ite_eq_left hgt, ← mul_sub, norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) (hphase g hg i hi)).trans
      refine (hvariation i hi (w g) (hthick g hg hgt)).trans ?_
      exact le_max_of_le_left (mul_le_mul_of_nonneg_left
        (sub_le_iff_le_add'.mpr (hthick g hg hgt).2) (by positivity))
    · obtain ⟨hw, hscale⟩ := hthin g hg hgt
      rcases hw.eq_or_lt with hzero | hpos
      · simpa [hgt, ← hzero] using hB
      simp only [ite_eq_right hgt, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hw]
      apply (mul_le_of_le_one_left (mul_nonneg hw (norm_nonneg _)) (hphase g hg i hi)).trans
      calc
        w g * ‖R i (a / w g)‖ ≤ w g * (S * (a / w g)) :=
          mul_le_mul_of_nonneg_left (hsaving i hi _ (hscale hpos)) hw
        _ = S * a := by field_simp [hpos.ne']
        _ ≤ B := le_max_right ..
  obtain rfl | hJ := J.eq_empty_or_nonempty
  · simpa using mul_nonneg (Nat.cast_nonneg (α := ℝ) C.card) hB
  rw [← expect_sub_distrib]
  refine (RCLike.norm_expect_le (K := ℂ)).trans (expect_le hJ fun g hg ↦ ?_)
  have hT : (∑ i ∈ C, if g ∈ T then phase g i * ((b : ℂ) * R i (a / b)) else 0) =
      (if g ∈ T then ∑ i ∈ C, phase g i * ((b : ℂ) * R i (a / b)) else 0) := by
    simp only [sum_ite_irrel, sum_const_zero]
  rw [← hT, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  simpa only [sum_const, nsmul_eq_mul] using sum_le_sum fun i hi ↦ hterm g hg i hi

/-- For each translate, drop the thin terms and freeze the thick caps at `b`, in the sum over
all tops and steps. Under the two cost conditions the resulting error in the mean over
translates is at most `#tops * #steps * b / x`. The argument allows the set of thick group
indices to depend on both the translate and the top, as it does for the partner map. -/
theorem norm_expect_sum_scaledRemainder_sub_thick_le_of_costs
    {ι χ υ τ κ : Type*} [DecidableEq ι]
    (J : Finset ι) (C : Finset χ) (translates : Finset υ) (tops : Finset τ) (steps : Finset κ)
    (thick : υ → τ → Finset ι) (phase : ι → χ → ℂ) (R : χ → ℝ → ℂ)
    (a : τ → ℝ) (w : υ → τ → κ → ι → ℝ)
    {x b b' D X S : ℝ} (hx : 3 ≤ x) (hD : 0 ≤ D)
    (hXb : b' * X ≤ x * b)
    (hscale : ∀ t ∈ tops, |a t / b - x| ≤ 1)
    (hphase : ∀ g ∈ J, ∀ i ∈ C, ‖phase g i‖ ≤ 1)
    (hthick : ∀ u ∈ translates, ∀ t ∈ tops, ∀ k ∈ steps, ∀ g ∈ J,
      g ∈ thick u t → w u t k g ∈ Set.Icc b (b + D))
    (hthin : ∀ u ∈ translates, ∀ t ∈ tops, ∀ k ∈ steps, ∀ g ∈ J,
      g ∉ thick u t → w u t k g ∈ Set.Icc 0 (2 * b'))
    (hsaving : ∀ i ∈ C, ∀ y ≥ X / 3, ‖R i y‖ ≤ S * y)
    (hvariation : ∀ t ∈ tops, ∀ i ∈ C, ∀ v ∈ Set.Icc b (b + D),
      ‖(v : ℂ) * R i (a t / v) - (b : ℂ) * R i (a t / b)‖ ≤ 3 * (a t / b) * (v - b))
    (hthickCost : (C.card : ℝ) * (3 * (x + 1) * D) ≤ b / x)
    (hthinCost : (C.card : ℝ) * ((x + 1) * b * S) ≤ b / x) :
    ‖(𝔼 u ∈ translates, ∑ t ∈ tops, ∑ k ∈ steps, 𝔼 g ∈ J,
        ∑ i ∈ C, phase g i * ((w u t k g : ℂ) * R i (a t / w u t k g))) -
      (𝔼 u ∈ translates, ∑ t ∈ tops, ∑ _k ∈ steps, 𝔼 g ∈ J,
        if g ∈ thick u t then ∑ i ∈ C, phase g i * ((b : ℂ) * R i (a t / b)) else 0)‖ ≤
      (tops.card : ℝ) * steps.card * (b / x) := by
  have hx₀ : 0 < x := by linarith
  have hx₁ : 0 ≤ x - 1 := by linarith
  have hcost₀ : 0 ≤ (C.card : ℝ) * (3 * (x + 1) * D) := by positivity
  have hb₀ : 0 ≤ b := by
    simpa only [zero_mul] using (le_div_iff₀ hx₀).mp (hcost₀.trans hthickCost)
  have hcap (u) (hu : u ∈ translates) (t) (ht : t ∈ tops) (k) (hk : k ∈ steps) :
      ‖(𝔼 g ∈ J, ∑ i ∈ C, phase g i * ((w u t k g : ℂ) * R i (a t / w u t k g))) -
        (𝔼 g ∈ J, if g ∈ thick u t then ∑ i ∈ C, phase g i * ((b : ℂ) * R i (a t / b))
          else 0)‖ ≤ b / x := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hscale t ht)
    have hb : 0 < b := hb₀.lt_of_ne' fun hzero ↦ by
      simp only [hzero, div_zero, zero_sub] at hlo hhi
      linarith
    have ha₁ : (x - 1) * b ≤ a t := (le_div_iff₀ hb).mp (by linarith)
    have ha₂ : a t ≤ (x + 1) * b := (div_le_iff₀ hb).mp (by linarith)
    have ha : 0 ≤ a t := (mul_nonneg hx₁ hb.le).trans ha₁
    refine (norm_expect_sum_scaledRemainder_sub_thick_le J (thick u t) C phase R (w u t k)
      ha hb₀ hD hphase (hthick u hu t ht k hk) ?_ hsaving (hvariation t ht)).trans ?_
    · intro g hg hgt
      obtain ⟨hw, hw'⟩ := hthin u hu t ht k hk g hg hgt
      refine ⟨hw, fun hw₀ ↦ (le_div_iff₀ hw₀).mpr ?_⟩
      by_cases hX : 0 ≤ X
      · have h := mul_le_mul_of_nonneg_left hw' hX
        have hxb := mul_le_mul_of_nonneg_right (show 2 * x ≤ 3 * (x - 1) by linarith) hb.le
        nlinarith only [h, hXb, hxb, ha₁]
      · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hw₀.le).trans ha
    · rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg C.card)]
      refine max_le (le_trans ?_ hthickCost) ?_
      · gcongr
        linarith
      · by_cases hS : 0 ≤ S
        · refine le_trans ?_ hthinCost
          rw [mul_comm S]
          gcongr
        · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity)
            (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hS) ha)).trans (by positivity)
  obtain rfl | hU := translates.eq_empty_or_nonempty
  · simp only [expect_empty, sub_self, norm_zero]
    positivity
  rw [← expect_sub_distrib]
  refine (RCLike.norm_expect_le (K := ℂ)).trans (expect_le hU fun u hu ↦ ?_)
  simp only [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  simpa only [sum_const, nsmul_eq_mul, mul_assoc] using sum_le_sum fun t ht ↦
    (norm_sum_le _ _).trans (sum_le_sum fun k hk ↦ hcap u hu t ht k hk)

end TauCeti
