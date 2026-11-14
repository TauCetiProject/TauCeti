/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.MeanInequalities

/-!
# `Lʳ` seminorms of the pieces of a function

Let `J₁, …, J_N` be pairwise disjoint measurable sets and `1 ≤ r ≤ ∞`. The restrictions `1_{Jᵢ} g`
of a function `g` have `Lʳ` seminorms whose `ℓʳ` sum is at most `‖g‖_r`, so by Hölder's inequality
in `ℝᴺ` their plain sum satisfies

`∑ᵢ ‖1_{Jᵢ} g‖_r ≤ N^{1 - 1/r} ‖g‖_r`

(`TauCeti.sum_eLpNorm_indicator_le`). For `r = 1` this is additivity of the integral over disjoint
sets, and for `r = ∞` it is the bound of each piece by `‖g‖_∞`. Such sums arise when a function is
cut into many pieces of comparable size, as in the dyadic decompositions behind the Christ–Kiselev
lemma.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- **Hölder's inequality for disjoint pieces.** For `1 ≤ r`, the `Lʳ` seminorms of the restrictions
of `g` to the members of a finite family of `N` pairwise disjoint measurable sets add up to at most
`N^{1 - 1/r} ‖g‖_r`. -/
theorem sum_eLpNorm_indicator_le {α ι F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {r : ℝ≥0∞} (hr : 1 ≤ r) (s : Finset ι) {J : ι → Set α}
    (hJ : ∀ i ∈ s, MeasurableSet (J i)) (hd : (s : Set ι).PairwiseDisjoint J) (g : α → F) :
    ∑ i ∈ s, eLpNorm ((J i).indicator g) r μ ≤
      (s.card : ℝ≥0∞) ^ (1 - r.toReal⁻¹) * eLpNorm g r μ := by
  rcases eq_or_ne r ∞ with rfl | hr_top
  · simp only [ENNReal.toReal_top, inv_zero, sub_zero, ENNReal.rpow_one]
    calc ∑ i ∈ s, eLpNorm ((J i).indicator g) ∞ μ ≤ ∑ _i ∈ s, eLpNorm g ∞ μ :=
          Finset.sum_le_sum fun i hi => eLpNorm_indicator_le g (hJ i hi).nullMeasurableSet
      _ = _ := by simp
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  by_cases hg : eLpNorm g r μ = ∞
  · rw [hg, ENNReal.mul_top (by simp [hs.ne_empty])]
    exact le_top
  have hgm := aestronglyMeasurable_of_eLpNorm_ne_top hg
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  set r₀ := r.toReal
  have hr₀ : 1 ≤ r₀ := by
    simpa using ENNReal.toReal_mono hr_top hr
  have hr₀0 : 0 < r₀ := zero_lt_one.trans_le hr₀
  have hnorm (K : Set α) (hK : MeasurableSet K) :
      eLpNorm (K.indicator g) r μ = (∫⁻ x in K, ‖g x‖ₑ ^ r₀ ∂μ) ^ (1 / r₀) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hK.nullMeasurableSet,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hr0 hr_top hgm.restrict]
  have hg_eq : eLpNorm g r μ = (∫⁻ x, ‖g x‖ₑ ^ r₀ ∂μ) ^ (1 / r₀) :=
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hr0 hr_top hgm
  rw [Finset.sum_congr rfl fun i hi => hnorm _ (hJ i hi), hg_eq]
  set x : ι → ℝ≥0∞ := fun i => (∫⁻ y in J i, ‖g y‖ₑ ^ r₀ ∂μ) ^ (1 / r₀)
  -- The `r₀`-th power of the sum is controlled by the sum of the `r₀`-th powers.
  have hpow : (∑ i ∈ s, x i) ^ r₀ ≤ (s.card : ℝ≥0∞) ^ (r₀ - 1) * ∫⁻ y, ‖g y‖ₑ ^ r₀ ∂μ := by
    refine (ENNReal.rpow_sum_le_const_mul_sum_rpow s x hr₀).trans ?_
    gcongr
    calc ∑ i ∈ s, x i ^ r₀ = ∑ i ∈ s, ∫⁻ y in J i, ‖g y‖ₑ ^ r₀ ∂μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hr₀0.ne', ENNReal.rpow_one]
      _ = ∫⁻ y in ⋃ i ∈ s, J i, ‖g y‖ₑ ^ r₀ ∂μ :=
          (lintegral_biUnion_finset hd hJ _).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  calc ∑ i ∈ s, x i = ((∑ i ∈ s, x i) ^ r₀) ^ (1 / r₀) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr₀0.ne', ENNReal.rpow_one]
    _ ≤ ((s.card : ℝ≥0∞) ^ (r₀ - 1) * ∫⁻ y, ‖g y‖ₑ ^ r₀ ∂μ) ^ (1 / r₀) := by gcongr
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        congr 2
        field_simp

end TauCeti
