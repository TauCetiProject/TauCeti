/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
-- `Mathlib.Analysis.SpecialFunctions.NonIntegrable` is imported privately: it supplies
-- `not_integrableOn_Ioi_inv`, used only inside the proof that the maximal function of the
-- indicator is not integrable.
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# The maximal function of the indicator of an interval

Let `f = 1_{[a, b]}` on `ℝ`, with `a < b`, and let `M f` be its centred Hardy–Littlewood maximal
function for Lebesgue measure (`TauCeti.maximalFunction`). This file computes `M f` exactly:

* `M f x = 1` for `a < x < b` (`TauCeti.maximalFunction_indicator_Icc_of_mem_Ioo`);
* `M f x = (b - a) / (2 (x - a))` for `x ≥ b`
  (`TauCeti.maximalFunction_indicator_Icc_of_right_le`), the supremum being attained at the
  radius `x - a`, whose ball `(a, 2 x - a)` contains `(a, b]`;
* `M f x = (b - a) / (2 (b - x))` for `x ≤ a` (`TauCeti.maximalFunction_indicator_Icc_of_le_left`),
  by the symmetry `M f (a + b - x) = M f x` (`TauCeti.maximalFunction_indicator_Icc_add_sub`).

At the endpoints both formulas give `1 / 2`.

The tails decay like `1 / |x|`, so `M f` is not integrable although `f` is
(`TauCeti.lintegral_maximalFunction_indicator_Icc_eq_top`): **the maximal function is not
bounded on `L¹`**, and the weak type `(1, 1)` bound `TauCeti.mul_measure_lt_maximalFunction_le`
is the correct `L¹` statement. The superlevel sets are explicit: for `0 < t ≤ 1 / 2`,
`{M f > t}` is the interval of half-length `(1 - t) (b - a) / (2 t)` about the midpoint of `[a, b]`
(`TauCeti.setOf_lt_maximalFunction_indicator_Icc`), so

`t · |{M f > t}| = (1 - t) (b - a) = (1 - t) ‖f‖₁`

(`TauCeti.ofReal_mul_volume_lt_maximalFunction_indicator_Icc`). The weak type `(1, 1)` quotient
`t · |{M f > t}| / ‖f‖₁` therefore tends to `1` as `t → 0`, below the constant `4` of the general
inequality in dimension one, while the integral `∫ M f = ∫₀^∞ |{M f > t}| dt` diverges at
`t = 0`.

## References

* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, §1.
* L. Grafakos, *Classical Fourier Analysis*, Section 2.1.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {a b : ℝ}

/-- The average of the indicator of `[a, b]` over a ball is the proportion of the ball that the
interval covers. -/
private theorem setLAverage_ball_indicator_Icc (x r : ℝ) :
    ⨍⁻ y in ball x r, ‖(Icc a b).indicator (1 : ℝ → ℝ) y‖ₑ =
      volume (Icc a b ∩ ball x r) / ENNReal.ofReal (2 * r) := by
  simp_rw [eNorm_indicator_eq_indicator_eNorm, Pi.one_apply, eNorm_one]
  rw [setLAverage_eq, lintegral_indicator_const measurableSet_Icc, one_mul,
    Measure.restrict_apply measurableSet_Icc, Real.volume_ball]

/-- Inside the interval, the maximal function of its indicator is `1`: small balls lie in the
interval, and no average of the indicator exceeds `1`. -/
theorem maximalFunction_indicator_Icc_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo a b) :
    maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x = 1 := by
  refine le_antisymm (maximalFunction_le fun r _ => ?_) ?_
  · rw [setLAverage_ball_indicator_Icc, ← Real.volume_ball x r]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
  · set r := min (x - a) (b - x)
    have hr : 0 < r := lt_min (sub_pos.2 hx.1) (sub_pos.2 hx.2)
    have hsub : ball x r ⊆ Icc a b := by
      intro y hy
      rw [Real.ball_eq_Ioo] at hy
      have h₁ := min_le_left (x - a) (b - x)
      have h₂ := min_le_right (x - a) (b - x)
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc (1 : ℝ≥0∞) = volume (Icc a b ∩ ball x r) / ENNReal.ofReal (2 * r) := by
          rw [inter_eq_right.2 hsub, Real.volume_ball,
            ENNReal.div_self (by simpa using hr) ENNReal.ofReal_ne_top]
      _ ≤ _ := (setLAverage_ball_indicator_Icc x r).symm.le.trans
          (setLAverage_le_maximalFunction _ _ x hr)

/-- To the right of the interval, the maximal function of its indicator is
`(b - a) / (2 (x - a))`. The supremum is attained at the radius `x - a`, whose ball
`(a, 2 x - a)` contains `(a, b]`. -/
theorem maximalFunction_indicator_Icc_of_right_le (hab : a ≤ b) {x : ℝ} (hx : b ≤ x) :
    maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x =
      ENNReal.ofReal ((b - a) / (2 * (x - a))) := by
  rcases hab.eq_or_lt with rfl | hab
  · -- A degenerate interval is a null set, so both sides vanish.
    rw [sub_self, zero_div, ENNReal.ofReal_zero]
    refine le_antisymm (maximalFunction_le fun r _ => ?_) zero_le
    rw [setLAverage_ball_indicator_Icc, Icc_self,
      measure_mono_null inter_subset_left (Real.volume_singleton), ENNReal.zero_div]
  have hxa : 0 < x - a := by linarith
  refine le_antisymm (maximalFunction_le fun r _ => ?_) ?_
  · rw [setLAverage_ball_indicator_Icc]
    refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hsub : Icc a b ∩ ball x r ⊆ Icc (max a (x - r)) b := by
      intro y ⟨hy, hy'⟩
      rw [Real.ball_eq_Ioo] at hy'
      exact ⟨max_le hy.1 hy'.1.le, hy.2⟩
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Icc]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rcases le_total (x - r) a with h | h
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right h]
      nlinarith
  · have hsub : Ioo a b ⊆ Icc a b ∩ ball x (x - a) := by
      intro y hy
      rw [Real.ball_eq_Ioo]
      exact ⟨Ioo_subset_Icc_self hy, by linarith [hy.1], by linarith [hy.2]⟩
    calc ENNReal.ofReal ((b - a) / (2 * (x - a)))
        = volume (Ioo a b) / ENNReal.ofReal (2 * (x - a)) := by
          rw [Real.volume_Ioo, ENNReal.ofReal_div_of_pos (by positivity)]
      _ ≤ volume (Icc a b ∩ ball x (x - a)) / ENNReal.ofReal (2 * (x - a)) := by
          gcongr
      _ ≤ _ := (setLAverage_ball_indicator_Icc x (x - a)).symm.le.trans
          (setLAverage_le_maximalFunction _ _ x hxa)

/-- The maximal function of the indicator of `[a, b]` is symmetric about the midpoint of the
interval. This is the invariance of the maximal function under the reflection `x ↦ a + b - x`,
a dilation by `-1` followed by a translation. -/
theorem maximalFunction_indicator_Icc_add_sub (x : ℝ) :
    maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) (a + b - x) =
      maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x := by
  have hsymm : (fun y => (Icc a b).indicator (1 : ℝ → ℝ) ((-1 : ℝ) • y + (a + b))) =
      (Icc a b).indicator 1 := by
    ext y
    have hmem : -y + (a + b) ∈ Icc a b ↔ y ∈ Icc a b := by
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [indicator_apply, smul_eq_mul, neg_one_mul, hmem, Pi.one_apply]
  have h := maximalFunction_comp_smul (μ := volume)
    (fun z => (Icc a b).indicator (1 : ℝ → ℝ) (z + (a + b))) (t := -1) (by norm_num) x
  rw [hsymm, maximalFunction_comp_add_right] at h
  rw [h, neg_one_smul, neg_add_eq_sub]

/-- To the left of the interval, the maximal function of its indicator is
`(b - a) / (2 (b - x))`. -/
theorem maximalFunction_indicator_Icc_of_le_left (hab : a ≤ b) {x : ℝ} (hx : x ≤ a) :
    maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x =
      ENNReal.ofReal ((b - a) / (2 * (b - x))) := by
  rw [← maximalFunction_indicator_Icc_add_sub,
    maximalFunction_indicator_Icc_of_right_le hab (by linarith),
    show a + b - x - a = b - x by ring]

/-- **The maximal function is not bounded on `L¹`.** The indicator of `[a, b]` is integrable, but
its maximal function is not: its tail `(b - a) / (2 (x - a))` decays only like `1 / x`. -/
theorem lintegral_maximalFunction_indicator_Icc_eq_top (hab : a < b) :
    ∫⁻ x, maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x = ∞ := by
  -- Beyond `c`, the maximal function dominates `k / x` with `k = (b - a) / 4`, which is not
  -- integrable there.
  set c := max b |a|
  set k := (b - a) / 4
  have hk : 0 < k := by positivity [sub_pos.2 hab]
  have hc : 0 < c := by
    rcases le_or_gt b 0 with hb | hb
    · exact lt_max_of_lt_right (abs_pos.2 (by linarith))
    · exact lt_max_of_lt_left hb
  have hle : ∫⁻ x in Ioi c, ENNReal.ofReal (k * x⁻¹) ≤
      ∫⁻ x, maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x := by
    refine (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall
      fun x hx => ?_))).trans (setLIntegral_le_lintegral _ _)
    have hbx : b < x := (le_max_left b |a|).trans_lt hx
    have hax : -a < x := (neg_le_abs a).trans_lt ((le_max_right b |a|).trans_lt hx)
    rw [maximalFunction_indicator_Icc_of_right_le hab.le hbx.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← div_eq_mul_inv, div_div]
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  by_contra h
  have hint : IntegrableOn (fun x : ℝ => k * x⁻¹) (Ioi c) :=
    ⟨(measurable_const.mul measurable_inv).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioi).2
        (.of_forall fun x hx => by have : 0 < x := hc.trans hx; positivity))).2
        (hle.trans_lt (lt_top_iff_ne_top.2 h))⟩
  exact not_integrableOn_Ioi_inv (a := c) (by
    simpa [IntegrableOn, inv_mul_cancel_left₀ hk.ne'] using hint.const_mul k⁻¹)

/-- For `0 < t ≤ 1 / 2`, the set where the maximal function of the indicator of `[a, b]` exceeds
`t` is the open interval of half-length `(1 - t) (b - a) / (2 t)` about the midpoint of
`[a, b]`. -/
theorem setOf_lt_maximalFunction_indicator_Icc (hab : a < b) {t : ℝ} (ht : 0 < t)
    (ht' : t ≤ 1 / 2) :
    {x | ENNReal.ofReal t < maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x} =
      Ioo (b - (b - a) / (2 * t)) (a + (b - a) / (2 * t)) := by
  set d := (b - a) / (2 * t) with hd_def
  have hd : 2 * t * d = b - a := by
    rw [hd_def]
    field_simp
  have hwide : b - a ≤ d := by nlinarith
  ext x
  simp only [mem_ofPred_eq, mem_Ioo]
  rcases le_or_gt b x with hbx | hxb
  · rw [maximalFunction_indicator_Icc_of_right_le hab.le hbx,
      ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) (by linarith)), lt_div_iff₀ (by linarith)]
    constructor
    · intro h
      exact ⟨by linarith, by nlinarith⟩
    · intro h
      nlinarith [h.2]
  rcases le_or_gt x a with hxa | hax
  · rw [maximalFunction_indicator_Icc_of_le_left hab.le hxa,
      ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) (by linarith)), lt_div_iff₀ (by linarith)]
    constructor
    · intro h
      exact ⟨by nlinarith, by linarith⟩
    · intro h
      nlinarith [h.1]
  · rw [maximalFunction_indicator_Icc_of_mem_Ioo ⟨hax, hxb⟩, ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff one_pos]
    exact iff_of_true (by linarith) ⟨by linarith, by linarith⟩

/-- The weak type `(1, 1)` quantity of the indicator of `[a, b]`: for `0 < t ≤ 1 / 2`,
`t · |{M f > t}| = (1 - t) (b - a)`, which is `(1 - t) ‖f‖₁`. -/
theorem ofReal_mul_volume_lt_maximalFunction_indicator_Icc (hab : a < b) {t : ℝ} (ht : 0 < t)
    (ht' : t ≤ 1 / 2) :
    ENNReal.ofReal t *
        volume {x | ENNReal.ofReal t < maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x} =
      ENNReal.ofReal ((1 - t) * (b - a)) := by
  rw [setOf_lt_maximalFunction_indicator_Icc hab ht ht', Real.volume_Ioo,
    ← ENNReal.ofReal_mul ht.le]
  congr 1
  field_simp
  ring

end TauCeti
