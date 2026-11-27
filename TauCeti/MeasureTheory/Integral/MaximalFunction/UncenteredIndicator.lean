/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction.Indicator
public import TauCeti.MeasureTheory.Integral.UncenteredMaximalFunction
-- The following are imported privately: they supply `TauCeti.setLAverage_enorm_indicator_one`,
-- `MeasureTheory.Measure.addHaar_real_ball_div_addHaar_real_ball`,
-- `Metric.measureReal_ball_pos` and `MeasureTheory.measure_inter_div_le_one`, used only inside
-- proofs.
import TauCeti.MeasureTheory.Integral.Average.Indicator
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.MeasureTheory.OuterMeasure.Basic

/-!
# The uncentred maximal function of the indicator of an interval or a ball

The uncentred maximal function `M_u f` (`TauCeti.uncenteredMaximalFunction`) is at most `2ⁿ` times
the centred one `M f` (`TauCeti.maximalFunction`) for an additive Haar measure on a real normed
space of dimension `n` (`TauCeti.uncenteredMaximalFunction_le_two_pow_mul_maximalFunction`). This
file shows that the constant `2ⁿ` cannot be lowered, by testing indicators.

* **Dimension one, exactly.** For `f = 1_{[a, b]}` on `ℝ` and `x ≥ b`, the intervals `(a, x + ε)`
  contain `x` and give `M_u f x = (b - a) / (x - a)`
  (`TauCeti.uncenteredMaximalFunction_indicator_Icc_of_right_le`), while the centred value is
  `(b - a) / (2 (x - a))` (`TauCeti.maximalFunction_indicator_Icc_of_right_le`). So
  `M_u f x = 2 · M f x` at every such `x`
  (`TauCeti.uncenteredMaximalFunction_indicator_Icc_eq_two_mul_maximalFunction`): the constant
  `2` is attained.
* **Every dimension, asymptotically.** For `f = 1_{B(0, 1)}` and `‖x‖ = R > 1`, a centred ball
  meets `B(0, 1)` only if its radius exceeds `R - 1`, so `M f x ≤ (R - 1)⁻ⁿ`
  (`TauCeti.maximalFunction_indicator_ball_zero_one_le`); the ball of radius `R / 2 + 1` about
  `x / 2`, of about half that radius, still contains `x` and all of `B(0, 1)`, so
  `M_u f x ≥ (R / 2 + 1)⁻ⁿ`
  (`TauCeti.ofReal_inv_pow_le_uncenteredMaximalFunction_indicator_ball_zero_one`). The ratio
  `((R - 1) / (R / 2 + 1))ⁿ` tends to `2ⁿ`, so any `c` with `M_u f ≤ c · M f` satisfies `2ⁿ ≤ c`
  (`TauCeti.two_pow_finrank_le_of_uncenteredMaximalFunction_le_mul_maximalFunction`).

## References

* E. Stein, *Harmonic Analysis*, Chapter I.
* L. Grafakos, *Classical Fourier Analysis*, Section 2.1.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module Set Filter Topology
open scoped ENNReal

section Interval

variable {a b x : ℝ}

/-- An interval `(y - r, y + r)` containing a point `x` to the right of `[a, b]` meets `[a, b]`
inside `[max a (y - r), b]`, so the average of the indicator over it is at most
`(b - a) / (x - a)`. -/
private theorem setLAverage_ball_indicator_Icc_le (hab : a < b) (hx : b ≤ x) {y r : ℝ}
    (hxr : x ∈ ball y r) :
    ⨍⁻ z in ball y r, ‖(Icc a b).indicator (1 : ℝ → ℝ) z‖ₑ ≤
      ENNReal.ofReal ((b - a) / (x - a)) := by
  have hxa : 0 < x - a := by linarith
  rw [setLAverage_enorm_indicator_one measurableSet_Icc, Real.volume_ball]
  rw [mem_ball, Real.dist_eq, abs_lt] at hxr
  refine ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine volume_Icc_inter_ball_le.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_mul_eq_mul_div, le_div_iff₀ hxa]
  rcases le_total (y - r) a with h | h
  · rw [max_eq_left h]
    nlinarith
  · rw [max_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hx)]

/-- To the right of `[a, b]`, the uncentred maximal function of its indicator is
`(b - a) / (x - a)`. The supremum is approached by the intervals `(a, x + ε)`, which contain `x`
and `(a, b)`. -/
theorem uncenteredMaximalFunction_indicator_Icc_of_right_le (hab : a ≤ b) (hx : b ≤ x) :
    uncenteredMaximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x =
      ENNReal.ofReal ((b - a) / (x - a)) := by
  rcases hab.eq_or_lt with rfl | hab
  · -- A degenerate interval is a null set, so both sides vanish.
    rw [sub_self, zero_div, ENNReal.ofReal_zero]
    refine le_antisymm (uncenteredMaximalFunction_le fun y r _ => ?_) zero_le
    rw [setLAverage_enorm_indicator_one measurableSet_Icc, Icc_self,
      measure_mono_null inter_subset_left Real.volume_singleton, ENNReal.zero_div]
  have hxa : 0 < x - a := by linarith
  refine le_antisymm (uncenteredMaximalFunction_le fun y r hxr =>
    setLAverage_ball_indicator_Icc_le hab hx hxr) ?_
  · -- The averages over `(a, x + ε)` are `(b - a) / (x - a + ε)`, which tend to the value.
    have hlim : Tendsto (fun ε => ENNReal.ofReal ((b - a) / (x - a + ε))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((b - a) / (x - a)))) := by
      refine ENNReal.tendsto_ofReal (Tendsto.mono_left ?_ nhdsWithin_le_nhds)
      have h := tendsto_const_nhds (x := b - a).div (tendsto_const_nhds (x := x - a).add
        (tendsto_id (x := 𝓝 (0 : ℝ)))) (by rw [add_zero]; exact hxa.ne')
      rwa [add_zero] at h
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun (ε : ℝ) (hε : 0 < ε) => ?_)
    have hball : ball ((a + (x + ε)) / 2) ((x + ε - a) / 2) = Ioo a (x + ε) := by
      rw [Real.ball_eq_Ioo]
      congr 1 <;> ring
    have hmem : x ∈ ball ((a + (x + ε)) / 2) ((x + ε - a) / 2) := by
      rw [hball]
      exact ⟨by linarith, by linarith⟩
    refine le_trans ?_ (setLAverage_le_uncenteredMaximalFunction volume _ hmem)
    rw [setLAverage_enorm_indicator_one measurableSet_Icc, hball]
    have hsub : Ioo a b ⊆ Icc a b ∩ Ioo a (x + ε) :=
      fun z hz => ⟨Ioo_subset_Icc_self hz, hz.1, by linarith [hz.2]⟩
    calc ENNReal.ofReal ((b - a) / (x - a + ε))
        = volume (Ioo a b) / volume (Ioo a (x + ε)) := by
          rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_div_of_pos (by linarith),
            show x + ε - a = x - a + ε by ring]
      _ ≤ volume (Icc a b ∩ Ioo a (x + ε)) / volume (Ioo a (x + ε)) :=
          ENNReal.div_le_div_right (measure_mono hsub) _

/-- **The comparison constant `2` between the uncentred and centred maximal functions on `ℝ` is
attained.** To the right of `[a, b]`, the uncentred maximal function of its indicator is exactly
twice the centred one. -/
theorem uncenteredMaximalFunction_indicator_Icc_eq_two_mul_maximalFunction (hab : a ≤ b)
    (hx : b ≤ x) :
    uncenteredMaximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x =
      2 * maximalFunction volume ((Icc a b).indicator (1 : ℝ → ℝ)) x := by
  rw [uncenteredMaximalFunction_indicator_Icc_of_right_le hab hx,
    maximalFunction_indicator_Icc_of_right_le hab hx, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul zero_le_two, ← mul_div_assoc, mul_div_mul_left _ _ two_ne_zero]

end Interval

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The unit ball fills the proportion `r⁻ⁿ` of the measure of any ball of radius `r > 0`. -/
private theorem addHaar_ball_zero_one_div_addHaar_ball (y : E) {r : ℝ} (hr : 0 < r) :
    μ (ball (0 : E) 1) / μ (ball y r) = ENNReal.ofReal ((r ^ finrank ℝ E)⁻¹) := by
  rw [← ofReal_measureReal measure_ball_lt_top.ne, ← ofReal_measureReal measure_ball_lt_top.ne,
    ← ENNReal.ofReal_div_of_pos (measureReal_ball_pos μ y hr),
    μ.addHaar_real_ball_div_addHaar_real_ball y 0 hr one_pos, one_div_pow, one_div]

/-- Away from the unit ball, the centred maximal function of its indicator is at most
`(‖x‖ - 1)⁻ⁿ`: a ball about `x` meets the unit ball only if its radius `r` exceeds `‖x‖ - 1`, and
then the unit ball fills at most the proportion `r⁻ⁿ` of it. -/
theorem maximalFunction_indicator_ball_zero_one_le {x : E} (hx : 1 < ‖x‖) :
    maximalFunction μ ((ball (0 : E) 1).indicator (1 : E → ℝ)) x ≤
      ENNReal.ofReal (((‖x‖ - 1) ^ finrank ℝ E)⁻¹) := by
  refine maximalFunction_le fun r hr => ?_
  rw [setLAverage_enorm_indicator_one measurableSet_ball]
  rcases le_or_gt r (‖x‖ - 1) with hrx | hrx
  · have hempty : ball (0 : E) 1 ∩ ball x r = ∅ := by
      refine eq_empty_of_forall_notMem fun z ⟨hz, hz'⟩ => ?_
      rw [mem_ball_zero_iff] at hz
      rw [mem_ball, dist_eq_norm] at hz'
      have := norm_sub_le z (z - x)
      rw [sub_sub_cancel] at this
      linarith
    rw [hempty, measure_empty, ENNReal.zero_div]
    exact zero_le
  · calc μ (ball 0 1 ∩ ball x r) / μ (ball x r) ≤ μ (ball (0 : E) 1) / μ (ball x r) := by
          gcongr
          exact inter_subset_left
      _ = ENNReal.ofReal ((r ^ finrank ℝ E)⁻¹) := addHaar_ball_zero_one_div_addHaar_ball μ x hr
      _ ≤ ENNReal.ofReal (((‖x‖ - 1) ^ finrank ℝ E)⁻¹) := by
          gcongr

/-- The uncentred maximal function of the indicator of the unit ball is at least
`(‖x‖ / 2 + 1)⁻ⁿ`: the ball of radius `‖x‖ / 2 + 1` about `x / 2` contains both `x` and the unit
ball. -/
theorem ofReal_inv_pow_le_uncenteredMaximalFunction_indicator_ball_zero_one (x : E) :
    ENNReal.ofReal (((‖x‖ / 2 + 1) ^ finrank ℝ E)⁻¹) ≤
      uncenteredMaximalFunction μ ((ball (0 : E) 1).indicator (1 : E → ℝ)) x := by
  have hhalf : ‖(2 : ℝ)⁻¹ • x‖ = ‖x‖ / 2 := by
    rw [norm_smul, norm_inv, Real.norm_two, inv_mul_eq_div]
  have hmem : x ∈ ball ((2 : ℝ)⁻¹ • x) (‖x‖ / 2 + 1) := by
    rw [mem_ball, dist_eq_norm, show x - (2 : ℝ)⁻¹ • x = (2 : ℝ)⁻¹ • x by module, hhalf]
    linarith
  have hsub : ball (0 : E) 1 ⊆ ball ((2 : ℝ)⁻¹ • x) (‖x‖ / 2 + 1) := fun z hz => by
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_eq_norm]
    linarith [norm_sub_le z ((2 : ℝ)⁻¹ • x)]
  refine le_trans ?_ (setLAverage_le_uncenteredMaximalFunction μ _ hmem)
  have hr : 0 < ‖x‖ / 2 + 1 := by positivity
  rw [setLAverage_enorm_indicator_one measurableSet_ball, inter_eq_left.2 hsub,
    addHaar_ball_zero_one_div_addHaar_ball μ _ hr]

/-- **The constant `2ⁿ` comparing the uncentred and centred maximal functions is sharp.** On a
real normed space of dimension `n` with an additive Haar measure, if the uncentred maximal
function of the indicator of the unit ball is at most `c` times its centred maximal function,
then `2ⁿ ≤ c`; so `TauCeti.uncenteredMaximalFunction_le_two_pow_mul_maximalFunction` cannot hold
with a smaller constant. -/
theorem two_pow_finrank_le_of_uncenteredMaximalFunction_le_mul_maximalFunction {c : ℝ≥0∞}
    (h : ∀ x, uncenteredMaximalFunction μ ((ball (0 : E) 1).indicator (1 : E → ℝ)) x ≤
      c * maximalFunction μ ((ball (0 : E) 1).indicator (1 : E → ℝ)) x) :
    2 ^ finrank ℝ E ≤ c := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension `0`, both maximal functions equal `1` at the origin.
    have hM : maximalFunction μ ((ball (0 : E) 1).indicator (1 : E → ℝ)) 0 ≤ 1 :=
      maximalFunction_indicator_one_le_one measurableSet_ball 0
    have hcM : c * maximalFunction μ ((ball (0 : E) 1).indicator (1 : E → ℝ)) 0 ≤ c * 1 := by
      gcongr
    have h0 := (ofReal_inv_pow_le_uncenteredMaximalFunction_indicator_ball_zero_one μ 0).trans
      ((h 0).trans hcM)
    simpa [finrank_zero_of_subsingleton] using h0
  -- At a point of norm `R > 1`, the two bounds give `((R - 1) / (R / 2 + 1))ⁿ ≤ c`.
  have hbound : ∀ R : ℝ, 1 < R →
      ENNReal.ofReal (((R - 1) / (R / 2 + 1)) ^ finrank ℝ E) ≤ c := by
    intro R hR
    obtain ⟨x, hx⟩ := exists_norm_eq E (zero_le_one.trans hR.le)
    have h1 := ofReal_inv_pow_le_uncenteredMaximalFunction_indicator_ball_zero_one μ x
    have h2 := maximalFunction_indicator_ball_zero_one_le μ (hx ▸ hR)
    rw [hx] at h1 h2
    rw [div_pow, div_eq_mul_inv, ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal ((R - 1) ^ finrank ℝ E) * ENNReal.ofReal (((R / 2 + 1) ^ finrank ℝ E)⁻¹)
        ≤ ENNReal.ofReal ((R - 1) ^ finrank ℝ E) *
            (c * ENNReal.ofReal (((R - 1) ^ finrank ℝ E)⁻¹)) := by
          gcongr
          exact h1.trans ((h x).trans (by gcongr))
      _ = c := by
          rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity),
            mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, mul_one]
  -- As `R → ∞`, `(R - 1) / (R / 2 + 1) = 2 - 6 / (R + 2)` tends to `2`.
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal (((R - 1) / (R / 2 + 1)) ^ finrank ℝ E))
      atTop (𝓝 (2 ^ finrank ℝ E)) := by
    have h6 : Tendsto (fun R : ℝ => 2 - 6 / (R + 2)) atTop (𝓝 (2 - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_id))
    rw [sub_zero] at h6
    have h2 : Tendsto (fun R : ℝ => (R - 1) / (R / 2 + 1)) atTop (𝓝 2) := by
      refine h6.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with R hR
      field_simp
      ring
    have := ENNReal.tendsto_ofReal (h2.pow (finrank ℝ E))
    rwa [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat] at this
  exact le_of_tendsto hlim ((eventually_gt_atTop (1 : ℝ)).mono hbound)

end Ball

end TauCeti
