/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.MeasureTheory.Integral.Average

/-!
# The logarithm of the norm has bounded, but not vanishing, mean oscillation

On a finite-dimensional real normed space `E` of dimension `n ≥ 1` with an additive Haar
measure `μ`, the function `x ↦ log ‖x‖` is the basic example separating the space of functions of
bounded mean oscillation from the bounded functions and from the functions of vanishing mean
oscillation:

* it has bounded mean oscillation, with `‖log ‖·‖‖_{BMO} ≤ 2 · 3ⁿ`
  (`TauCeti.bmoSeminorm_log_norm_le`, `TauCeti.memBMO_log_norm`);
* it is not essentially bounded (`TauCeti.not_memLp_top_log_norm`), so the inclusion
  `L^∞ ⊆ BMO` of `MeasureTheory.MemLp.memBMO` is strict;
* its mean oscillation on every ball centred at the origin is at least `log 2 / (2 · 8ⁿ)`, however
  small the ball (`TauCeti.ofReal_le_setLAverage_enorm_log_norm_sub_setAverage_ball_zero`), so it
  does not have vanishing mean oscillation (`TauCeti.not_memVMO_log_norm`).

## Main declarations

* `TauCeti.setLIntegral_enorm_log_norm_sub_log_le`: `∫_{B(0, R)} |log ‖y‖ - log R| ≤ μ(B(0, R))`.
* `TauCeti.bmoSeminorm_log_norm_le`, `TauCeti.memBMO_log_norm`: `log ‖·‖` has bounded mean
  oscillation.
* `TauCeti.not_memLp_top_log_norm`: `log ‖·‖` is not essentially bounded.
* `TauCeti.ofReal_le_setLAverage_enorm_log_norm_sub_setAverage_ball_zero`,
  `TauCeti.not_memVMO_log_norm`: `log ‖·‖` does not have vanishing mean oscillation.

## The bounds

The upper bound distinguishes two kinds of balls `B = B(c, r)`. If `‖c‖ ≥ 2r`, the ball stays
away from the origin and `‖y‖ / ‖c‖` lies between `1/2` and `3/2` on it, so `log ‖·‖` differs from
the constant `log ‖c‖` by at most `1` there. Otherwise `B ⊆ B(0, 3r)`, and the layer cake formula
computes the mean of `log (3r / ‖y‖)` over `B(0, 3r)`: its superlevel set at height `t > 0` lies in
the ball `B(0, 3r e^{-t})`, of measure at most `e^{-t} μ(B(0, 3r))`, so the mean is at most `1`, and
the mean over `B` is at most `μ(B(0, 3r)) / μ(B) = 3ⁿ` times as large. Replacing the constant by
the average of `log ‖·‖` over `B` costs a factor `2`.

The lower bound is scale invariant. The ball `B(0, r)` contains two balls of radius `r / 8`, each
of measure `8⁻ⁿ μ(B(0, r))`, one on which `log ‖·‖ < log (r / 4)` and one on which
`log ‖·‖ > log (r / 2)`. No constant is within `log 2 / 2` of both ranges.

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.1.
* E. M. Stein, *Harmonic Analysis*, Chapter IV, §1.1.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- **`log ‖x‖` is not essentially bounded** on a nontrivial real normed space, for any measure that
is positive on nonempty open sets. With `TauCeti.memBMO_log_norm`, this shows that the inclusion
`L^∞ ⊆ BMO` is strict. -/
theorem not_memLp_top_log_norm [Nontrivial E] [μ.IsOpenPosMeasure] :
    ¬ MemLp (fun x : E => Real.log ‖x‖) ∞ μ := by
  intro h
  set M := eLpNormEssSup (fun x : E => Real.log ‖x‖) μ
  have hM : M ≠ ∞ := by
    have h' := h.eLpNorm_lt_top
    rw [eLpNorm_exponent_top] at h'
    · exact h'.ne
    · exact h.aestronglyMeasurable
  -- The points of norm greater than `e^M` form a nonempty open set, hence one of positive
  -- measure, on which `|log ‖·‖|` exceeds its essential supremum.
  set U : Set E := {x | Real.exp M.toReal < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  obtain ⟨x, hx⟩ := exists_norm_eq E (Real.exp_pos (M.toReal + 1)).le
  have hUne : U.Nonempty :=
    ⟨x, by simp only [U, mem_ofPred_eq, hx, Real.exp_lt_exp]; linarith⟩
  have hUsub : U ⊆ {x | ¬ ‖Real.log ‖x‖‖ₑ ≤ M} := by
    intro y hy
    simp only [U, mem_ofPred_eq] at hy ⊢
    have hlog : M.toReal < Real.log ‖y‖ := by
      rwa [Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hy)]
    rw [not_le, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal hM]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2
      (hlog.trans_le (le_abs_self _))
  exact (hU.measure_pos μ hUne).ne' (measure_mono_null hUsub ae_le_eLpNormEssSup)

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-- On a ball `B(0, R)` of a nontrivial finite-dimensional real normed space with an additive Haar
measure, the function `log (R / ‖y‖)` has mean at most `1`:
`∫_{B(0, R)} |log ‖y‖ - log R| ≤ μ(B(0, R))`. -/
theorem setLIntegral_enorm_log_norm_sub_log_le [Nontrivial E] {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in ball (0 : E) R, ‖Real.log ‖y‖ - Real.log R‖ₑ ∂μ ≤ μ (ball 0 R) := by
  set g : E → ℝ := fun y => Real.log R - Real.log ‖y‖
  -- On the ball `g` is nonnegative away from the null set `{0}`.
  have hg0 : ∀ᵐ y ∂μ.restrict (ball (0 : E) R), 0 ≤ g y ∧
      ‖Real.log ‖y‖ - Real.log R‖ₑ = ENNReal.ofReal (g y) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (μ := μ) (0 : E)))]
      with y hy hy0
    have hpos : 0 < ‖y‖ := norm_pos_iff.2 (by simpa using hy0)
    have hle : 0 ≤ g y := sub_nonneg.2 (Real.log_le_log hpos (mem_ball_zero_iff.1 hy).le)
    refine ⟨hle, ?_⟩
    rw [← enorm_neg, neg_sub, Real.enorm_eq_ofReal hle]
  have hmeas : AEMeasurable g (μ.restrict (ball 0 R)) :=
    (measurable_const.sub (Real.measurable_log.comp measurable_norm)).aemeasurable
  rw [lintegral_congr_ae (hg0.mono fun _ hy => hy.2),
    lintegral_eq_lintegral_meas_lt _ (hg0.mono fun _ hy => hy.1) hmeas]
  -- The superlevel set at height `t > 0` lies in the ball of radius `e^{-t} R`.
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), μ.restrict (ball 0 R) {y | t < g y} ≤
      ENNReal.ofReal (Real.exp (-t)) * μ (ball 0 R) := by
    intro t ht
    have hsub : {y | t < g y} ⊆ ball (0 : E) (Real.exp (-t) * R) := by
      intro y hy
      rw [mem_ball_zero_iff]
      rcases eq_or_ne y 0 with rfl | hy0
      · simpa using mul_pos (Real.exp_pos _) hR
      have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hlt : Real.log ‖y‖ < Real.log (Real.exp (-t) * R) := by
        rw [Real.log_mul (Real.exp_pos _).ne' hR.ne', Real.log_exp]
        simp only [g, mem_ofPred_eq] at hy
        linarith
      exact (Real.log_lt_log_iff hpos (mul_pos (Real.exp_pos _) hR)).1 hlt
    calc μ.restrict (ball 0 R) {y | t < g y} ≤ μ {y | t < g y} := Measure.restrict_apply_le _ _
      _ ≤ μ (ball 0 (Real.exp (-t) * R)) := measure_mono hsub
      _ = ENNReal.ofReal (Real.exp (-t) ^ finrank ℝ E) * μ (ball 0 R) :=
        Measure.addHaar_ball_mul_of_pos μ 0 (Real.exp_pos _) R
      _ ≤ ENNReal.ofReal (Real.exp (-t)) * μ (ball 0 R) := by
        gcongr
        exact pow_le_of_le_one (Real.exp_pos _).le
          (Real.exp_le_one_iff.2 (neg_nonpos.2 (le_of_lt ht))) finrank_pos.ne'
  have hexp : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
      (ae_of_all _ fun t => (Real.exp_pos _).le), integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]
  calc ∫⁻ t in Ioi (0 : ℝ), μ.restrict (ball 0 R) {y | t < g y}
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) * μ (ball 0 R) :=
        setLIntegral_mono' measurableSet_Ioi hlevel
    _ = μ (ball 0 R) := by
        rw [lintegral_mul_const' _ _ measure_ball_lt_top.ne, hexp, one_mul]

omit [NormedSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Away from the origin `log ‖·‖` is nearly constant: if `‖y - c‖ < r` and `2r ≤ ‖c‖`, then
`|log ‖y‖ - log ‖c‖| ≤ 1`. -/
private theorem abs_log_norm_sub_log_norm_le_one {y c : E} {r : ℝ} (hyc : ‖y - c‖ < r)
    (hc : 2 * r ≤ ‖c‖) : |Real.log ‖y‖ - Real.log ‖c‖| ≤ 1 := by
  have hc0 : 0 < ‖c‖ := by linarith [(norm_nonneg _).trans_lt hyc]
  -- `‖y‖ / ‖c‖` lies between `1 / 2` and `3 / 2`.
  have hlo : ‖c‖ / 2 < ‖y‖ := by linarith [norm_le_insert' c y, norm_sub_rev c y]
  have hhi : ‖y‖ < 3 / 2 * ‖c‖ := by linarith [norm_le_insert' y c]
  have hy0 : 0 < ‖y‖ := by linarith
  have hq : 0 < ‖y‖ / ‖c‖ := div_pos hy0 hc0
  rw [← Real.log_div hy0.ne' hc0.ne', abs_le]
  constructor
  · have h2 : (‖y‖ / ‖c‖)⁻¹ ≤ 2 := by
      rw [inv_div, div_le_iff₀ hy0]
      linarith
    linarith [Real.one_sub_inv_le_log_of_pos hq]
  · have h2 : ‖y‖ / ‖c‖ ≤ 2 := by
      rw [div_le_iff₀ hc0]
      linarith
    linarith [Real.log_le_sub_one_of_pos hq]

/-- The mean of `|log ‖·‖ - a|` over a ball, for a suitable constant `a`, is at most `3ⁿ`. -/
private theorem exists_setLAverage_enorm_log_norm_sub_le [Nontrivial E] (c : E) {r : ℝ}
    (hr : 0 < r) :
    ∃ a : ℝ, ⨍⁻ y in ball c r, ‖Real.log ‖y‖ - a‖ₑ ∂μ ≤ 3 ^ finrank ℝ E := by
  rcases le_or_gt (2 * r) ‖c‖ with hc | hc
  · -- Away from the origin, `log ‖·‖` is within `1` of `log ‖c‖`.
    refine ⟨Real.log ‖c‖, (laverage_le_essSup _).trans (essSup_le_of_ae_le _ ?_)⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have habs := abs_log_norm_sub_log_norm_le_one (mem_ball_iff_norm.1 hy) hc
    rw [Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_one.2 habs).trans (one_le_pow₀ (by norm_num))
  · -- Near the origin, `B(c, r) ⊆ B(0, 3r)` and `log ‖·‖` is within `1` of `log (3r)` in mean
    -- over `B(0, 3r)`.
    refine ⟨Real.log (3 * r), ?_⟩
    have hsub : ball c r ⊆ ball (0 : E) (3 * r) := by
      intro y hy
      rw [mem_ball_zero_iff]
      have := norm_le_insert' y c
      linarith [mem_ball_iff_norm.1 hy]
    have hball : μ (ball (0 : E) (3 * r)) = 3 ^ finrank ℝ E * μ (ball c r) := by
      rw [Measure.addHaar_ball_mul_of_pos μ 0 three_pos, Measure.addHaar_ball_center μ c,
        ENNReal.ofReal_pow zero_le_three, ENNReal.ofReal_ofNat]
    rw [setLAverage_eq]
    refine ENNReal.div_le_of_le_mul ?_
    calc ∫⁻ y in ball c r, ‖Real.log ‖y‖ - Real.log (3 * r)‖ₑ ∂μ
        ≤ ∫⁻ y in ball (0 : E) (3 * r), ‖Real.log ‖y‖ - Real.log (3 * r)‖ₑ ∂μ :=
          lintegral_mono_set hsub
      _ ≤ μ (ball (0 : E) (3 * r)) := setLIntegral_enorm_log_norm_sub_log_le (by positivity)
      _ = 3 ^ finrank ℝ E * μ (ball c r) := hball

/-- **`log ‖x‖` has bounded mean oscillation**, with `‖log ‖·‖‖_{BMO} ≤ 2 · 3ⁿ` on a
finite-dimensional real normed space of dimension `n` with an additive Haar measure. -/
theorem bmoSeminorm_log_norm_le :
    bmoSeminorm (fun x : E => Real.log ‖x‖) μ ≤ 2 * 3 ^ finrank ℝ E := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h : (fun x : E => Real.log ‖x‖) = fun _ => 0 := by
      funext x
      rw [Subsingleton.elim x 0, norm_zero, Real.log_zero]
    rw [h, bmoSeminorm_const]
    exact zero_le
  refine bmoSeminorm_le fun c r => ?_
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  obtain ⟨a, ha⟩ := exists_setLAverage_enorm_log_norm_sub_le (μ := μ) c hr
  have hint : IntegrableOn (fun x : E => Real.log ‖x‖) (ball c r) μ :=
    (locallyIntegrable_log_norm.integrableOn_isCompact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  exact (setLAverage_enorm_sub_setAverage_le hint a).trans (by gcongr)

/-- **`log ‖x‖` has bounded mean oscillation** on a finite-dimensional real normed space with an
additive Haar measure. -/
theorem memBMO_log_norm : MemBMO (fun x : E => Real.log ‖x‖) μ :=
  memBMO_iff.2 ⟨locallyIntegrable_log_norm, bmoSeminorm_log_norm_le.trans_lt (by finiteness)⟩

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- For every constant `a`, the ball `B(0, r)` contains a ball of radius `r / 8` on which `log ‖·‖`
stays at distance at least `log 2 / 2` from `a`. -/
private theorem exists_forall_mem_ball_ofReal_le_enorm_log_norm_sub [Nontrivial E] (a : ℝ)
    {r : ℝ} (hr : 0 < r) : ∃ z : E, ball z (r / 8) ⊆ ball 0 r ∧
      ∀ y ∈ ball z (r / 8), ENNReal.ofReal (Real.log 2 / 2) ≤ ‖Real.log ‖y‖ - a‖ₑ := by
  set δ := Real.log 2 / 2 with hδ
  have hsub {z : E} (hz : ‖z‖ ≤ 3 / 4 * r) : ball z (r / 8) ⊆ ball 0 r := fun y hy => by
    rw [mem_ball_zero_iff]
    linarith [norm_le_insert' y z, mem_ball_iff_norm.1 hy]
  have h42 : Real.log (r / 2) = Real.log (r / 4) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) two_ne_zero]
    congr 1
    ring
  rcases le_or_gt (Real.log (r / 4) + δ) a with ha | ha
  · -- `a` lies above the values of `log ‖·‖` on a ball of points of norm in `(0, r / 4)`.
    obtain ⟨z, hz⟩ := exists_norm_eq E (by positivity : 0 ≤ r / 8)
    refine ⟨z, hsub (by rw [hz]; linarith), fun y hy => ?_⟩
    have hyz := mem_ball_iff_norm.1 hy
    have hy0 : 0 < ‖y‖ := by linarith [norm_le_insert' z y, norm_sub_rev y z]
    have hlog := Real.log_lt_log hy0 (by linarith [norm_le_insert' y z] : ‖y‖ < r / 4)
    rw [Real.enorm_eq_ofReal_abs, abs_sub_comm]
    exact ENNReal.ofReal_le_ofReal ((by linarith : δ ≤ a - Real.log ‖y‖).trans (le_abs_self _))
  · -- `a` lies below the values of `log ‖·‖` on a ball of points of norm in `(r / 2, r)`.
    obtain ⟨z, hz⟩ := exists_norm_eq E (by positivity : 0 ≤ 3 / 4 * r)
    refine ⟨z, hsub hz.le, fun y hy => ?_⟩
    have hyz := mem_ball_iff_norm.1 hy
    have hlog := Real.log_lt_log (by positivity)
      (by linarith [norm_le_insert' z y, norm_sub_rev y z] : r / 2 < ‖y‖)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ((by linarith : δ ≤ Real.log ‖y‖ - a).trans (le_abs_self _))

/-- **The mean oscillation of `log ‖x‖` does not vanish on small balls.** On a nontrivial
finite-dimensional real normed space of dimension `n` with an additive Haar measure, the mean
oscillation of `log ‖·‖` on every ball centred at the origin is at least `log 2 / (2 · 8ⁿ)`. -/
theorem ofReal_le_setLAverage_enorm_log_norm_sub_setAverage_ball_zero [Nontrivial E] {r : ℝ}
    (hr : 0 < r) :
    ENNReal.ofReal (Real.log 2 / (2 * 8 ^ finrank ℝ E)) ≤
      ⨍⁻ y in ball (0 : E) r,
        ‖Real.log ‖y‖ - ⨍ z in ball (0 : E) r, Real.log ‖z‖ ∂μ‖ₑ ∂μ := by
  set a := ⨍ z in ball (0 : E) r, Real.log ‖z‖ ∂μ
  obtain ⟨z, hsub, hz⟩ := exists_forall_mem_ball_ofReal_le_enorm_log_norm_sub (E := E) a hr
  have hball : μ (ball (0 : E) r) = 8 ^ finrank ℝ E * μ (ball z (r / 8)) := by
    have h8 := Measure.addHaar_ball_mul_of_pos μ (0 : E) (by norm_num : (0 : ℝ) < 8) (r / 8)
    rw [show (8 : ℝ) * (r / 8) = r by ring] at h8
    rw [Measure.addHaar_ball_center μ z, h8, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  have hpos : μ (ball (0 : E) r) ≠ 0 := (measure_ball_pos μ 0 hr).ne'
  have htop : μ (ball (0 : E) r) ≠ ∞ := measure_ball_lt_top.ne
  rw [setLAverage_eq, ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl htop)]
  calc ENNReal.ofReal (Real.log 2 / (2 * 8 ^ finrank ℝ E)) * μ (ball (0 : E) r)
      = ENNReal.ofReal (Real.log 2 / 2) * μ (ball z (r / 8)) := by
        rw [hball, ← mul_assoc, ← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
    _ = ∫⁻ _ in ball z (r / 8), ENNReal.ofReal (Real.log 2 / 2) ∂μ := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in ball z (r / 8), ‖Real.log ‖y‖ - a‖ₑ ∂μ :=
        setLIntegral_mono' measurableSet_ball hz
    _ ≤ ∫⁻ y in ball (0 : E) r, ‖Real.log ‖y‖ - a‖ₑ ∂μ := lintegral_mono_set hsub

/-- **`log ‖x‖` does not have vanishing mean oscillation** on a nontrivial finite-dimensional real
normed space with an additive Haar measure. -/
theorem not_memVMO_log_norm [Nontrivial E] :
    ¬ MemVMO (fun x : E => Real.log ‖x‖) μ := by
  intro h
  set δ := ENNReal.ofReal (Real.log 2 / (2 * 8 ^ finrank ℝ E))
  have hδ : δ ≠ 0 := by
    simp only [δ, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos (Real.log_pos one_lt_two) (by positivity)
  obtain ⟨r, hr, hle⟩ := (memVMO_iff.1 h).2 (δ / 2) (ENNReal.half_pos hδ)
  have := (ofReal_le_setLAverage_enorm_log_norm_sub_setAverage_ball_zero (μ := μ) hr).trans
    ((setLAverage_enorm_sub_setAverage_le_vmoModulus _ μ 0 le_rfl).trans hle)
  exact (ENNReal.half_lt_self hδ ENNReal.ofReal_ne_top).not_ge this

end TauCeti
