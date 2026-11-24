/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Sobolev.Sharp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic

/-!
# Sharpness of the BV Sobolev constant

Scalar multiples of ball indicators attain the critical BV Sobolev bound. Mollifying an
indicator and normalizing its critical norm gives nonnegative compactly supported smooth
near-extremizers. Thus the constant is optimal even on compactly supported smooth functions,
although the ball indicator itself is discontinuous.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*,
  Theorem 12.37 (the sharp BV Sobolev inequality).
-/

public noncomputable section

open MeasureTheory Metric Module Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Topology Convolution ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0}

/-- Every scalar multiple of a ball indicator attains the critical BV Sobolev bound.
Zero scalars and empty balls are included. -/
theorem mul_eLpNorm_smul_indicator_ball_eq_totalVariationOn
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (a : ℝ) (c : E) (r : ℝ) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^
        (finrank ℝ E : ℝ)⁻¹) * eLpNorm (a • (ball c r).indicator (1 : E → ℝ)) p volume =
      totalVariationOn volume ⊤ (a • (ball c r).indicator (1 : E → ℝ)) := by
  by_cases hr : 0 < r
  swap
  · simp only [ball_eq_empty.2 (not_lt.1 hr), indicator_empty, ← Pi.zero_def, smul_zero,
      eLpNorm_zero, totalVariationOn_zero, mul_zero]
  have hn : finrank ℝ E ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.symm.pos.ne'
  have hpower : 1 / (p : ℝ) = 1 - (finrank ℝ E : ℝ)⁻¹ := by
    simpa only [one_div, NNReal.coe_natCast] using hp.coe.one_sub_inv.symm
  have hball : ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^
      (finrank ℝ E : ℝ)⁻¹ * volume.real (ball c r) ^ (1 - (finrank ℝ E : ℝ)⁻¹)) =
      perimeter volume ⊤ (ball c r) := by
    apply ENNReal.rpow_left_injective (x := (finrank ℝ E : ℝ)) (by exact_mod_cast hn)
    simp only [ENNReal.rpow_natCast]
    rw [← ENNReal.ofReal_pow (by positivity),
      ← finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal measure_ball_lt_top.ne hn,
      perimeter_ball_pow hn hr]
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
    measureReal_nonneg _)), ← ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg
      (by rw [← hpower]; positivity), ofReal_measureReal measure_ball_lt_top.ne,
    ← hpower, perimeter_def] at hball
  simp only [Pi.one_def] at hball ⊢
  rw [eLpNorm_const_smul, totalVariationOn_smul, eLpNorm_indicator_const
    measurableSet_ball.nullMeasurableSet hp0 ENNReal.coe_ne_top]
  simp only [eNorm_one, one_mul, ENNReal.coe_toReal]
  rw [mul_left_comm, hball]

private theorem exists_smooth_ball_approximation
    (hp : 1 ≤ (p : ℝ≥0∞)) (c : E) (r : ℝ) :
    ∃ w : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (w n) ∧ HasCompactSupport (w n) ∧
        (∀ x, 0 ≤ w n x) ∧ MemLp (w n) p volume) ∧
      Tendsto (fun n => eLpNorm (w n - (ball c r).indicator 1) p volume) atTop (𝓝 0) ∧
      Tendsto (fun n => totalVariationOn volume ⊤ (w n)) atTop
        (𝓝 (perimeter volume ⊤ (ball c r))) := by
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨hp⟩
  let f : E → ℝ := (ball c r).indicator 1
  have hf : MemLp f p volume :=
    memLp_indicator_const _ measurableSet_ball.nullMeasurableSet 1 (Or.inr measure_ball_lt_top.ne)
  have hi : Integrable f :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  have hc : HasCompactSupport f := .of_support_subset_isCompact (isCompact_closedBall c r)
    (support_indicator_subset.trans ball_subset_closedBall)
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let w (n : ℕ) : E → ℝ := (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] f
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) ∧ HasCompactSupport (w n) :=
    ⟨(φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hi.locallyIntegrable, (φ n).hasCompactSupport_normed.convolution _ hc⟩
  refine ⟨w, fun n => ⟨(hw n).1, (hw n).2, ?_, ?_⟩,
    tendsto_eLpNorm_normed_convolution_sub ENNReal.coe_ne_top hφ hf,
    ?_⟩
  · intro x
    exact integral_nonneg fun t => mul_nonneg ((φ n).nonneg_normed _) (indicator_nonneg
      (fun _ _ => zero_le_one) _)
  · exact (Lp.memLp ((normedBumpLp ENNReal.coe_ne_top (φ n) volume) (hf.toLp f))).ae_eq
      (normedBumpLp_ae_eq_convolution ENNReal.coe_ne_top (φ n) hf)
  · rw [perimeter_def]
    exact tendsto_totalVariationOn_normed_convolution hφ hi.locallyIntegrable

/-- Nonnegative compactly supported smooth functions with critical norm exactly one approach
any normalized positive-radius ball indicator in `Lᵖ`, and their total variations tend to the
sharp constant `n ωₙ^(1/n)`. No smooth function is asserted to attain that constant. -/
theorem exists_contDiff_near_extremizers_sharp_sobolev
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧ ∃ u : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n) ∧
        (∀ x, 0 ≤ u n x) ∧ eLpNorm (u n) p volume = 1) ∧
      Tendsto (fun n => eLpNorm (u n - a • (ball c r).indicator 1) p volume) atTop (𝓝 0) ∧
      Tendsto (fun n => totalVariationOn volume ⊤ (u n)) atTop
        (𝓝 (ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^
          (finrank ℝ E : ℝ)⁻¹))) := by
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp.symm.lt.le⟩
  let f : E → ℝ := (ball c r).indicator 1
  have hf : MemLp f p volume :=
    memLp_indicator_const _ measurableSet_ball.nullMeasurableSet 1 (Or.inr measure_ball_lt_top.ne)
  have hF : 0 < ‖hf.toLp f‖ := by
    have hμ := Metric.measure_ball_pos (μ := volume) c hr
    rw [Lp.norm_toLp]
    apply ENNReal.toReal_pos _ hf.eLpNorm_ne_top
    simp only [f, Pi.one_def, eLpNorm_indicator_const measurableSet_ball.nullMeasurableSet
      (by exact_mod_cast hp.symm.pos.ne') ENNReal.coe_ne_top, eNorm_one, one_mul, ne_eq]
    positivity
  obtain ⟨w, hw, hconv, hvar⟩ :=
    exists_smooth_ball_approximation (by exact_mod_cast hp.symm.lt.le) c r
  let W (n : ℕ) := (hw n).2.2.2.toLp (w n)
  have hW : Tendsto W atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm W f hf).2 (hconv.congr fun n =>
      (eLpNorm_congr_ae ((hw n).2.2.2.coeFn_toLp.sub (Filter.EventuallyEq.refl _ _))).symm)
  -- Discard an initial segment before normalizing, so every critical norm is nonzero.
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hW.norm.eventually (lt_mem_nhds hF))
  let b (n : ℕ) : ℝ := ‖W (n + N)‖⁻¹
  have hb : Tendsto b atTop (𝓝 ‖hf.toLp f‖⁻¹) :=
    (hW.norm.comp (tendsto_add_atTop_nat N)).inv₀ hF.ne'
  have hbpos (n : ℕ) : 0 < b n := inv_pos.2 (hN _ (Nat.le_add_left N n))
  let u (n : ℕ) := b n • w (n + N)
  have hu (n : ℕ) : ((hw (n + N)).2.2.2.const_smul (b n)).toLp (u n) = b n • W (n + N) :=
    MemLp.toLp_const_smul _ _
  refine ⟨_, inv_pos.2 hF, u, fun n => ⟨(hw (n + N)).1.const_smul (b n),
    (hw (n + N)).2.1.smul_left,
    fun x => mul_nonneg (hbpos n).le ((hw (n + N)).2.2.1 x), ?_⟩, ?_, ?_⟩
  · rw [← Lp.eNorm_toLp ((hw (n + N)).2.2.2.const_smul (b n)), hu n, ← ofReal_norm,
      norm_smul, Real.norm_eq_abs, abs_of_pos (hbpos n), inv_mul_cancel₀
        (ne_of_gt (hN _ (Nat.le_add_left N n))), ENNReal.ofReal_one]
  · have h := hb.smul (hW.comp (tendsto_add_atTop_nat N))
    rw [← hf.toLp_const_smul] at h
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ _).1 h |>.congr
    intro n
    exact eLpNorm_congr_ae (((hw (n + N)).2.2.2.const_smul (b n)).coeFn_toLp.sub
      (Filter.EventuallyEq.refl _ _))
  · have h := ENNReal.Tendsto.mul (ENNReal.tendsto_ofReal hb) (Or.inr (by
      rw [perimeter_ball hr]; finiteness)) (hvar.comp (tendsto_add_atTop_nat N))
      (Or.inr ENNReal.ofReal_ne_top)
    have hnorm : ENNReal.ofReal ‖hf.toLp f‖ = eLpNorm f p volume := by
      rw [Lp.norm_toLp, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
    have heq := mul_eLpNorm_smul_indicator_ball_eq_totalVariationOn hp 1 c r
    simp only [one_smul, ← perimeter_def] at heq
    rw [ENNReal.ofReal_inv_of_pos hF, hnorm, ← heq, mul_left_comm,
      ENNReal.inv_mul_cancel (by rw [← hnorm]; positivity) hf.eLpNorm_ne_top, mul_one] at h
    exact h.congr fun n => by
      simp only [u, totalVariationOn_smul, Function.comp_apply, Real.eNorm_of_nonneg (hbpos n).le]

/-- The coefficient `n ωₙ^(1/n)` in `C ‖u‖ₚ ≤ |Du|` cannot be increased even when the test
functions are restricted to nonnegative compactly supported smooth functions. -/
theorem le_sharp_sobolev_const_of_forall_contDiff
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) {C : ℝ≥0∞}
    (hC : ∀ u : E → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ x, 0 ≤ u x) → C * eLpNorm u p volume ≤ totalVariationOn volume ⊤ u) :
    C ≤ ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^
      (finrank ℝ E : ℝ)⁻¹) := by
  obtain ⟨a, -, u, hu, -, hvar⟩ :=
    exists_contDiff_near_extremizers_sharp_sobolev hp (0 : E) one_pos
  refine ge_of_tendsto hvar (.of_forall fun n => ?_)
  have h := hC (u n) (hu n).1 (hu n).2.1 (hu n).2.2.1
  simpa only [(hu n).2.2.2, mul_one] using h

end TauCeti
