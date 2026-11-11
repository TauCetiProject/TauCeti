/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Disc.Regularity
public import TauCeti.MeasureTheory.Integral.NormRpow
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Sharp global integrability for the disc indicator Cauchy integral

For a nonzero disc the actual normalized Cauchy integral belongs to finite positive `Lp`
exactly when `p>2`; its actual holomorphic Wirtinger derivative belongs exactly when `p>1`.
The borderline divergence comes from the exact reciprocal and reciprocal square tails.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2. The explicit disc calculation gives
  the sharp endpoint examples for this Cauchy–Beurling framework.
-/

public noncomputable section

open Complex MeasureTheory Metric Set
open scoped Real ENNReal Topology ComplexConjugate

namespace TauCeti

/-- On a nondegenerate disc the actual Cauchy integral is globally `Lp` exactly above exponent
two. Exponent zero and infinity are deliberately excluded from this finite positive assertion. -/
theorem memLp_pi_inv_mul_integral_sub_inv_ball_iff {r : ℝ} (hr : 0 < r) (c : ℂ)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    MemLp (fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w - z)⁻¹) p volume ↔ 2 < p.toReal := by
  have htrans := (MeasurableEquiv.addLeft c).memLp_map_measure_iff
    (g := fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w - z)⁻¹) (p := p) (μ := volume)
  have hpres : MeasurePreserving (MeasurableEquiv.addLeft c : ℂ → ℂ) volume volume :=
    measurePreserving_add_left volume c
  rw [hpres.map_eq] at htrans
  have heq : (fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w - z)⁻¹) ∘
      (MeasurableEquiv.addLeft c : ℂ → ℂ) =
      (fun w => (π : ℂ)⁻¹ * ∫ z in ball (0 : ℂ) r, (w - z)⁻¹) := by
    funext w
    dsimp only [Function.comp_apply]
    rw [pi_inv_mul_integral_sub_inv_ball hr.le, pi_inv_mul_integral_sub_inv_ball_zero hr.le]
    simp
  rw [heq] at htrans
  apply htrans.trans
  let f : ℂ → ℂ := fun w => (π : ℂ)⁻¹ * ∫ z in ball (0 : ℂ) r, (w - z)⁻¹
  have hm : AEStronglyMeasurable f volume :=
    (lipschitzWith_pi_inv_mul_integral_sub_inv_ball hr.le 0).continuous.aestronglyMeasurable
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) r)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hlocal : MemLp f p (volume.restrict (closedBall 0 r)) :=
    MemLp.of_bound (hm.mono_measure Measure.restrict_le_self) r
        (Filter.Eventually.of_forall (norm_pi_inv_mul_integral_sub_inv_ball_le hr.le 0))
  have hsplit : MemLp f p volume ↔ MemLp f p (volume.restrict (closedBall 0 r)ᶜ) := by
    refine ⟨fun h => h.restrict _, fun h => ?_⟩
    have ha := hlocal.add_measure h
    rwa [Measure.restrict_add_restrict_compl measurableSet_closedBall] at ha
  rw [hsplit]
  have hfun : f =ᵐ[volume.restrict (closedBall 0 r)ᶜ] (fun w => (r : ℂ)^2/w) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with w hw
    have hvalue : f w = if ‖w‖ ≤ r then conj w else (r : ℂ)^2/w :=
      pi_inv_mul_integral_sub_inv_ball_zero hr.le w
    rw [hvalue, ite_eq_right (by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right] using hw)]
  rw [memLp_congr_ae hfun]
  simpa using memLp_div_pow_compl_closedBall_iff
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr.ne')) hr 1 hp0 hp_top

/-- The actual holomorphic Wirtinger derivative has the sharp finite positive integrability
range `p>1`, independently of any separately constructed Beurling realization. -/
theorem memLp_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_iff {r : ℝ} (hr : 0 < r) (c : ℂ)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    MemLp (fun w => wirtingerDeriv
      (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w 1) p volume ↔ 1 < p.toReal := by
  rw [memLp_congr_ae (ae_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball hr.le c)]
  have htrans := (MeasurableEquiv.addLeft c).memLp_map_measure_iff
    (g := (closedBall c r)ᶜ.indicator (fun w => -(r : ℂ)^2/(w - c)^2)) (p := p) (μ := volume)
  have hpres : MeasurePreserving (MeasurableEquiv.addLeft c : ℂ → ℂ) volume volume :=
    measurePreserving_add_left volume c
  rw [hpres.map_eq] at htrans
  have heq : (closedBall c r)ᶜ.indicator (fun w => -(r : ℂ)^2/(w - c)^2) ∘
      (MeasurableEquiv.addLeft c : ℂ → ℂ) =
      (closedBall (0 : ℂ) r)ᶜ.indicator (fun w => -(r : ℂ)^2/w^2) := by
    funext w
    simp [Set.indicator, mem_closedBall, dist_eq_norm, Function.comp_apply, MeasurableEquiv.addLeft]
  rw [heq] at htrans
  refine htrans.trans ?_
  rw [memLp_indicator_iff_restrict measurableSet_closedBall.compl.nullMeasurableSet]
  rw [memLp_div_pow_compl_closedBall_iff
    (neg_ne_zero.mpr (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr.ne'))) hr 2 hp0 hp_top]
  norm_num

/-- The actual disc Cauchy integral is essentially bounded, including a degenerate disc. -/
theorem memLp_top_pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    MemLp (fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w-z)⁻¹) ∞ volume := by
  have hm : AEStronglyMeasurable
      (fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w-z)⁻¹) volume :=
    (lipschitzWith_pi_inv_mul_integral_sub_inv_ball hr c).continuous.aestronglyMeasurable
  exact memLp_top_of_bound hm r (Filter.Eventually.of_forall
    (norm_pi_inv_mul_integral_sub_inv_ball_le hr c))

/-- The actual holomorphic derivative is essentially bounded by one. -/
theorem memLp_top_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    MemLp (fun w => wirtingerDeriv
      (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v-z)⁻¹) w 1) ∞ volume := by
  rw [memLp_congr_ae (ae_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball hr c)]
  have hm : Measurable ((closedBall c r)ᶜ.indicator (fun w => -(r : ℂ)^2/(w-c)^2)) := by
    have hrat : Measurable (fun w : ℂ => -(r : ℂ)^2/(w-c)^2) := by fun_prop
    exact hrat.indicator measurableSet_closedBall.compl
  apply memLp_top_of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  by_cases hw : w ∈ (closedBall c r)ᶜ
  · rw [indicator_of_mem hw, norm_div, norm_neg, norm_pow, norm_pow, norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr]
    have hwr : r < ‖w-c‖ := by
      simpa only [mem_compl_iff, mem_closedBall_iff_norm, not_le] using hw
    have hw0 : 0 < ‖w-c‖ := hr.trans_lt hwr
    apply (div_le_iff₀ (sq_pos_of_pos hw0)).mpr
    nlinarith
  · simp [indicator_of_notMem hw]

/-- A radius-zero disc gives the zero Cauchy integral, hence belongs to every `Lp`, including
exponents zero and infinity. -/
theorem _root_.Complex.memLp_pi_inv_mul_integral_sub_inv_ball_radius_zero (c : ℂ) (p : ℝ≥0∞) :
    MemLp (fun w => (π : ℂ)⁻¹ * ∫ z in ball c 0, (w-z)⁻¹) p volume := by
  simp

/-- The holomorphic derivative of the radius-zero potential is zero at every exponent. -/
theorem _root_.Complex.memLp_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_radius_zero
    (c : ℂ) (p : ℝ≥0∞) :
    MemLp (fun w => wirtingerDeriv
      (fun v => (π : ℂ)⁻¹ * ∫ z in ball c 0, (v-z)⁻¹) w 1) p volume := by
  simp only [ball_zero, setIntegral_empty, mul_zero]
  have heq : (fun w : ℂ => wirtingerDeriv (fun _ : ℂ => (0 : ℂ)) w 1) = 0 := by
    funext w
    simp
  rw [heq]
  exact MemLp.zero

/-- No native `L¹` output can agree with the actual holomorphic derivative of a nonzero disc
potential. Thus an `L¹` extension agreeing on this indicator input is impossible. -/
theorem not_exists_L1_ae_eq_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball
    {r : ℝ} (hr : 0 < r) (c : ℂ) :
    ¬ ∃ g : Lp ℂ 1 volume, (g : ℂ → ℂ) =ᵐ[volume] (fun w => wirtingerDeriv
      (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v-z)⁻¹) w 1) := by
  rintro ⟨g, hg⟩
  have hm := (memLp_congr_ae hg).mp (Lp.memLp g)
  have hp := (memLp_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_iff hr c
    one_ne_zero (by simp)).mp hm
  norm_num at hp

end TauCeti
