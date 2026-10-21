/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Truncated Laplace transforms of bounded functions

For `f : ℝ → ℂ`, this file studies the Laplace transform `G z = ∫ t in Ici 0, f t * exp (-z t)`
and its truncations `G_T z = ∫ t in 0..T, f t * exp (-z t)`:

* each truncation is entire (`differentiable_intervalIntegral_mul_cexp_neg_mul`), and, for `f`
  bounded on `[0, ∞)`, the full transform is holomorphic on `0 < re z`
  (`differentiableOn_integral_mul_cexp_neg_mul`), being a locally uniform limit of truncations;
* if `‖f‖ ≤ M` on `[0, ∞)`, the tail bound `‖G z - G_T z‖ ≤ M exp (-T re z) / re z` holds for
  `0 < re z` (`norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le`), and if `‖f‖ ≤ M` on
  `[0, T]`, then `‖G_T z‖ ≤ M exp (-T re z) / (-re z)` for `re z < 0`
  (`norm_intervalIntegral_mul_cexp_neg_mul_le_of_re_neg`).

These are the analytic inputs of Newman's contour argument for his Tauberian theorem.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Complex Interval

namespace TauCeti

variable {f : ℝ → ℂ} {M T : ℝ}

/-- **Truncated Laplace transforms are entire.** If `f` is interval integrable on `[a, b]`, then
`z ↦ ∫ t in a..b, f t * exp (-z t)` is complex differentiable everywhere. -/
theorem differentiable_intervalIntegral_mul_cexp_neg_mul {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    Differentiable ℂ fun z : ℂ ↦ ∫ t in a..b, f t * cexp (-z * t) := by
  intro z₀
  -- On `Ι a b` we have `|t| ≤ C` and, for `z` within distance `1` of `z₀`, `‖exp (-z t)‖ ≤ K`;
  -- so the `z`-derivative `-t f t exp (-z t)` of the integrand is dominated by `C * K * ‖f t‖`.
  set C := max |a| |b|
  set K := Real.exp ((‖z₀‖ + 1) * C)
  have habs : ∀ t ∈ Ι a b, |t| ≤ C := by
    intro t ht
    rcases le_total a b with hab | hab
    · rw [uIoc_of_le hab] at ht
      exact abs_le_max_abs_abs ht.1.le ht.2
    · rw [uIoc_of_ge hab] at ht
      exact (abs_le_max_abs_abs ht.1.le ht.2).trans_eq (max_comm _ _)
  have hexp : ∀ t ∈ Ι a b, ∀ z ∈ ball z₀ 1, ‖cexp (-z * t)‖ ≤ K := by
    intro t ht z hz
    rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
    refine Real.exp_le_exp.mpr ?_
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le z z₀
      rw [mem_ball_iff_norm] at hz
      linarith
    calc -z.re * t ≤ |z.re| * |t| := (le_abs_self _).trans_eq (by rw [abs_mul, abs_neg])
      _ ≤ (‖z₀‖ + 1) * C :=
          mul_le_mul ((Complex.abs_re_le_norm z).trans hz') (habs t ht) (abs_nonneg _)
            (by positivity)
  have hcont : ∀ z : ℂ, Continuous fun t : ℝ ↦ cexp (-z * t) := fun z ↦ by fun_prop
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun z t ↦ f t * (cexp (-z * t) * (-(t : ℂ))))
    (bound := fun t ↦ C * K * ‖f t‖) (ball_mem_nhds z₀ one_pos)
    (.of_forall fun z ↦ hf.def'.aestronglyMeasurable.mul (hcont z).aestronglyMeasurable)
    (hf.mul_continuousOn (hcont z₀).continuousOn)
    (hf.def'.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ ↦
      cexp (-z₀ * t) * (-(t : ℂ))).aestronglyMeasurable)
    (.of_forall fun t ht z hz ↦ ?_) (hf.norm.const_mul _)
    (.of_forall fun t _ z _ ↦ ?_)).2.differentiableAt
  · rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    calc ‖f t‖ * (‖cexp (-z * t)‖ * |t|) ≤ ‖f t‖ * (K * C) := by
          gcongr
          exacts [hexp t ht z hz, habs t ht]
      _ = C * K * ‖f t‖ := by ring
  · have h := ((hasDerivAt_id' z).neg.mul_const (t : ℂ)).cexp.const_mul (f t)
    simpa using h

/-- Pointwise bound on the Laplace integrand: if `‖w‖ ≤ M`, then
`‖w * exp (-z t)‖ ≤ M * exp (-re z * t)` for real `t`. -/
theorem norm_mul_cexp_neg_mul_le {w z : ℂ} {t : ℝ} (h : ‖w‖ ≤ M) :
    ‖w * cexp (-z * t)‖ ≤ M * Real.exp (-z.re * t) := by
  rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- For `0 < re z`, the Laplace integrand of a function bounded on `[0, ∞)` is integrable there. -/
theorem integrableOn_mul_cexp_neg_mul (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ ↦ f t * cexp (-z * t)) (Ici 0) := by
  refine Integrable.mono' (((integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (exp_neg_integrableOn_Ioi 0 hz)).const_mul M)
    (hf.mul (by fun_prop : Continuous fun t : ℝ ↦ cexp (-z * t)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ici fun t ht ↦ ?_)
  exact norm_mul_cexp_neg_mul_le (hbound t ht)

/-- **Tail bound.** For `0 < re z` and `0 ≤ T`, the Laplace transform of a function bounded by
`M` on `[0, ∞)` differs from its truncation at `T` by at most `M exp (-T re z) / re z`. -/
theorem norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} (hz : 0 < z.re) (hT : 0 ≤ T) :
    ‖(∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖ ≤
      M * Real.exp (-z.re * T) / z.re := by
  have hint := integrableOn_mul_cexp_neg_mul hf hbound hz
  rw [integral_Ici_eq_integral_Ioi, ← intervalIntegral.integral_interval_add_Ioi
    ((integrableOn_Ici_iff_integrableOn_Ioi).mp hint) (hint.mono_set (Ioi_subset_Ici hT)),
    add_sub_cancel_left]
  calc ‖∫ t in Ioi T, f t * cexp (-z * t)‖ ≤ ∫ t in Ioi T, M * Real.exp (-z.re * t) := by
        refine norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (by linarith) T).const_mul M)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
            norm_mul_cexp_neg_mul_le (hbound t (hT.trans (le_of_lt ht))))
    _ = M * Real.exp (-z.re * T) / z.re := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith), neg_div_neg_eq, mul_div_assoc]

/-- **Left half-plane bound.** For `re z < 0` and `0 ≤ T`, the truncated Laplace transform of a
function bounded by `M` on `[0, T]` is at most `M exp (-T re z) / (-re z)`. -/
theorem norm_intervalIntegral_mul_cexp_neg_mul_le_of_re_neg
    (hbound : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) {z : ℂ} (hz : z.re < 0) (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖ ≤ M * Real.exp (-z.re * T) / -z.re := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 ⟨le_rfl, hT⟩)
  have hg : IntegrableOn (fun t : ℝ ↦ M * Real.exp (-z.re * t)) (Iic T) :=
    (integrableOn_exp_mul_Iic (by linarith) T).const_mul M
  calc ‖∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖
      ≤ ∫ t in (0 : ℝ)..T, M * Real.exp (-z.re * t) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall fun t ht ↦
          norm_mul_cexp_neg_mul_le (hbound t (Ioc_subset_Icc_self ht)))
          ((by fun_prop : Continuous fun t : ℝ ↦ M * Real.exp (-z.re * t)).intervalIntegrable _ _)
    _ ≤ ∫ t in Iic T, M * Real.exp (-z.re * t) := by
        rw [intervalIntegral.integral_of_le hT]
        exact setIntegral_mono_set hg (.of_forall fun t ↦ by positivity)
          (.of_forall fun t ht ↦ (Ioc_subset_Iic_self ht : t ∈ Iic T))
    _ = M * Real.exp (-z.re * T) / -z.re := by
        rw [integral_const_mul, integral_exp_mul_Iic (by linarith), mul_div_assoc]

/-- **Holomorphy of the Laplace transform.** If `f` is bounded on `[0, ∞)`, its Laplace transform
`z ↦ ∫ t in Ici 0, f t * exp (-z t)` is complex differentiable on the half-plane `0 < re z`. -/
theorem differentiableOn_integral_mul_cexp_neg_mul
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) {z | 0 < z.re} := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 (mem_Ici.mpr le_rfl))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  -- The truncations at `n : ℕ` converge to the transform uniformly on each `{c < re z}`.
  have hloc (n : ℕ) : IntervalIntegrable f volume 0 n := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le n.cast_nonneg).mpr
      (Integrable.mono' (integrableOn_const measure_Ioc_lt_top.ne (C := M))
        (hf.mono_set (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self))
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hbound t (le_of_lt ht.1)))
  refine TendstoLocallyUniformlyOn.differentiableOn (φ := atTop)
    (F := fun (n : ℕ) (z : ℂ) ↦ ∫ t in (0 : ℝ)..n, f t * cexp (-z * t)) ?_
    (.of_forall fun n ↦
      (differentiable_intervalIntegral_mul_cexp_neg_mul (hloc n)).differentiableOn) hopen
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε z₀ hz₀
  have hc : 0 < z₀.re / 2 := half_pos hz₀
  refine ⟨{z | z₀.re / 2 < z.re}, mem_nhdsWithin_of_mem_nhds
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_lt_self hz₀)), ?_⟩
  have hlim : Tendsto (fun n : ℕ ↦ M * Real.exp (-(z₀.re / 2) * n) / (z₀.re / 2)) atTop (𝓝 0) := by
    have := ((Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg
      (neg_lt_zero.mpr hc))).const_mul M).div_const (z₀.re / 2)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  calc _ ≤ M * Real.exp (-z.re * n) / z.re :=
        norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le hf hbound (hc.trans hz) n.cast_nonneg
    _ ≤ M * Real.exp (-(z₀.re / 2) * n) / (z₀.re / 2) := by
        gcongr

end TauCeti
