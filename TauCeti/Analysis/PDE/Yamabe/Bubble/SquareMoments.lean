/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Moments
import TauCeti.Analysis.PDE.Yamabe.Bubble.Decay
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Concentration of the square moments of Yamabe bubbles

For `0 ≤ p < n - 4`, the weighted square density `‖x - b‖ ^ p U_{t,b}(x)²`, divided by
`t ^ (p + 2)`, concentrates at `b`. Against any bounded measurable function continuous at `b`,
its integral converges to the value of that function at `b` times the exact beta moment.
In particular, a cutoff equal to one near the centre preserves the leading coefficient.
When the cutoff equals one on a fixed ball of radius `r > 0`, its error is bounded by
`(C + 1) (2t/r)^(n-2)` times the square moment at scale `r`, where `|χ| ≤ C`.
The case `p = 2` in dimensions at least seven has scale `t⁴`, as needed for second-order
potential terms in localized bubble energies.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §6.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11
  (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open Filter InnerProductSpace MeasureTheory Metric Module ProbabilityTheory Real Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- Outside a ball on which a bounded measurable cutoff equals one, its error in a finite
square moment is bounded by `(C + 1) * (2 * t / r) ^ (n - 2)` times the moment at scale `r`,
where `‖χ x‖ ≤ C` for every `x`. In particular the error has order `t ^ (n - 2)` at fixed
`r > 0`. -/
theorem abs_integral_cutoff_norm_sub_rpow_mul_bubble_sq_sub_le
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 0 ≤ p)
    (hpn : p < (finrank ℝ E : ℝ) - 4) {χ : E → ℝ} (hχ : Measurable χ)
    {C : ℝ} (hχC : ∀ x, ‖χ x‖ ≤ C) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (b : E) (hχone : EqOn χ 1 (ball b r)) :
    |(∫ x, χ x * (‖x - b‖ ^ p * bubble t b x ^ 2) ∂μ) -
      ∫ x, ‖x - b‖ ^ p * bubble t b x ^ 2 ∂μ| ≤
      (C + 1) * (2 * t / r) ^ (finrank ℝ E - 2) *
        ∫ x, ‖x - b‖ ^ p * bubble r b x ^ 2 ∂μ := by
  have hn : 2 ≤ finrank ℝ E := by
    exact_mod_cast (show (2 : ℝ) ≤ finrank ℝ E by linarith)
  have hC : 0 ≤ C := (norm_nonneg (χ b)).trans (hχC b)
  have hMt := integrable_norm_sub_rpow_mul_bubble_sq μ hp hpn ht b
  have hMr := integrable_norm_sub_rpow_mul_bubble_sq μ hp hpn hr b
  have hcut := hMt.bdd_mul hχ.aestronglyMeasurable (.of_forall hχC)
  rw [← integral_sub hcut hMt, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans
    (integral_mono (hcut.sub hMt).abs (hMr.const_mul _) fun x ↦ ?_)
  by_cases hx : x ∈ ball b r
  · rw [hχone hx, Pi.one_apply, one_mul, sub_self, abs_zero]
    positivity
  · have hnorm : r ≤ ‖x - b‖ := by
      simpa only [mem_ball, dist_eq_norm, not_lt] using hx
    have hχsub : |χ x - 1| ≤ C + 1 := by
      calc
        |χ x - 1| ≤ |χ x| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ C + 1 := add_le_add (by simpa only [Real.norm_eq_abs] using hχC x) (by norm_num)
    rw [← sub_one_mul, abs_mul, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg (x - b)) p) (sq_nonneg (bubble t b x)))]
    calc
      |χ x - 1| * (‖x - b‖ ^ p * bubble t b x ^ 2)
          ≤ (C + 1) * (‖x - b‖ ^ p *
            ((2 * t / r) ^ (finrank ℝ E - 2) * bubble r b x ^ 2)) := by
        gcongr
        exact bubble_sq_le_mul_of_le_norm_sub hn ht hr hnorm
      _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- Every finite square moment, normalized by its scale, converges against a bounded measurable
weight continuous at the bubble centre to the weight's value times the exact beta moment. -/
theorem tendsto_integral_mul_norm_sub_rpow_mul_bubble_sq_div
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 0 ≤ p)
    (hpn : p < (finrank ℝ E : ℝ) - 4) {χ : E → ℝ} (hχ : Measurable χ)
    {C : ℝ} (hχC : ∀ x, ‖χ x‖ ≤ C) (b : E) (hχb : ContinuousAt χ b) :
    Tendsto (fun t : ℝ ↦
      (∫ x, χ x * (‖x - b‖ ^ p * bubble t b x ^ 2) ∂μ) / t ^ (p + 2))
      (𝓝[>] 0) (𝓝 (χ b * ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) *
          beta (((finrank ℝ E : ℝ) + p) / 2) (((finrank ℝ E : ℝ) - p - 4) / 2))))) := by
  have hn : 0 < finrank ℝ E := by
    exact_mod_cast (show (0 : ℝ) < finrank ℝ E by linarith)
  let _ := Module.finite_of_finrank_pos (R := ℝ) (M := E) hn
  let J : E → ℝ := fun z ↦ ‖z‖ ^ p * bubble 1 0 z ^ 2
  have hJ : Integrable J μ := by
    simpa only [sub_zero] using integrable_norm_sub_rpow_mul_bubble_sq μ hp hpn zero_lt_one 0
  have hlim : Tendsto (fun t : ℝ ↦ ∫ z, χ (b + t • z) * J z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z, χ b * J z ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ C * ‖J z‖)
      (.of_forall fun t ↦ ?_) (.of_forall fun t ↦ .of_forall fun z ↦ ?_)
      (hJ.norm.const_mul C) (.of_forall fun z ↦ ?_)
    · exact ((hχ.comp (by fun_prop)).aestronglyMeasurable).mul hJ.aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hχC _) (norm_nonneg _)
    · have ht : Tendsto (fun t : ℝ ↦ b + t • z) (𝓝[>] 0) (𝓝 b) := by
        have h : ContinuousAt (fun t : ℝ ↦ b + t • z) 0 := by fun_prop
        simpa only [zero_smul, add_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
      exact (hχb.tendsto.comp ht).mul_const _
  have hmoment : (∫ z, J z ∂μ) =
      (finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) *
          beta (((finrank ℝ E : ℝ) + p) / 2) (((finrank ℝ E : ℝ) - p - 4) / 2)) := by
    simpa only [J, sub_zero, Real.one_rpow, mul_one] using
      integral_norm_sub_rpow_mul_bubble_sq μ hp hpn zero_lt_one (0 : E)
  rw [integral_const_mul, hmoment] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [integral_mul_norm_sub_rpow_mul_bubble_sq_eq_mul μ χ p ht b,
    mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos ht _).ne']

omit [FiniteDimensional ℝ E] in
/-- A bounded measurable cutoff equal to one near the centre preserves the leading coefficient
of every finite square moment. -/
theorem tendsto_integral_cutoff_norm_sub_rpow_mul_bubble_sq_div
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 0 ≤ p)
    (hpn : p < (finrank ℝ E : ℝ) - 4) {χ : E → ℝ} (hχ : Measurable χ)
    {C : ℝ} (hχC : ∀ x, ‖χ x‖ ≤ C) (b : E) (hχone : χ =ᶠ[𝓝 b] 1) :
    Tendsto (fun t : ℝ ↦
      (∫ x, χ x * (‖x - b‖ ^ p * bubble t b x ^ 2) ∂μ) / t ^ (p + 2))
      (𝓝[>] 0) (𝓝 ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 3) *
          beta (((finrank ℝ E : ℝ) + p) / 2) (((finrank ℝ E : ℝ) - p - 4) / 2)))) := by
  simpa only [hχone.eq_of_nhds, Pi.one_apply, one_mul] using
    tendsto_integral_mul_norm_sub_rpow_mul_bubble_sq_div μ hp hpn hχ hχC b hχone.continuousAt

end TauCeti.Yamabe
