/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.MeasureTheory.Integral.Entropy
public import TauCeti.MeasureTheory.Integral.Dilation
public import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Poincaré and logarithmic Sobolev inequalities

A probability measure `μ` on a normed space `E` satisfies the **Poincaré inequality** with constant
`C` if `Var_μ(f) ≤ C ∫ ‖∇f‖² dμ`, and the **logarithmic Sobolev inequality** with constant `C` if
`Ent_μ(f²) ≤ 2 C ∫ ‖∇f‖² dμ`, where `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`, for every
smooth test function `f` for which the quantities involved are integrable. The norm `‖∇f x‖` of the
gradient is the operator norm `‖fderiv ℝ f x‖`.

## Main definitions

* `MeasureTheory.Measure.PoincareInequality`: the Poincaré inequality with constant `C`.
* `MeasureTheory.Measure.LogSobolevInequality`: the logarithmic Sobolev inequality with constant
  `C`.

## Main results

* `MeasureTheory.Measure.PoincareInequality.mono` and
  `MeasureTheory.Measure.LogSobolevInequality.mono`: the inequalities persist for larger constants.
* `MeasureTheory.Measure.PoincareInequality.map_smul` and
  `MeasureTheory.Measure.LogSobolevInequality.map_smul`: dilating the measure by `a ≠ 0`
  multiplies the constant by `a ^ 2`.
* `TauCeti.Probability.not_poincareInequality_bernoulliMeasure`: a two-point measure `p δ₁ +
  (1 - p) δ₀` on `ℝ` with `0 < p < 1` satisfies no Poincaré inequality.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, §2.3.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped ContDiff unitInterval

namespace MeasureTheory.Measure

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The measure `μ` on `E` satisfies the **Poincaré inequality** with constant `C`:
`Var_μ(f) ≤ C ∫ ‖∇f‖² dμ` for every smooth `f` with `f` and `‖∇f‖` square-integrable. -/
def PoincareInequality (μ : Measure E) (C : ℝ) : Prop :=
  ∀ f : E → ℝ, ContDiff ℝ ∞ f → MemLp f 2 μ → MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ →
    variance f μ ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ

/-- The defining condition for the Poincaré inequality. -/
theorem PoincareInequality_def (μ : Measure E) (C : ℝ) :
    PoincareInequality μ C ↔
      ∀ f : E → ℝ, ContDiff ℝ ∞ f → MemLp f 2 μ →
        MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ →
          variance f μ ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  constructor <;> intro h f hf hfL hdf
  · exact h f hf hfL hdf
  · exact h f hf hfL hdf

/-- Apply a Poincaré inequality to an admissible test function. -/
theorem PoincareInequality.apply {μ : Measure E} {C : ℝ} (h : PoincareInequality μ C)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfL : MemLp f 2 μ)
    (hdf : MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ) :
    variance f μ ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
  h f hf hfL hdf

/-- The measure `μ` on `E` satisfies the **logarithmic Sobolev inequality** with constant `C`:
`Ent_μ(f²) ≤ 2 C ∫ ‖∇f‖² dμ` for every smooth `f` with `‖∇f‖` square-integrable and `f²` and
`f² log f²` integrable. -/
def LogSobolevInequality (μ : Measure E) (C : ℝ) : Prop :=
  ∀ f : E → ℝ, ContDiff ℝ ∞ f → MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ →
    Integrable (fun x ↦ f x ^ 2) μ → Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ →
    entropy μ (fun x ↦ f x ^ 2) ≤ 2 * C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ

/-- The defining condition for the logarithmic Sobolev inequality. -/
theorem LogSobolevInequality_def (μ : Measure E) (C : ℝ) :
    LogSobolevInequality μ C ↔
      ∀ f : E → ℝ, ContDiff ℝ ∞ f →
        MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ →
          Integrable (fun x ↦ f x ^ 2) μ →
            Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ →
              entropy μ (fun x ↦ f x ^ 2) ≤ 2 * C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  constructor <;> intro h f hf hdf hf2 hf2log
  · exact h f hf hdf hf2 hf2log
  · exact h f hf hdf hf2 hf2log

/-- Apply a logarithmic Sobolev inequality to an admissible test function. -/
theorem LogSobolevInequality.apply {μ : Measure E} {C : ℝ} (h : LogSobolevInequality μ C)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hdf : MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ) (hf2 : Integrable (fun x ↦ f x ^ 2) μ)
    (hf2log : Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ) :
    entropy μ (fun x ↦ f x ^ 2) ≤ 2 * C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
  h f hf hdf hf2 hf2log

theorem PoincareInequality.mono {μ : Measure E} {C C' : ℝ} (h : PoincareInequality μ C)
    (hC : C ≤ C') : PoincareInequality μ C' := fun f hf hfL hdf ↦
  (h f hf hfL hdf).trans
    (mul_le_mul_of_nonneg_right hC (integral_nonneg fun _ ↦ sq_nonneg _))

theorem LogSobolevInequality.mono {μ : Measure E} {C C' : ℝ} (h : LogSobolevInequality μ C)
    (hC : C ≤ C') : LogSobolevInequality μ C' := fun f hf hdf hf2 hf2log ↦
  (h f hf hdf hf2 hf2log).trans
    (mul_le_mul_of_nonneg_right (by linarith) (integral_nonneg fun _ ↦ sq_nonneg _))

end Definitions

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dilating a measure satisfying the Poincaré inequality with constant `C` by `a ≠ 0` gives a
measure satisfying it with constant `a ^ 2 * C`. -/
theorem PoincareInequality.map_smul {μ : Measure E} {C : ℝ} (h : PoincareInequality μ C) {a : ℝ}
    (ha : a ≠ 0) : PoincareInequality (μ.map (fun x ↦ a • x)) (a ^ 2 * C) := by
  have he := measurableEmbedding_const_smul₀ (α := E) ha
  intro f hf hfL hdf
  have hg : ContDiff ℝ ∞ (fun y ↦ f (a • y)) := hf.comp (contDiff_const_smul a)
  have hgL : MemLp (fun y ↦ f (a • y)) 2 μ := (he.memLp_map_measure_iff).1 hfL
  have hdg : MemLp (fun x ↦ ‖fderiv ℝ (fun y ↦ f (a • y)) x‖) 2 μ := by
    simp only [TauCeti.norm_fderiv_comp_smul a]
    exact ((he.memLp_map_measure_iff).1 hdf).const_mul |a|
  rw [variance_map hfL.aemeasurable he.measurable.aemeasurable,
    TauCeti.integral_sq_norm_fderiv_comp_smul ha]
  have := h _ hg hgL hdg
  have hpos : 0 < a ^ 2 := by positivity
  calc _ ≤ C * ∫ x, ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ ^ 2 ∂μ := this
    _ = a ^ 2 * C * ((a ^ 2)⁻¹ * ∫ x, ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ ^ 2 ∂μ) := by
      field_simp

/-- Dilating a measure satisfying the logarithmic Sobolev inequality with constant `C` by `a ≠ 0`
gives a measure satisfying it with constant `a ^ 2 * C`. -/
theorem LogSobolevInequality.map_smul {μ : Measure E} {C : ℝ} (h : LogSobolevInequality μ C)
    {a : ℝ} (ha : a ≠ 0) : LogSobolevInequality (μ.map (fun x ↦ a • x)) (a ^ 2 * C) := by
  have he := measurableEmbedding_const_smul₀ (α := E) ha
  intro f hf hdf hf2 hf2log
  have hg : ContDiff ℝ ∞ (fun y ↦ f (a • y)) := hf.comp (contDiff_const_smul a)
  have hdg : MemLp (fun x ↦ ‖fderiv ℝ (fun y ↦ f (a • y)) x‖) 2 μ := by
    simp only [TauCeti.norm_fderiv_comp_smul a]
    exact ((he.memLp_map_measure_iff).1 hdf).const_mul |a|
  rw [entropy_map he, TauCeti.integral_sq_norm_fderiv_comp_smul ha]
  have := h _ hg hdg ((he.integrable_map_iff).1 hf2) ((he.integrable_map_iff).1 hf2log)
  have hpos : 0 < a ^ 2 := by positivity
  calc _ ≤ 2 * C * ∫ x, ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ ^ 2 ∂μ := this
    _ = 2 * (a ^ 2 * C) * ((a ^ 2)⁻¹ * ∫ x, ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ ^ 2 ∂μ) := by
      field_simp

end Scaling

end MeasureTheory.Measure

namespace TauCeti.Probability

section Bernoulli

/-- A smooth function equal to `0` near `0` and to `1` near `1`. -/
private noncomputable def step (x : ℝ) : ℝ := Real.smoothTransition (3 * x - 1)

private lemma contDiff_step : ContDiff ℝ ∞ step :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private lemma fderiv_step_zero : fderiv ℝ step 0 = 0 := by
  have hthird_lt : (0 : ℝ) < 1 / 3 := by norm_num
  have : step =ᶠ[nhds 0] fun _ ↦ (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hthird_lt] with x hx
    exact Real.smoothTransition.zero_of_nonpos (by simp at hx; linarith)
  rw [this.fderiv_eq]
  simp

private lemma fderiv_step_one : fderiv ℝ step 1 = 0 := by
  have htwo_thirds_lt_one : (2 / 3 : ℝ) < 1 := by norm_num
  have : step =ᶠ[nhds 1] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds htwo_thirds_lt_one] with x hx
    exact Real.smoothTransition.one_of_one_le (by simp at hx; linarith)
  rw [this.fderiv_eq]
  simp

/-- **A two-point measure satisfies no Poincaré inequality.** For `0 < p < 1`, the measure
`p δ₁ + (1 - p) δ₀` on `ℝ` satisfies no Poincaré inequality, whatever the constant: a smooth
function equal to `0` near `0` and to `1` near `1` has variance `p (1 - p) > 0` and vanishing
gradient on the support. -/
theorem not_poincareInequality_bernoulliMeasure {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1)
    (C : ℝ) : ¬ MeasureTheory.Measure.PoincareInequality Ber((1 : ℝ), 0, p) C := by
  intro h
  have hae : ∀ᵐ x ∂Ber((1 : ℝ), 0, p), ‖fderiv ℝ step x‖ = 0 := by
    rw [bernoulliMeasure_def]
    refine ae_add_measure_iff.2 ⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩
    · rw [ae_dirac_eq]
      exact Filter.eventually_pure.2 (by simp [fderiv_step_one])
    · rw [ae_dirac_eq]
      exact Filter.eventually_pure.2 (by simp [fderiv_step_zero])
  have hstep : step 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hstep1 : step 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  have hstep_ae : step =ᵐ[Ber((1 : ℝ), 0, p)] id := by
    rw [bernoulliMeasure_def]
    refine ae_add_measure_iff.2 ⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩
    · rw [ae_dirac_eq]
      exact Filter.eventually_pure.2 (by simp [hstep1])
    · rw [ae_dirac_eq]
      exact Filter.eventually_pure.2 (by simp [hstep])
  have hmem : MemLp step 2 Ber((1 : ℝ), 0, p) :=
    MemLp.of_bound contDiff_step.continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x ↦ by
        unfold step
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _)
  have hdmem : MemLp (fun x ↦ ‖fderiv ℝ step x‖) 2 Ber((1 : ℝ), 0, p) :=
    (MemLp.zero.ae_eq (hae.mono fun x hx ↦ hx.symm) : _)
  have h0 := h step contDiff_step hmem hdmem
  rw [integral_eq_zero_of_ae (hae.mono fun x hx ↦ by simp [hx]), mul_zero] at h0
  rw [variance_congr hstep_ae, variance_id_bernoulliMeasure] at h0
  nlinarith [mul_pos hp₀ (sub_pos.2 hp₁)]

end Bernoulli

end TauCeti.Probability
