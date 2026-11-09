/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Basic facts about moment-generating functions

This file supplements Mathlib's basic moment-generating-function API.

## Main results

* `TauCeti.isProbabilityMeasure_of_mgf_zero_eq_one`: a measure is a probability measure if the
  moment-generating function of any real-valued statistic equals `1` at zero.
* `TauCeti.isFiniteMeasure_of_zero_mem_integrableExpSet`: a measure with an exponential moment at
  `0` is finite.
* `TauCeti.mgf_lt_one_of_nonneg_of_neg`: under a probability measure, the moment-generating
  function of a nonnegative random variable that is not almost surely zero is strictly less than
  `1` at every negative argument.
* `TauCeti.mgf_id_conv`: the moment-generating function of a convolution of two s-finite measures
  on `ℝ` is the product of their moment-generating functions.  This is the transform side of
  `MeasureTheory.Measure.conv`, the companion of `MeasureTheory.charFun_conv`.
* `TauCeti.ae_sum_eq_zero_of_sum_integral_sq_eq_zero`: a finite sum of square-integrable random
  variables whose second moments sum to zero vanishes almost surely.
* `ProbabilityTheory.iIndepFun.mgf_sum_of_aemeasurable`: the moment-generating function of a finite
  sum of independent variables is the product of the factors, needing a.e. measurability only on
  the summation set.
* `ProbabilityTheory.iIndepFun.integrable_exp_mul_sum_of_aemeasurable`: the exponential of a finite
  sum of independent a.e. measurable variables is integrable when each factor is.

* `TauCeti.ofReal_mgf_sub_integral_le_lintegral`: symmetrization by Jensen's inequality, the
  moment-generating function of `f - 𝔼 f` is at most `∫∫ exp (t (f x - f y)) dμ(x) dμ(y)`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-- A measure is a probability measure if the moment-generating function of any real-valued
statistic equals `1` at zero. -/
theorem isProbabilityMeasure_of_mgf_zero_eq_one (hmgf : mgf X μ 0 = 1) :
    IsProbabilityMeasure μ := by
  rw [mgf_zero'] at hmgf
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 hmgf⟩

/-- A measure admitting an exponential moment at rate `0` is finite: at rate `0` the integrand is
the constant `1`, whose integrability is finiteness of the measure. -/
theorem isFiniteMeasure_of_zero_mem_integrableExpSet (h : (0 : ℝ) ∈ integrableExpSet X μ) :
    IsFiniteMeasure μ :=
  (integrable_const_iff_isFiniteMeasure one_ne_zero).mp <| by
    simpa using integrable_of_mem_integrableExpSet h

/-- Under a probability measure, the moment-generating function of an almost surely nonnegative
random variable that is positive with positive probability is strictly less than `1` at every
negative argument. -/
theorem mgf_lt_one_of_nonneg_of_neg [IsProbabilityMeasure μ] (hX : AEMeasurable X μ)
    (hX0 : 0 ≤ᵐ[μ] X) (hpos : μ {ω | 0 < X ω} ≠ 0) {t : ℝ} (ht : t < 0) : mgf X μ t < 1 := by
  have hle : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 := by
    filter_upwards [hX0] with ω hω
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ht.le hω)
  have hint : Integrable (fun ω ↦ Real.exp (t * X ω)) μ :=
    Integrable.of_bound (by fun_prop) 1 <| hle.mono fun ω hω ↦ by
      rwa [Real.norm_of_nonneg (Real.exp_pos _).le]
  -- `1 - exp (t * X)` is nonnegative and vanishes exactly where `X` does.
  have hdiff : 0 < ∫ ω, (1 - Real.exp (t * X ω)) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (hle.mono fun ω hω ↦ sub_nonneg.2 hω)
      ((integrable_const 1).sub hint)]
    refine pos_iff_ne_zero.2 fun h0 ↦ hpos <| measure_mono_null (fun ω hω ↦ ?_) h0
    have : t * X ω < 0 := mul_neg_of_neg_of_pos ht hω
    simp [Function.mem_support, sub_eq_zero, (Real.exp_lt_one_iff.2 this).ne']
  rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ, one_smul] at hdiff
  rw [mgf]
  linarith

/-- **The moment-generating function of a convolution is the product of the two
moment-generating functions.** This is the transform companion of `MeasureTheory.charFun_conv`.
No integrability hypothesis is needed, even though Mathlib totalizes a divergent `mgf` to `0`. -/
@[simp]
theorem mgf_id_conv {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] :
    mgf id (μ ∗ ν) = mgf id μ * mgf id ν := by
  ext t
  rw [Measure.conv, mgf_id_map (by fun_prop), mgf]
  simp only [mul_add, Real.exp_add]
  exact integral_prod_mul (L := ℝ) (fun x ↦ Real.exp (t * x)) fun y ↦ Real.exp (t * y)

/-- If square-integrable random variables have vanishing total second moment, their sum vanishes
almost surely. -/
theorem ae_sum_eq_zero_of_sum_integral_sq_eq_zero {ι : Type*} {X : ι → Ω → ℝ}
    {s : Finset ι} (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∑ i ∈ s, X i ω = 0 := by
  have hsq : ∀ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _).1 hv
  have hae : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω = 0 := fun i hi ↦ by
    have h := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω ↦ sq_nonneg (X i ω))
      (hX i hi).integrable_sq).1 (hsq i hi)
    filter_upwards [h] with ω hω
    simpa using hω
  filter_upwards [(Filter.eventually_all_finset s).2 hae] with ω hω
  exact Finset.sum_eq_zero hω

section Symmetrization

open Real

variable {f : Ω → ℝ}

/-- **Symmetrization by Jensen's inequality.** For a probability measure `μ`, the moment
generating function of `f - 𝔼 f` at `t` is at most `∫∫ exp (t (f x - f y)) dμ(x) dμ(y)`. -/
theorem ofReal_mgf_sub_integral_le_lintegral [IsProbabilityMeasure μ]
    (hfi : Integrable f μ) {t : ℝ} (hint : Integrable (fun x ↦ exp (t * (f x - ∫ y, f y ∂μ))) μ)
    (hneg : Integrable (fun x ↦ exp (-t * f x)) μ) :
    ENNReal.ofReal (mgf (fun x ↦ f x - ∫ y, f y ∂μ) μ t) ≤
      ∫⁻ p, .ofReal (exp (t * (f p.1 - f p.2))) ∂μ.prod μ := by
  set m := ∫ y, f y ∂μ
  have hexp (x y : Ω) : exp (t * (f x - f y)) = exp (t * f x) * exp (-t * f y) := by
    rw [← exp_add]
    congr 1
    ring
  have hexpi (x : Ω) : Integrable (fun y ↦ exp (t * (f x - f y))) μ := by
    simp_rw [hexp]
    exact hneg.const_mul _
  -- Jensen's inequality in `y`, for each fixed `x`.
  have hjensen (x : Ω) : exp (t * (f x - m)) ≤ ∫ y, exp (t * (f x - f y)) ∂μ := by
    have hmean : ∫ y, t * (f x - f y) ∂μ = t * (f x - m) := by
      rw [integral_const_mul, integral_sub (integrable_const _) hfi]
      simp [m]
    rw [← hmean]
    exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (by simp)
      (((integrable_const _).sub hfi).const_mul t) (hexpi x)
  have hf1 : AEMeasurable (fun p : Ω × Ω ↦ f p.1) (μ.prod μ) :=
    hfi.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hf2 : AEMeasurable (fun p : Ω × Ω ↦ f p.2) (μ.prod μ) :=
    hfi.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hF : AEMeasurable (fun p : Ω × Ω ↦ ENNReal.ofReal (exp (t * (f p.1 - f p.2)))) (μ.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (by fun_prop)
  rw [mgf]
  calc ENNReal.ofReal (∫ x, exp (t * (f x - m)) ∂μ)
      = ∫⁻ x, .ofReal (exp (t * (f x - m))) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (exp_pos _).le)
    _ ≤ ∫⁻ x, .ofReal (∫ y, exp (t * (f x - f y)) ∂μ) ∂μ :=
        lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hjensen x)
    _ = ∫⁻ p, .ofReal (exp (t * (f p.1 - f p.2))) ∂μ.prod μ := by
        rw [lintegral_prod _ hF]
        refine lintegral_congr fun x ↦ ?_
        rw [ofReal_integral_eq_lintegral_ofReal (hexpi x) (.of_forall fun _ ↦ (exp_pos _).le)]

end Symmetrization

end TauCeti

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*} {X : ι → Ω → ℝ} {t : ℝ}

omit [IsProbabilityMeasure μ] in
/-- The moment-generating function of a finite sum of independent variables is the product of
their moment-generating functions, where only the members indexed by the sum need be a.e.
measurable. This weakens the measurability hypothesis of `ProbabilityTheory.iIndepFun.mgf_sum₀`. -/
theorem mgf_sum_of_aemeasurable (h_indep : iIndepFun X μ) {s : Finset ι}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  have h := (h_indep.precomp Subtype.val_injective).mgf_sum₀ (t := t)
    (fun i : s => h_meas i i.2) Finset.univ
  rw [Finset.prod_coe_sort s (fun i => mgf (X i) μ t)] at h
  rw [← h]
  congr 1
  ext ω
  simp only [Finset.sum_apply]
  exact (Finset.sum_coe_sort s (fun i => X i ω)).symm

/-- A finite sum of independent, almost-everywhere measurable variables with integrable
exponentials has an integrable exponential. This weakens the measurability hypothesis of
`ProbabilityTheory.iIndepFun.integrable_exp_mul_sum`. -/
theorem integrable_exp_mul_sum_of_aemeasurable (h_indep : iIndepFun X μ)
    {s : Finset ι} (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_int : ∀ i ∈ s, Integrable (fun ω => Real.exp (t * X i ω)) μ) :
    Integrable (fun ω => Real.exp (t * (∑ i ∈ s, X i ω))) μ := by
  rw [← mgf_pos_iff]
  rw [h_indep.mgf_sum_of_aemeasurable h_meas (t := t)]
  exact Finset.prod_pos fun i hi => mgf_pos (h_int i hi)

end ProbabilityTheory.iIndepFun
