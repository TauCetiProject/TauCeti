/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Integrating representatives of real L² curves

On a finite sample measure, an integrable curve in real `L²` can be integrated
samplewise whenever its representatives are jointly almost everywhere strongly measurable.
The resulting ordinary integral represents the Bochner integral in `L²`. This connects
mean-square process integrals to ordinary time integrals, without treating point evaluation
as a continuous functional on `L²`.
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace MeasureTheory

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {μ : Measure α} {P : Measure Ω} [IsFiniteMeasure P]
  {F : α → Lp ℝ 2 P} {X : α → Ω → ℝ}

/-- Jointly measurable representatives of an integrable real L² curve are integrable
on the product of the parameter measure and a finite sample measure. -/
theorem Integrable.integrable_uncurry_of_ae_eq_L2 (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    Integrable (Function.uncurry X) (μ.prod P) := by
  refine (integrable_prod_iff hX).2 ⟨?_, ?_⟩
  · filter_upwards [heq] with t ht
    exact ((Lp.memLp (F t)).integrable (by norm_num)).congr ht
  · refine (hF.norm.const_mul
      ((P Set.univ ^ (1 - 1 / (2 : ℝ≥0∞).toReal)).toReal)).mono'
      hX.norm.integral_prod_right' ?_
    filter_upwards [heq] with t ht
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      ← integral_congr_ae (ht.mono fun ω hω ↦ congrArg (‖·‖) hω)]
    exact Lp.integral_norm_le_mul_norm (F t)

variable [SFinite μ]

/-- The ordinary samplewise integral of jointly measurable representatives of an
integrable real L² curve represents its L²-valued Bochner integral. -/
theorem Integrable.coeFn_integral_L2 (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    ⇑(∫ t, F t ∂μ) =ᵐ[P] fun ω ↦ ∫ t, X t ω ∂μ := by
  have hi := hF.integrable_uncurry_of_ae_eq_L2 hX heq
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right fun s hs _ ↦ ?_
  have hPs : P s ≠ ∞ := measure_ne_top _ _
  rw [← L2.inner_indicatorConstLp_one hs hPs]
  have hcomm := (innerSL ℝ (indicatorConstLp 2 hs hPs (1 : ℝ))).integral_comp_comm hF
  simp only [innerSL_apply_apply] at hcomm
  rw [← hcomm]
  have hi' : Integrable (Function.uncurry X) (μ.prod (P.restrict s)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← integral_integral_swap hi']
  refine integral_congr_ae ?_
  filter_upwards [heq] with t ht
  rw [L2.inner_indicatorConstLp_one hs hPs]
  exact integral_congr_ae (ae_restrict_of_ae ht)

end MeasureTheory
