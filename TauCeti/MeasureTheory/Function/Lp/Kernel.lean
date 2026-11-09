/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# `Lᵖ` seminorms and Markov kernels

The pointwise `Lᵖ` seminorm of a strongly measurable function against a kernel is measurable.
Taking its `Lᵖ` seminorm against a measure gives the seminorm against the mixture measure. Both
statements hold for every exponent `p`, including `0` and `∞`.

## Main statements

* `TauCeti.measurable_eLpNorm_kernel`: measurability of the pointwise seminorm;
* `TauCeti.eLpNorm_eLpNorm_kernel`: the seminorm of pointwise seminorms equals the seminorm
  against the mixture.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

universe u v w

variable {X : Type u} {Y : Type v} {ε : Type w} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace ε] [ContinuousENorm ε] {p : ℝ≥0∞}

/-- The pointwise `L^p` seminorm `x ↦ ‖f‖_{L^p (κ x)}` of a strongly measurable function against
a kernel is measurable, for every exponent `p`. -/
theorem measurable_eLpNorm_kernel (κ : Kernel X Y) {f : Y → ε} (hf : StronglyMeasurable f) :
    Measurable fun x ↦ eLpNorm f p (κ x) := by
  simp only [← eLpNorm_enorm f hf.aestronglyMeasurable]
  have hg : Measurable fun y ↦ ‖f y‖ₑ := hf.enorm
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [eLpNorm_exponent_zero hg.aestronglyMeasurable, measurable_const]
  rcases eq_or_ne p ∞ with rfl | hp
  · simp only [eLpNorm_exponent_top hg.aestronglyMeasurable, eLpNormEssSup, enorm_eq_self]
    -- `essSup ‖f‖ₑ (κ x) ≤ c` exactly when `κ x` gives no mass to `{y | c < ‖f y‖ₑ}`
    refine measurable_of_Iic fun c ↦ ?_
    have hs : MeasurableSet {y | c < ‖f y‖ₑ} := measurableSet_lt measurable_const hg
    convert (κ.measurable_coe hs) (measurableSet_singleton 0) using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_singleton_iff, ← not_le, ← ae_iff]
    exact ⟨fun h ↦ (ENNReal.ae_le_essSup _).mono fun y hy ↦ hy.trans h,
      essSup_le_of_ae_le (μ := κ x) c⟩
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable]
  exact ((hg.enorm.pow_const _).lintegral_kernel).pow_const _

/-- Averaging the pointwise `L^p` seminorms `x ↦ ‖f‖_{L^p (κ x)}` over `μ` in `L^p` gives the
`L^p` seminorm of `f` against the mixture `κ ∘ₘ μ`, for every exponent `p`. -/
@[simp] theorem eLpNorm_eLpNorm_kernel (κ : Kernel X Y) (μ : Measure X) {f : Y → ε}
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    eLpNorm (fun x ↦ eLpNorm f p (κ x)) p μ = eLpNorm f p (κ ∘ₘ μ) := by
  -- replace `f` by the norm `g` of a strongly measurable version of it, on both sides
  set g : Y → ℝ≥0∞ := fun y ↦ ‖hf.mk f y‖ₑ
  have hg : Measurable g := hf.stronglyMeasurable_mk.enorm
  have hfg {ν : Measure Y} (h : f =ᵐ[ν] hf.mk f) : eLpNorm f p ν = eLpNorm g p ν :=
    (eLpNorm_congr_ae h).trans
      (eLpNorm_enorm _ hf.stronglyMeasurable_mk.aestronglyMeasurable).symm
  rw [hfg hf.ae_eq_mk, eLpNorm_congr_ae ((Measure.ae_ae_of_ae_comp hf.ae_eq_mk).mono
    fun x hx ↦ hfg hx)]
  clear_value g
  have hgk : Measurable fun x ↦ eLpNorm g p (κ x) :=
    measurable_eLpNorm_kernel κ hg.stronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hgk.aestronglyMeasurable,
      eLpNorm_exponent_zero hg.aestronglyMeasurable]
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hgk.aestronglyMeasurable]
    simp only [eLpNorm_exponent_top hg.aestronglyMeasurable, eLpNormEssSup, enorm_eq_self]
    refine le_antisymm (essSup_le_of_ae_le _ ?_) (essSup_le_of_ae_le _ ?_)
    · filter_upwards [Measure.ae_ae_of_ae_comp (ENNReal.ae_le_essSup g)] with x hx
      exact essSup_le_of_ae_le _ hx
    · refine Measure.ae_comp_of_ae_ae (measurableSet_le hg measurable_const) ?_
      filter_upwards [ENNReal.ae_le_essSup fun x ↦ essSup g (κ x)] with x hx
      filter_upwards [ENNReal.ae_le_essSup g] with y hy using hy.trans hx
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hgk.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable,
    Measure.lintegral_bind κ.aemeasurable (hg.enorm.pow_const _).aemeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable,
    enorm_eq_self, one_div, ENNReal.rpow_inv_rpow hr.ne']

end TauCeti
