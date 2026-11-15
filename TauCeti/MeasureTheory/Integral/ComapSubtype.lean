/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration and `Lᵖ` norms for subtype pullback measures

For a measurable set `s : Set α` and a measure `μ : Measure α`, the subtype pullback measure
`μ.comap ((↑) : s → α)` pushes forward along `(↑) : s → α` to `μ.restrict s`
(`map_comap_subtype_coe`). Mathlib provides the lower Lebesgue integral, `IntegrableOn`, and
Bochner integral bridges `lintegral_subtype_comap`, `integrableOn_iff_comap_subtypeVal`, and
`integral_subtype_comap`.

This file completes that bridge in three directions:

1. **`AEStronglyMeasurable`, `eLpNorm` and `MemLp` on `μ.comap (↑)`**: exact subtype counterparts
   of `μ.restrict s`.
2. **Agreement with ambient integrals and norms**: when `f =ᵐ[μ.restrict sᶜ] 0`, strong
   measurability, `lintegral`, `eLpNorm`, `MemLp`, `Integrable`, and the Bochner integral against
   `μ` on `α` agree with those of `x : s ↦ f x` against `μ.comap (↑)` on `s`.
3. **Independence of the ambient carrier**: if `f` vanishes almost everywhere outside two
   measurable sets `s₁` and `s₂`, all six quantities agree between `(s₁, μ.comap (↑))` and
   `(s₂, μ.comap (↑))`.

## Main results

* `MeasureTheory.aestronglyMeasurable_restrict_iff_comap_subtypeVal`,
  `MeasureTheory.eLpNorm_comp_subtypeVal`, `MeasureTheory.memLp_restrict_iff_comap_subtypeVal`:
  restriction-to-subtype equivalences.
* `MeasureTheory.aestronglyMeasurable_iff_comap_subtypeVal_of_ae_eq_zero`,
  `MeasureTheory.lintegral_eq_subtype_comap_of_ae_eq_zero`,
  `MeasureTheory.eLpNorm_eq_comap_subtypeVal_of_ae_eq_zero`,
  `MeasureTheory.memLp_iff_comap_subtypeVal_of_ae_eq_zero`,
  `MeasureTheory.integrable_iff_comap_subtypeVal_of_ae_eq_zero`,
  `MeasureTheory.integral_eq_subtype_comap_of_ae_eq_zero`: agreement with ambient quantities when
  `f =ᵐ[μ.restrict sᶜ] 0`, together with the two-carrier congruence corollaries `*_congr`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s s₁ s₂ : Set α} {p : ℝ≥0∞}

section RestrictBridge

/-- Almost-everywhere strong measurability on `μ.restrict s` is equivalent to almost-everywhere
strong measurability on `(s, μ.comap (↑))`. -/
theorem aestronglyMeasurable_restrict_iff_comap_subtypeVal {β : Type*} [TopologicalSpace β]
    (hs : MeasurableSet s) {f : α → β} :
    AEStronglyMeasurable f (μ.restrict s) ↔
      AEStronglyMeasurable (fun x : s ↦ f x) (μ.comap ((↑) : s → α)) := by
  rw [← map_comap_subtype_coe hs,
    (MeasurableEmbedding.subtype_coe hs).aestronglyMeasurable_map_iff]
  rfl

/-- The essential supremum seminorm on `(s, μ.comap (↑))` agrees with that on `μ.restrict s`. -/
theorem eLpNormEssSup_comp_subtypeVal {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (hs : MeasurableSet s) (f : α → ε) :
    eLpNormEssSup (fun x : s ↦ f x) (μ.comap ((↑) : s → α)) = eLpNormEssSup f (μ.restrict s) := by
  rw [← map_comap_subtype_coe hs,
    (MeasurableEmbedding.subtype_coe hs).eLpNormEssSup_map_measure]
  rfl

/-- The `Lᵖ` seminorm on `(s, μ.comap (↑))` agrees with that on `μ.restrict s`. -/
theorem eLpNorm_comp_subtypeVal {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (hs : MeasurableSet s) (f : α → ε) (p : ℝ≥0∞) :
    eLpNorm (fun x : s ↦ f x) p (μ.comap ((↑) : s → α)) = eLpNorm f p (μ.restrict s) := by
  rw [← map_comap_subtype_coe hs,
    (MeasurableEmbedding.subtype_coe hs).eLpNorm_map_measure]
  rfl

/-- Membership in `Lᵖ` on `μ.restrict s` is equivalent to membership in `Lᵖ` on
`(s, μ.comap (↑))`. -/
theorem memLp_restrict_iff_comap_subtypeVal {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (hs : MeasurableSet s) {f : α → ε} :
    MemLp f p (μ.restrict s) ↔ MemLp (fun x : s ↦ f x) p (μ.comap ((↑) : s → α)) := by
  rw [← map_comap_subtype_coe hs,
    (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff]
  rfl

end RestrictBridge

section AmbientAgreement

/-- A function vanishing `μ`-almost everywhere outside a measurable set `s` is almost everywhere
strongly measurable on `α` if and only if its restriction to `s` is almost everywhere strongly
measurable for `μ.comap (↑)`. -/
theorem aestronglyMeasurable_iff_comap_subtypeVal_of_ae_eq_zero {β : Type*} [TopologicalSpace β]
    [Zero β] (hs : MeasurableSet s) {f : α → β} (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    AEStronglyMeasurable f μ ↔
      AEStronglyMeasurable (fun x : s ↦ f x) (μ.comap ((↑) : s → α)) := by
  rw [← aestronglyMeasurable_congr (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hf),
    aestronglyMeasurable_indicator_iff hs, aestronglyMeasurable_restrict_iff_comap_subtypeVal hs]

/-- If `f` vanishes `μ`-almost everywhere outside measurable sets `s₁` and `s₂`, almost-everywhere
strong measurability of its restrictions to `(s₁, μ.comap (↑))` and `(s₂, μ.comap (↑))` are
equivalent. -/
theorem aestronglyMeasurable_comap_subtypeVal_congr {β : Type*} [TopologicalSpace β] [Zero β]
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) {f : α → β}
    (hf₁ : f =ᵐ[μ.restrict s₁ᶜ] 0) (hf₂ : f =ᵐ[μ.restrict s₂ᶜ] 0) :
    AEStronglyMeasurable (fun x : s₁ ↦ f x) (μ.comap ((↑) : s₁ → α)) ↔
      AEStronglyMeasurable (fun x : s₂ ↦ f x) (μ.comap ((↑) : s₂ → α)) :=
  (aestronglyMeasurable_iff_comap_subtypeVal_of_ae_eq_zero hs₁ hf₁).symm.trans
    (aestronglyMeasurable_iff_comap_subtypeVal_of_ae_eq_zero hs₂ hf₂)

/-- If `f : α → ℝ≥0∞` vanishes `μ`-almost everywhere outside a measurable set `s`, its ambient
lower Lebesgue integral equals its integral on `(s, μ.comap (↑))`. -/
theorem lintegral_eq_subtype_comap_of_ae_eq_zero (hs : MeasurableSet s) {f : α → ℝ≥0∞}
    (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    ∫⁻ x, f x ∂μ = ∫⁻ x : s, f x ∂(μ.comap ((↑) : s → α)) := by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hf),
    lintegral_indicator hs, lintegral_subtype_comap hs]

/-- Independence of the carrier for the lower Lebesgue integral of `f : α → ℝ≥0∞` vanishing almost
everywhere outside `s₁` and `s₂`. -/
theorem lintegral_subtype_comap_congr (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂)
    {f : α → ℝ≥0∞} (hf₁ : f =ᵐ[μ.restrict s₁ᶜ] 0) (hf₂ : f =ᵐ[μ.restrict s₂ᶜ] 0) :
    ∫⁻ x : s₁, f x ∂(μ.comap ((↑) : s₁ → α)) = ∫⁻ x : s₂, f x ∂(μ.comap ((↑) : s₂ → α)) :=
  (lintegral_eq_subtype_comap_of_ae_eq_zero hs₁ hf₁).symm.trans
    (lintegral_eq_subtype_comap_of_ae_eq_zero hs₂ hf₂)

/-- If `f` vanishes `μ`-almost everywhere outside a measurable set `s`, its ambient `Lᵖ` seminorm
equals the `Lᵖ` seminorm of its restriction to `(s, μ.comap (↑))`. -/
theorem eLpNorm_eq_comap_subtypeVal_of_ae_eq_zero {ε : Type*} [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] (hs : MeasurableSet s) {f : α → ε} (hf : f =ᵐ[μ.restrict sᶜ] 0)
    (p : ℝ≥0∞) :
    eLpNorm f p μ = eLpNorm (fun x : s ↦ f x) p (μ.comap ((↑) : s → α)) := by
  rw [← eLpNorm_congr_ae (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hf),
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet, eLpNorm_comp_subtypeVal hs]

/-- Independence of the carrier for the `Lᵖ` seminorm of a function vanishing almost everywhere
outside `s₁` and `s₂`. -/
theorem eLpNorm_comap_subtypeVal_congr {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) {f : α → ε}
    (hf₁ : f =ᵐ[μ.restrict s₁ᶜ] 0) (hf₂ : f =ᵐ[μ.restrict s₂ᶜ] 0) (p : ℝ≥0∞) :
    eLpNorm (fun x : s₁ ↦ f x) p (μ.comap ((↑) : s₁ → α)) =
      eLpNorm (fun x : s₂ ↦ f x) p (μ.comap ((↑) : s₂ → α)) :=
  (eLpNorm_eq_comap_subtypeVal_of_ae_eq_zero hs₁ hf₁ p).symm.trans
    (eLpNorm_eq_comap_subtypeVal_of_ae_eq_zero hs₂ hf₂ p)

/-- If `f` vanishes `μ`-almost everywhere outside a measurable set `s`, membership in ambient `Lᵖ`
is equivalent to membership in `Lᵖ` on `(s, μ.comap (↑))`. -/
theorem memLp_iff_comap_subtypeVal_of_ae_eq_zero {ε : Type*} [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] (hs : MeasurableSet s) {f : α → ε} (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    MemLp f p μ ↔ MemLp (fun x : s ↦ f x) p (μ.comap ((↑) : s → α)) := by
  rw [← memLp_congr_ae (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hf),
    memLp_indicator_iff_restrict hs.nullMeasurableSet, memLp_restrict_iff_comap_subtypeVal hs]

/-- Independence of the carrier for `Lᵖ` membership of a function vanishing almost everywhere
outside `s₁` and `s₂`. -/
theorem memLp_comap_subtypeVal_congr {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) {f : α → ε}
    (hf₁ : f =ᵐ[μ.restrict s₁ᶜ] 0) (hf₂ : f =ᵐ[μ.restrict s₂ᶜ] 0) :
    MemLp (fun x : s₁ ↦ f x) p (μ.comap ((↑) : s₁ → α)) ↔
      MemLp (fun x : s₂ ↦ f x) p (μ.comap ((↑) : s₂ → α)) :=
  (memLp_iff_comap_subtypeVal_of_ae_eq_zero hs₁ hf₁).symm.trans
    (memLp_iff_comap_subtypeVal_of_ae_eq_zero hs₂ hf₂)

/-- If `f` vanishes `μ`-almost everywhere outside a measurable set `s`, ambient integrability is
equivalent to integrability on `(s, μ.comap (↑))`. -/
theorem integrable_iff_comap_subtypeVal_of_ae_eq_zero {ε : Type*} [TopologicalSpace ε]
    [ENormedAddMonoid ε] (hs : MeasurableSet s) {f : α → ε} (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    Integrable f μ ↔ Integrable (fun x : s ↦ f x) (μ.comap ((↑) : s → α)) := by
  rw [← integrable_congr (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hf),
    integrable_indicator_iff hs, integrableOn_iff_comap_subtypeVal hs]
  rfl

/-- Independence of the carrier for integrability of a function vanishing almost everywhere outside
`s₁` and `s₂`. -/
theorem integrable_comap_subtypeVal_congr {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) {f : α → ε}
    (hf₁ : f =ᵐ[μ.restrict s₁ᶜ] 0) (hf₂ : f =ᵐ[μ.restrict s₂ᶜ] 0) :
    Integrable (fun x : s₁ ↦ f x) (μ.comap ((↑) : s₁ → α)) ↔
      Integrable (fun x : s₂ ↦ f x) (μ.comap ((↑) : s₂ → α)) :=
  (integrable_iff_comap_subtypeVal_of_ae_eq_zero hs₁ hf₁).symm.trans
    (integrable_iff_comap_subtypeVal_of_ae_eq_zero hs₂ hf₂)

/-- If `f` vanishes `μ`-almost everywhere outside a measurable set `s`, its ambient Bochner
integral equals its Bochner integral on `(s, μ.comap (↑))`. No integrability or completeness
assumption is required. -/
theorem integral_eq_subtype_comap_of_ae_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hs : MeasurableSet s) {f : α → E} (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    ∫ x, f x ∂μ = ∫ x : s, f x ∂(μ.comap ((↑) : s → α)) := by
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero ((ae_restrict_iff' hs.compl).1 hf),
    integral_subtype_comap hs]

/-- Independence of the carrier for the Bochner integral of a function vanishing almost everywhere
outside `s₁` and `s₂`. -/
theorem integral_subtype_comap_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) {f : α → E}
    (hf₁ : f =ᵐ[μ.restrict s₁ᶜ] 0) (hf₂ : f =ᵐ[μ.restrict s₂ᶜ] 0) :
    ∫ x : s₁, f x ∂(μ.comap ((↑) : s₁ → α)) = ∫ x : s₂, f x ∂(μ.comap ((↑) : s₂ → α)) :=
  (integral_eq_subtype_comap_of_ae_eq_zero hs₁ hf₁).symm.trans
    (integral_eq_subtype_comap_of_ae_eq_zero hs₂ hf₂)

end AmbientAgreement

end MeasureTheory
