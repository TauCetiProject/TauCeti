/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Ambient agreement and subset independence for subtype integrals

When a function `f` vanishes almost everywhere outside a measurable set `s` — in the restricted
form `f =ᵐ[μ.restrict sᶜ] 0` produced by inner-regular localization theorems such as
`MeasureTheory.exists_isSigmaCompact` and
`MeasureTheory.exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero` — integrating `f` on the
subtype `s` against the pullback measure `μ.comap ((↑) : s → α)` agrees with integrating `f` over
the ambient space `α` against `μ`, and `f` is integrable on `α` if and only if `f ∘ (↑)` is
integrable on `s`.

Consequently, if `f` vanishes almost everywhere outside each of two measurable sets `s` and `t`
(for example two σ-compact open subgroups containing the support of `f`), then its Lebesgue
integral, its Bochner integral, and its integrability on `s` agree with those on `t`: restricted
integration is independent of the ambient carrier chosen.

## Main statements

* `MeasureTheory.setLIntegral_eq_lintegral_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.lintegral_subtype_comap_of_ae_restrict_compl_eq_zero`: lower Lebesgue integral
  agreement when `f =ᵐ[μ.restrict sᶜ] 0`.
* `MeasureTheory.integral_subtype_comap_of_ae_restrict_compl_eq_zero`: Bochner integral agreement
  when `f =ᵐ[μ.restrict sᶜ] 0`.
* `MeasureTheory.integrable_iff_integrableOn_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.integrable_iff_comap_subtypeVal_of_ae_restrict_compl_eq_zero`: integrability
  equivalence with the subtype pullback when `f =ᵐ[μ.restrict sᶜ] 0`.
* `MeasureTheory.lintegral_subtype_comap_eq_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.integral_subtype_comap_eq_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.integrable_comap_subtypeVal_iff_of_ae_restrict_compl_eq_zero`: independence of the
  measurable subset chosen.
-/

public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}

/-- Null-measurable version of `MeasureTheory.indicator_ae_eq_of_restrict_compl_ae_eq_zero`: if `f`
vanishes `μ.restrict sᶜ`-almost everywhere for a null-measurable set `s`, then `s.indicator f`
agrees `μ`-almost everywhere with `f`. -/
theorem indicator_ae_eq_of_restrict_compl_ae_eq_zero₀ {β : Type*} [Zero β] {f : α → β}
    (hs : NullMeasurableSet s μ) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    s.indicator f =ᵐ[μ] f :=
  ae_of_ae_restrict_of_ae_restrict_compl s (indicator_ae_eq_restrict hs)
    ((indicator_ae_eq_restrict_compl hs).trans hf.symm)

section LIntegral

/-- If `f` vanishes `μ.restrict sᶜ`-almost everywhere on the complement of a null-measurable set
`s`, its set lower Lebesgue integral on `s` equals its ambient lower Lebesgue integral. -/
theorem setLIntegral_eq_lintegral_of_ae_restrict_compl_eq_zero {f : α → ℝ≥0∞}
    (hs : NullMeasurableSet s μ) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_indicator₀ hs,
    lintegral_congr_ae (indicator_ae_eq_of_restrict_compl_ae_eq_zero₀ hs hf)]

/-- If `f` vanishes `μ.restrict sᶜ`-almost everywhere outside a measurable set `s`, integrating `f`
on the subtype `s` against `μ.comap (↑)` gives the ambient lower Lebesgue integral. -/
theorem lintegral_subtype_comap_of_ae_restrict_compl_eq_zero {f : α → ℝ≥0∞}
    (hs : MeasurableSet s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    ∫⁻ x : s, f x ∂(μ.comap ((↑) : s → α)) = ∫⁻ x, f x ∂μ :=
  (lintegral_subtype_comap hs f).trans
    (setLIntegral_eq_lintegral_of_ae_restrict_compl_eq_zero hs.nullMeasurableSet hf)

/-- **Subset independence of subtype lower Lebesgue integrals.** If `f` vanishes almost everywhere
outside each of two measurable sets `s` and `t`, its subtype lower Lebesgue integrals on `s` and on
`t` agree. -/
theorem lintegral_subtype_comap_eq_of_ae_restrict_compl_eq_zero {f : α → ℝ≥0∞}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : f =ᵐ[μ.restrict sᶜ] 0) (hft : f =ᵐ[μ.restrict tᶜ] 0) :
    ∫⁻ x : s, f x ∂(μ.comap ((↑) : s → α)) = ∫⁻ x : t, f x ∂(μ.comap ((↑) : t → α)) :=
  (lintegral_subtype_comap_of_ae_restrict_compl_eq_zero hs hfs).trans
    (lintegral_subtype_comap_of_ae_restrict_compl_eq_zero ht hft).symm

end LIntegral

section Integrable

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/-- If `f` vanishes `μ.restrict sᶜ`-almost everywhere outside a null-measurable set `s`, then `f`
is integrable on `α` if and only if it is integrable on `s`. -/
theorem integrable_iff_integrableOn_of_ae_restrict_compl_eq_zero {f : α → ε}
    (hs : NullMeasurableSet s μ) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    Integrable f μ ↔ IntegrableOn f s μ :=
  (integrable_congr (indicator_ae_eq_of_restrict_compl_ae_eq_zero₀ hs hf)).symm.trans
    (integrable_indicator_iff₀ hs)

/-- If `f` vanishes `μ.restrict sᶜ`-almost everywhere outside a measurable set `s`, then `f` is
integrable against `μ` if and only if `f ∘ (↑)` is integrable against `μ.comap (↑)` on `s`. -/
theorem integrable_iff_comap_subtypeVal_of_ae_restrict_compl_eq_zero {f : α → ε}
    (hs : MeasurableSet s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    Integrable f μ ↔ Integrable (f ∘ ((↑) : s → α)) (μ.comap ((↑) : s → α)) :=
  (integrable_iff_integrableOn_of_ae_restrict_compl_eq_zero hs.nullMeasurableSet hf).trans
    (integrableOn_iff_comap_subtypeVal hs)

/-- **Subset independence of subtype integrability.** If `f` vanishes almost everywhere outside each
of two measurable sets `s` and `t`, then `f ∘ (↑)` is integrable on `s` if and only if it is
integrable on `t`. -/
theorem integrable_comap_subtypeVal_iff_of_ae_restrict_compl_eq_zero {f : α → ε}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : f =ᵐ[μ.restrict sᶜ] 0) (hft : f =ᵐ[μ.restrict tᶜ] 0) :
    Integrable (f ∘ ((↑) : s → α)) (μ.comap ((↑) : s → α)) ↔
      Integrable (f ∘ ((↑) : t → α)) (μ.comap ((↑) : t → α)) :=
  (integrable_iff_comap_subtypeVal_of_ae_restrict_compl_eq_zero hs hfs).symm.trans
    (integrable_iff_comap_subtypeVal_of_ae_restrict_compl_eq_zero ht hft)

end Integrable

section Bochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Ambient agreement of subtype Bochner integrals.** If `f` vanishes `μ.restrict sᶜ`-almost
everywhere outside a measurable set `s`, integrating `f` on the subtype `s` against `μ.comap (↑)`
gives the ambient Bochner integral. -/
theorem integral_subtype_comap_of_ae_restrict_compl_eq_zero {f : α → E}
    (hs : MeasurableSet s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    ∫ x : s, f x ∂(μ.comap ((↑) : s → α)) = ∫ x, f x ∂μ :=
  (integral_subtype_comap hs f).trans
    (setIntegral_eq_integral_of_ae_compl_eq_zero ((ae_restrict_iff' hs.compl).1 hf))

/-- **Subset independence of subtype Bochner integrals.** If `f` vanishes almost everywhere outside
each of two measurable sets `s` and `t`, its subtype Bochner integrals on `s` and on `t` agree. -/
theorem integral_subtype_comap_eq_of_ae_restrict_compl_eq_zero {f : α → E}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : f =ᵐ[μ.restrict sᶜ] 0) (hft : f =ᵐ[μ.restrict tᶜ] 0) :
    ∫ x : s, f x ∂(μ.comap ((↑) : s → α)) = ∫ x : t, f x ∂(μ.comap ((↑) : t → α)) :=
  (integral_subtype_comap_of_ae_restrict_compl_eq_zero hs hfs).trans
    (integral_subtype_comap_of_ae_restrict_compl_eq_zero ht hft).symm

end Bochner

end MeasureTheory
