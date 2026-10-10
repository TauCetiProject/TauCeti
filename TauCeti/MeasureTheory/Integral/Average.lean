/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Norms of averages

The extended norm of the average of a function is at most the average of its extended norm, and
consequently the measure of a set times the norm of the average over it is at most the integral of
the norm over it. These are the estimates used to bound a function that has been replaced by its
averages on the pieces of a partition, as in the Calderón–Zygmund decomposition.

Both hold without any integrability or finiteness assumption: when the average is not defined it
is `0` by convention.

Measuring the mean oscillation of a function about its own average rather than about a constant
`c` costs at most a factor `2`: `⨍_s ‖f - f_s‖ ≤ 2 ⨍_s ‖f - c‖`. So a bound on the oscillation
about any convenient constant gives one about the average, the form used by the John–Nirenberg
inequality.

The average of a function over a set `s` is also controlled by its average over a larger set
`t ⊇ s`, at the cost of the ratio `μ t / μ s` of their measures.

Averages are unchanged by a change of variables that rescales the measure by a constant factor,
such as an affine homothety of a finite-dimensional space with its Haar measure: if a measurable
equivalence `e` pushes `μ` forward to `a • ν` with `0 < a < ∞`, then the average of `f ∘ e` over
`e ⁻¹' s` with respect to `μ` is the average of `f` over `s` with respect to `ν`.

## Main results

* `TauCeti.enorm_setAverage_le_setLAverage`: the extended norm of an average over a set is at most
  the average of the extended norm over the set.
* `TauCeti.measure_mul_enorm_setAverage_le`: the measure of a set times the extended norm of the
  average over it is at most the integral of the extended norm over it.
* `TauCeti.setLAverage_enorm_sub_setAverage_le`: the mean oscillation of `f` about its
  average is at most twice its mean oscillation about any constant.
* `TauCeti.norm_setAverage_sub_le_of_subset`: the average over a subset `s ⊆ t`
  differs from a constant `c` by at most `μ t / μ s` times the average of `‖f - c‖` over `t`.
* `TauCeti.setLIntegral_comp_preimage_of_map_eq_smul`,
  `TauCeti.setIntegral_comp_preimage_of_map_eq_smul`,
  `TauCeti.setLAverage_comp_preimage_of_map_eq_smul`,
  `TauCeti.setAverage_comp_preimage_of_map_eq_smul`: integrals and averages under a measurable
  equivalence that rescales the measure by a constant.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

section ENorm

variable {α E : Type*} {_ : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The extended norm of an average is at most the average of the extended norm. -/
theorem enorm_average_le_laverage (μ : Measure α) (f : α → E) :
    ‖⨍ x, f x ∂μ‖ₑ ≤ ⨍⁻ x, ‖f x‖ₑ ∂μ := by
  rw [average_eq', laverage_eq']
  exact enorm_integral_le_lintegral_enorm _

/-- The extended norm of an average over a set is at most the average of the extended norm over
the set. -/
theorem enorm_setAverage_le_setLAverage (μ : Measure α) (f : α → E) (s : Set α) :
    ‖⨍ x in s, f x ∂μ‖ₑ ≤ ⨍⁻ x in s, ‖f x‖ₑ ∂μ :=
  enorm_average_le_laverage _ _

/-- The measure of a set times the extended norm of the average over it is at most the integral of
the extended norm over it. -/
theorem measure_mul_enorm_setAverage_le (μ : Measure α) (f : α → E) (s : Set α) :
    μ s * ‖⨍ x in s, f x ∂μ‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ := by
  by_cases hs : μ s = ∞
  · simp [setAverage_eq, measureReal_def, hs]
  · rw [← measure_mul_setLAverage _ hs]
    gcongr
    exact enorm_setAverage_le_setLAverage μ f s

end ENorm

section Oscillation

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {s : Set X}

/-- The mean oscillation of `f` on `s` about its own average is at most twice its mean oscillation
about any constant `c`: `⨍_s ‖f - f_s‖ ≤ 2 ⨍_s ‖f - c‖`. -/
theorem setLAverage_enorm_sub_setAverage_le (hf : IntegrableOn f s μ) (c : F) :
    ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ ≤ 2 * ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := by
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ s) ∞ with htop | htop
  · simp [setLAverage_eq, htop]
  have heq : (⨍ y in s, f y ∂μ) - c = ⨍ y in s, (f y - c) ∂μ := by
    rw [setAverage_fun_sub hf (integrableOn_const htop), setAverage_const h0 htop]
  calc ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ
      ≤ ⨍⁻ x in s, (‖f x - c‖ₑ + ⨍⁻ y in s, ‖f y - c‖ₑ ∂μ) ∂μ := by
        refine setLAverage_mono_ae s (.of_forall fun x => ?_)
        calc ‖f x - ⨍ y in s, f y ∂μ‖ₑ = ‖(f x - c) - ((⨍ y in s, f y ∂μ) - c)‖ₑ := by
              congr 1; abel
          _ ≤ ‖f x - c‖ₑ + ‖(⨍ y in s, f y ∂μ) - c‖ₑ := enorm_sub_le
          _ ≤ ‖f x - c‖ₑ + ⨍⁻ y in s, ‖f y - c‖ₑ ∂μ := by
            rw [heq]
            gcongr
            exact enorm_setAverage_le_setLAverage μ _ s
    _ = 2 * ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := by
        rw [setLAverage_eq μ (fun x => ‖f x - c‖ₑ + ⨍⁻ y in s, ‖f y - c‖ₑ ∂μ) s,
          lintegral_add_right _ measurable_const, setLIntegral_const,
          ENNReal.add_div, ENNReal.mul_div_cancel_right h0 htop, ← setLAverage_eq, two_mul]

end Oscillation

section Subset

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {s t : Set X}

/-- The average of `f` over a subset `s` of `t` differs from a constant `c` by at most
`μ t / μ s` times the average of `‖f - c‖` over `t`. -/
theorem norm_setAverage_sub_le_of_subset (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ⊤)
    (hf : IntegrableOn f t μ) (c : F) :
    ‖(⨍ x in s, f x ∂μ) - c‖ ≤ μ.real t / μ.real s * ⨍ x in t, ‖f x - c‖ ∂μ := by
  have hs' : μ s ≠ ⊤ := ne_top_of_le_ne_top ht (measure_mono hst)
  have hsr : 0 < μ.real s := ENNReal.toReal_pos hs hs'
  have htr : 0 < μ.real t := hsr.trans_le (measureReal_mono hst ht)
  have hfs : IntegrableOn f s μ := hf.mono_set hst
  have heq : (⨍ x in s, f x ∂μ) - c = ⨍ x in s, (f x - c) ∂μ := by
    rw [setAverage_fun_sub hfs (integrableOn_const hs'), setAverage_const hs hs']
  calc ‖(⨍ x in s, f x ∂μ) - c‖ ≤ (μ.real s)⁻¹ * ∫ x in t, ‖f x - c‖ ∂μ := by
        rw [heq, setAverage_eq, norm_smul, norm_inv, Real.norm_of_nonneg hsr.le]
        gcongr
        refine (norm_integral_le_integral_norm _).trans
          (setIntegral_mono_set ?_ ?_ hst.eventuallyLE)
        · exact (hf.sub (integrableOn_const ht)).norm
        · exact ae_of_all _ fun _ ↦ norm_nonneg _
    _ = μ.real t / μ.real s * ⨍ x in t, ‖f x - c‖ ∂μ := by
        rw [setAverage_eq, smul_eq_mul]
        field_simp

end Subset

section ChangeOfVariables

variable {X Y F : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {e : X ≃ᵐ Y} {a : ℝ≥0∞}

/-- If a measurable equivalence `e` pushes `μ` forward to `a • ν`, then the lower integral of
`g ∘ e` over `e ⁻¹' s` with respect to `μ` is `a` times the lower integral of `g` over `s` with
respect to `ν`. -/
theorem setLIntegral_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (g : Y → ℝ≥0∞)
    (s : Set Y) : ∫⁻ x in e ⁻¹' s, g (e x) ∂μ = a * ∫⁻ y in s, g y ∂ν := by
  rw [← lintegral_map_equiv, ← e.measurableEmbedding.restrict_map, he, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul]

/-- Averages of nonnegative functions are invariant under a measurable equivalence `e` that pushes
`μ` forward to a positive finite multiple of `ν`. -/
theorem setLAverage_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (ha : a ≠ 0)
    (ha' : a ≠ ∞) (g : Y → ℝ≥0∞) (s : Set Y) :
    ⨍⁻ x in e ⁻¹' s, g (e x) ∂μ = ⨍⁻ y in s, g y ∂ν := by
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_comp_preimage_of_map_eq_smul he,
    ← e.map_apply, he, Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_mul_left _ _ ha ha']

/-- If a measurable equivalence `e` pushes `μ` forward to `a • ν`, then the integral of `f ∘ e`
over `e ⁻¹' s` with respect to `μ` is `a.toReal` times the integral of `f` over `s` with respect
to `ν`. -/
theorem setIntegral_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (f : Y → F) (s : Set Y) :
    ∫ x in e ⁻¹' s, f (e x) ∂μ = a.toReal • ∫ y in s, f y ∂ν := by
  rw [← setIntegral_map_equiv, he, Measure.restrict_smul, integral_smul_measure]

/-- Averages are invariant under a measurable equivalence `e` that pushes `μ` forward to a
positive finite multiple of `ν`. -/
theorem setAverage_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (ha : a ≠ 0)
    (ha' : a ≠ ∞) (f : Y → F) (s : Set Y) :
    ⨍ x in e ⁻¹' s, f (e x) ∂μ = ⨍ y in s, f y ∂ν := by
  have hmeas : μ.real (e ⁻¹' s) = a.toReal * ν.real s := by
    rw [measureReal_def, ← e.map_apply, he, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      measureReal_def]
  rw [setAverage_eq, setAverage_eq, setIntegral_comp_preimage_of_map_eq_smul he, hmeas,
    smul_smul, mul_inv_rev, inv_mul_cancel_right₀ (ENNReal.toReal_ne_zero.2 ⟨ha, ha'⟩)]

end ChangeOfVariables

end TauCeti
