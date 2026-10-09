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

The average of a function over a set `s` is also controlled by its average over a larger set
`t ⊇ s`, at the cost of the ratio `μ t / μ s` of their measures. The mean oscillation
`⨍_s ‖f - f_s‖` of a function about its own average is, up to a factor `2`, the smallest mean
oscillation about any constant; together these compare mean oscillations on nested sets, as in the
theory of functions of bounded mean oscillation.

Averages are unchanged by a change of variables that rescales the measure by a constant factor,
such as an affine homothety of a finite-dimensional space with its Haar measure: if a measurable
equivalence `e` pushes `μ` forward to `a • ν` with `0 < a < ∞`, then the average of `f ∘ e` over
`e ⁻¹' s` with respect to `μ` is the average of `f` over `s` with respect to `ν`.

## Main results

* `TauCeti.enorm_setAverage_le_setLAverage`: the extended norm of an average over a set is at most
  the average of the extended norm over the set.
* `TauCeti.measure_mul_enorm_setAverage_le`: the measure of a set times the extended norm of the
  average over it is at most the integral of the extended norm over it.
* `TauCeti.norm_setAverage_sub_le_of_subset`: the average over a subset `s ⊆ t`
  differs from a constant `c` by at most `μ t / μ s` times the average of `‖f - c‖` over `t`.
* `TauCeti.setLAverage_le_div_mul_setLAverage_of_subset`: the average of a nonnegative function
  over a subset `s ⊆ t` is at most `μ t / μ s` times its average over `t`.
* `TauCeti.enorm_setAverage_sub_le_of_subset`: the extended-norm form of
  `TauCeti.norm_setAverage_sub_le_of_subset`.
* `TauCeti.setLAverage_enorm_sub_setAverage_le`: the mean oscillation of `f` about its average is
  at most twice its mean oscillation about any constant.
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

/-- The average of a nonnegative function over a subset `s` of `t` is at most `μ t / μ s` times
its average over `t`. -/
theorem setLAverage_le_div_mul_setLAverage_of_subset {g : X → ℝ≥0∞} (hst : s ⊆ t)
    (ht : μ t ≠ ⊤) : ⨍⁻ x in s, g x ∂μ ≤ μ t / μ s * ⨍⁻ x in t, g x ∂μ := by
  rcases eq_or_ne (μ t) 0 with ht0 | ht0
  · rw [setLAverage_eq, setLIntegral_measure_zero _ _ (measure_mono_null hst ht0),
      ENNReal.zero_div]
    exact zero_le
  have h : μ t / μ s * ((∫⁻ x in t, g x ∂μ) / μ t) = (∫⁻ x in t, g x ∂μ) / μ s := by
    rw [ENNReal.div_eq_inv_mul, mul_assoc, ENNReal.mul_div_cancel ht0 ht,
      ← ENNReal.div_eq_inv_mul]
  rw [setLAverage_eq, setLAverage_eq, h]
  exact ENNReal.div_le_div_right (lintegral_mono_set hst) _

/-- The average of `f` over a subset `s` of `t` differs from a constant `c` by at most `μ t / μ s`
times the average of `‖f - c‖ₑ` over `t`. This is the extended-norm form of
`TauCeti.norm_setAverage_sub_le_of_subset`; it needs `f` to be integrable only on `s`. -/
theorem enorm_setAverage_sub_le_of_subset (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ⊤)
    (hf : IntegrableOn f s μ) (c : F) :
    ‖(⨍ x in s, f x ∂μ) - c‖ₑ ≤ μ t / μ s * ⨍⁻ x in t, ‖f x - c‖ₑ ∂μ := by
  have hs' : μ s ≠ ⊤ := ne_top_of_le_ne_top ht (measure_mono hst)
  calc ‖(⨍ x in s, f x ∂μ) - c‖ₑ = ‖⨍ x in s, (f x - c) ∂μ‖ₑ := by
        rw [setAverage_fun_sub hf (integrableOn_const hs'), setAverage_const hs hs']
    _ ≤ ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := enorm_setAverage_le_setLAverage _ _ _
    _ ≤ μ t / μ s * ⨍⁻ x in t, ‖f x - c‖ₑ ∂μ :=
        setLAverage_le_div_mul_setLAverage_of_subset hst ht

/-- The mean oscillation of `f` on `s` about its own average is at most twice its mean oscillation
about any constant `c`. -/
theorem setLAverage_enorm_sub_setAverage_le (hf : IntegrableOn f s μ) (c : F) :
    ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ ≤ 2 * ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := by
  rcases eq_or_ne (μ s) ⊤ with hs | hs
  · simp [setLAverage_eq, hs]
  rcases eq_or_ne (μ s) 0 with hs0 | hs0
  · simp [setLAverage_eq, setLIntegral_measure_zero _ _ hs0]
  have hsub : ⨍ y in s, (f y - c) ∂μ = (⨍ y in s, f y ∂μ) - c := by
    rw [setAverage_fun_sub hf (integrableOn_const hs), setAverage_const hs0 hs]
  have hint : ∫⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ ≤ 2 * ∫⁻ x in s, ‖f x - c‖ₑ ∂μ :=
    calc ∫⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ
        ≤ ∫⁻ x in s, (‖f x - c‖ₑ + ‖(⨍ y in s, f y ∂μ) - c‖ₑ) ∂μ := by
          gcongr with x
          rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
          exact edist_triangle_right _ _ _
      _ = ∫⁻ x in s, ‖f x - c‖ₑ ∂μ + μ s * ‖(⨍ y in s, f y ∂μ) - c‖ₑ := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x in s, ‖f x - c‖ₑ ∂μ + ∫⁻ x in s, ‖f x - c‖ₑ ∂μ := by
          rw [← hsub]
          gcongr
          exact measure_mul_enorm_setAverage_le μ (fun y => f y - c) s
      _ = 2 * ∫⁻ x in s, ‖f x - c‖ₑ ∂μ := (two_mul _).symm
  rw [setLAverage_eq, setLAverage_eq, ← mul_div_assoc]
  exact ENNReal.div_le_div_right hint _

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
