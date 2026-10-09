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
`t ⊇ s`, at the cost of the ratio `μ t / μ s` of their measures.

## Main results

* `TauCeti.enorm_setAverage_le_setLAverage`: the extended norm of an average over a set is at most
  the average of the extended norm over the set.
* `TauCeti.measure_mul_enorm_setAverage_le`: the measure of a set times the extended norm of the
  average over it is at most the integral of the extended norm over it.
* `TauCeti.norm_setAverage_sub_le_of_subset`: the average over a subset `s ⊆ t`
  differs from a constant `c` by at most `μ t / μ s` times the average of `‖f - c‖` over `t`.
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

end Subset

end TauCeti
