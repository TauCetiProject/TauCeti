/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Averages over nested sets

The average of a function over a set `s` is controlled by its average over a larger set `t ⊇ s`,
at the cost of the ratio `μ t / μ s` of their measures.

## Main results

* `TauCeti.MeasureTheory.norm_setAverage_sub_le_of_subset`: the average over a subset `s ⊆ t`
  differs from a constant `c` by at most `μ t / μ s` times the average of `‖f - c‖` over `t`.
-/

public section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

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

end MeasureTheory

end TauCeti
