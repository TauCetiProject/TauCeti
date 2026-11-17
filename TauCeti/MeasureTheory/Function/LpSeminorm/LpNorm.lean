/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Measure.Support

/-!
# Pointwise bounds and `L^∞` interval norms for the real-valued `Lᵖ` norm

A pointwise bound `‖f x‖ ≤ c ‖g x‖` almost everywhere bounds the real-valued `Lᵖ` norm:
`lpNorm f p μ ≤ c * lpNorm g p μ` (`MeasureTheory.lpNorm_le_mul_lpNorm_of_ae_le_mul`). This is
the `lpNorm` form of Mathlib's `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul`. Since
`lpNorm` is `0` off `Lᵖ`, the hypothesis `g ∈ Lᵖ(μ)` is needed. It is the estimate for
multiplication by a bounded measurable coefficient, as for the lower-order terms of a
differential operator.

For an open-positive measure `μ` on `ℝ` and a nonempty open interval `(a, b)`, the real-valued
`L^∞` norm of the identity function equals `max |a| |b|`
(`MeasureTheory.lpNorm_id_exponent_top_restrict_Ioo`). Combined with
`MeasureTheory.lpNorm_const_smul`, this computes the `L^∞` norm of any linear map `x ↦ c * x` on
`(a, b)`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α F G : Type*} {m : MeasurableSpace α} [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p : ℝ≥0∞} {μ : Measure α}

/-- **A pointwise bound bounds `lpNorm`.** If `g ∈ Lᵖ(μ)` and `‖f x‖ ≤ c ‖g x‖` for almost every
`x`, then `lpNorm f p μ ≤ c * lpNorm g p μ`. -/
theorem lpNorm_le_mul_lpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g p μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
    lpNorm f p μ ≤ c * lpNorm g p μ := by
  rcases lt_or_ge c 0 with hc | hc
  · -- For `c < 0` the bound forces `f = 0` and `g = 0` almost everywhere.
    obtain ⟨hf0, hg0⟩ := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, hf0, hg0, ENNReal.toReal_zero, mul_zero]
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, ← ENNReal.toReal_ofReal hc, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top)
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf h p)

/-- For an open-positive measure `μ` on `ℝ` and a nonempty open interval `(a, b)`, the real-valued
`L^∞` norm of the identity function is `max |a| |b|`. -/
@[simp]
theorem lpNorm_id_exponent_top_restrict_Ioo (μ : Measure ℝ) [μ.IsOpenPosMeasure]
    {a b : ℝ} (hab : a < b) :
    lpNorm (id : ℝ → ℝ) ∞ (μ.restrict (Set.Ioo a b)) = max |a| |b| := by
  rw [← toReal_eLpNorm, eLpNorm_exponent_top continuous_id.aestronglyMeasurable,
    eLpNormEssSup_eq_essSup_eNorm]
  simp only [id_eq]
  rw [TauCeti.essSup_eq_iSup_support _ continuous_eNorm.lowerSemicontinuous Measure.support_mem_ae,
    Measure.support_restrict_of_isOpen μ isOpen_Ioo, closure_Ioo hab.ne]
  have hsup : (⨆ x ∈ Set.Icc a b, ‖x‖ₑ) = ENNReal.ofReal (max |a| |b|) := by
    refine le_antisymm (iSup₂_le fun x hx => ?_) ?_
    · rw [Real.eNorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (abs_le_max_abs_abs hx.1 hx.2)
    · rw [ENNReal.ofReal_max]
      exact max_le
        (le_iSup₂_of_le a (Set.left_mem_Icc.2 hab.le) (Real.eNorm_eq_ofReal_abs a).ge)
        (le_iSup₂_of_le b (Set.right_mem_Icc.2 hab.le) (Real.eNorm_eq_ofReal_abs b).ge)
  rw [hsup, ENNReal.toReal_ofReal (le_max_of_le_left (abs_nonneg a))]

end MeasureTheory
