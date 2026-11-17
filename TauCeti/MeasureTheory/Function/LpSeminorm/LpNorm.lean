/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Bounds for the real-valued `Lᵖ` norm

Helpers converting `eLpNorm` estimates into bounds for the real-valued `Lᵖ` norm `lpNorm` and
for the Bochner `L¹` integral `∫ x, ‖f x‖ ∂μ`:

* `MeasureTheory.lpNorm_le_mul_lpNorm_of_ae_le_mul` — a pointwise bound `‖f x‖ ≤ c ‖g x‖` almost
  everywhere bounds `lpNorm f p μ ≤ c * lpNorm g p μ` when `g ∈ Lᵖ(μ)`. This is the `lpNorm` form
  of Mathlib's `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul`. Since `lpNorm` is `0` off
  `Lᵖ`, the hypothesis `g ∈ Lᵖ(μ)` is needed. It is the estimate for multiplication by a bounded
  measurable coefficient, as for the lower-order terms of a differential operator.
* `MeasureTheory.lpNorm_le_lpNorm_of_eLpNorm_le` — transfers `eLpNorm f p μ ≤ eLpNorm g p μ` to
  `lpNorm f p μ ≤ lpNorm g p μ` when `g ∈ Lᵖ(μ)`.
* `MeasureTheory.lpNorm_lt_of_eLpNorm_lt_ofReal` — transfers `eLpNorm f p μ < ENNReal.ofReal η`
  to `lpNorm f p μ < η` with no extra hypotheses.
* `MeasureTheory.integral_norm_le_integral_norm_of_eLpNorm_one_le` — transfers
  `eLpNorm f 1 μ ≤ eLpNorm g 1 μ` to `∫ x, ‖f x‖ ∂μ ≤ ∫ x, ‖g x‖ ∂μ` when `g` is integrable.
* `MeasureTheory.integral_norm_lt_of_eLpNorm_one_lt_ofReal` — transfers
  `eLpNorm f 1 μ < ENNReal.ofReal η` to `∫ x, ‖f x‖ ∂μ < η` with no extra hypotheses.
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

/-- If `g ∈ Lᵖ(μ)` and `eLpNorm f p μ ≤ eLpNorm g p μ`, then `lpNorm f p μ ≤ lpNorm g p μ`. -/
theorem lpNorm_le_lpNorm_of_eLpNorm_le {f : α → F} {g : α → G} (hg : MemLp g p μ)
    (h : eLpNorm f p μ ≤ eLpNorm g p μ) :
    lpNorm f p μ ≤ lpNorm g p μ := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top h

/-- If `eLpNorm f p μ < ENNReal.ofReal η`, then `lpNorm f p μ < η`. Neither `MemLp f p μ` nor
`0 ≤ η` is needed: both finiteness and `0 < η` follow from the strict inequality. -/
theorem lpNorm_lt_of_eLpNorm_lt_ofReal {f : α → F} {η : ℝ}
    (h : eLpNorm f p μ < ENNReal.ofReal η) :
    lpNorm f p μ < η := by
  have hη : 0 < η := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le h)
  rw [← toReal_eLpNorm]
  exact ((ENNReal.toReal_lt_toReal (ne_top_of_lt h)
    ENNReal.ofReal_ne_top).mpr h).trans_eq (ENNReal.toReal_ofReal hη.le)

/-- If `g` is integrable and `eLpNorm f 1 μ ≤ eLpNorm g 1 μ`, then
`∫ x, ‖f x‖ ∂μ ≤ ∫ x, ‖g x‖ ∂μ`. No measurability hypothesis on `f` is needed: finiteness of
`eLpNorm f 1 μ` follows from the inequality. -/
theorem integral_norm_le_integral_norm_of_eLpNorm_one_le {f : α → F} {g : α → G}
    (hg : Integrable g μ) (h : eLpNorm f 1 μ ≤ eLpNorm g 1 μ) :
    ∫ x, ‖f x‖ ∂μ ≤ ∫ x, ‖g x‖ ∂μ := by
  have hg1 : MemLp g 1 μ := memLp_one_iff_integrable.mpr hg
  have hf : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top hg1.eLpNorm_ne_top h)
  rw [← lpNorm_one_eq_integral_norm hf, ← lpNorm_one_eq_integral_norm hg.aestronglyMeasurable]
  exact lpNorm_le_lpNorm_of_eLpNorm_le hg1 h

/-- If `eLpNorm f 1 μ < ENNReal.ofReal η`, then `∫ x, ‖f x‖ ∂μ < η`. Neither integrability of `f`
nor `0 ≤ η` is needed: both follow from the strict inequality. -/
theorem integral_norm_lt_of_eLpNorm_one_lt_ofReal {f : α → F} {η : ℝ}
    (h : eLpNorm f 1 μ < ENNReal.ofReal η) :
    ∫ x, ‖f x‖ ∂μ < η := by
  have hf : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_lt h)
  rw [← lpNorm_one_eq_integral_norm hf]
  exact lpNorm_lt_of_eLpNorm_lt_ofReal h

end MeasureTheory
