/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic
public import TauCeti.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Analysis.Normed.Lp.LpEquiv
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# Hölder inequalities for finite `Lᵖ` spaces

This file bridges the finite `Lᵖ` spaces `PiLp s (fun _ : ι ↦ ℝ)` to `MeasureTheory.eLpNorm` for
the counting measure (`PiLp.eNorm_toLp_eq_eLpNorm_count`) and deduces the log-convex interpolation
Hölder inequality (`PiLp.norm_toLp_rpow_mul_rpow_le`) from
`MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow_of_ae_le`.
-/

public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι]

/-- For `1 ≤ s`, the `eNorm` of a vector in `PiLp s (fun _ : ι ↦ ℝ)` equals the `Lˢ` seminorm
of its coordinate function for the counting measure. -/
theorem eNorm_toLp_eq_eLpNorm_count {s : ℝ≥0∞} [Fact (1 ≤ s)] (f : ι → ℝ) :
    letI : MeasurableSpace ι := ⊤
    ‖WithLp.toLp s f‖ₑ = MeasureTheory.eLpNorm f s MeasureTheory.Measure.count := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  let F : lp (fun _ : ι ↦ ℝ) s := (lpPiLpₗᵢ (fun _ : ι ↦ ℝ) ℝ).symm (WithLp.toLp s f)
  have hnorm : ‖WithLp.toLp s f‖ₑ = ‖F‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, (lpPiLpₗᵢ (fun _ : ι ↦ ℝ) ℝ).symm.norm_map]
  exact hnorm.trans (lp.eLpNorm_count F).symm

/-- Log-convex Hölder inequality for finite `Lᵖ` norms under the complex interpolation relation
`q⁻¹ = (1 - θ) / q₀ + θ / q₁` with `0 ≤ θ ≤ 1`. -/
theorem norm_toLp_rpow_mul_rpow_le {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 <| by
    rw [hq]
    calc ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹
        ≤ ENNReal.ofReal (1 - θ) * 1 + ENNReal.ofReal θ * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (ENNReal.inv_le_one.2 Fact.out) (by positivity))
            (mul_le_mul_of_nonneg_left (ENNReal.inv_le_one.2 Fact.out) (by positivity))
      _ = 1 := by rw [mul_one, mul_one, ← ENNReal.ofReal_add h1θ hθ.1, sub_add_cancel,
          ENNReal.ofReal_one]
  have _ : Fact (1 ≤ q) := ⟨hq1⟩
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have h : ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ₑ ≤
      ‖WithLp.toLp q₀ a‖ₑ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ₑ ^ θ := by
    rw [eNorm_toLp_eq_eLpNorm_count, eNorm_toLp_eq_eLpNorm_count, eNorm_toLp_eq_eLpNorm_count]
    refine MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow_of_ae_le hθ hq
      Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable
      Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun i ↦ ?_)
    rw [Real.eNorm_eq_ofReal_abs, Real.eNorm_eq_ofReal_abs, Real.eNorm_eq_ofReal_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _)),
      abs_of_nonneg (ha i), abs_of_nonneg (hb i),
      ENNReal.ofReal_mul (Real.rpow_nonneg (ha i) _),
      ← ENNReal.ofReal_rpow_of_nonneg (ha i) h1θ, ← ENNReal.ofReal_rpow_of_nonneg (hb i) hθ.1]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) h1θ,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hθ.1,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _))).1 h

end PiLp
