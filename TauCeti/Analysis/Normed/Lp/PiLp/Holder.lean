/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.MeasureTheory.Function.LpSeminorm.Count
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# Hölder inequalities for finite `Lᵖ` spaces

This file bridges the finite `Lᵖ` norms `‖WithLp.toLp s f‖` (`s ≠ 0`) to `MeasureTheory.eLpNorm`
for the counting measure (`TauCeti.ofReal_norm_toLp_eq_eLpNorm_count`) and deduces the log-convex
interpolation Hölder inequality (`TauCeti.norm_toLp_rpow_mul_rpow_le`) from
`MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow_of_ae_le`.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- For `s ≠ 0`, `ENNReal.ofReal ‖WithLp.toLp s f‖` equals the `Lˢ` seminorm of `f` for the
counting measure. -/
theorem ofReal_norm_toLp_eq_eLpNorm_count {s : ℝ≥0∞} (hs : s ≠ 0) (f : ι → ℝ) :
    letI : MeasurableSpace ι := ⊤
    ENNReal.ofReal ‖WithLp.toLp s f‖ = MeasureTheory.eLpNorm f s MeasureTheory.Measure.count := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  rcases eq_or_ne s ∞ with rfl | hs_top
  · rw [PiLp.norm_eq_ciSup, MeasureTheory.eLpNorm_count_top]
    cases isEmpty_or_nonempty ι
    · simp
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i ↦ |f i|
      have hL : (⨆ i, ‖WithLp.toLp ∞ f i‖) = |f i₀| :=
        le_antisymm (ciSup_le fun i ↦ by simpa [PiLp.toLp_apply] using hi₀ i)
          ((le_ciSup (Set.Finite.bddAbove (Set.finite_range _)) i₀).trans_eq' (by simp))
      have hR : (⨆ i, ‖f i‖ₑ) = ENNReal.ofReal |f i₀| := le_antisymm
        (iSup_le fun i ↦ by rw [Real.eNorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hi₀ i))
        ((Real.eNorm_eq_ofReal_abs _).symm.trans_le (le_iSup (fun i ↦ ‖f i‖ₑ) i₀))
      rw [hL, hR]
  · have hs' : 0 < s.toReal := ENNReal.toReal_pos hs hs_top
    rw [PiLp.norm_eq_sum hs', MeasureTheory.eLpNorm_count_eq_tsum hs hs_top, tsum_fintype,
      ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity),
      ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
    exact congrArg (· ^ (1 / s.toReal)) (Finset.sum_congr rfl fun i _ ↦ by
      rw [PiLp.toLp_apply, Real.norm_eq_abs, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs'.le,
        Real.eNorm_eq_ofReal_abs])

/-- Log-convex Hölder inequality for finite `Lᵖ` norms under the complex interpolation relation
`q⁻¹ = (1 - θ) / q₀ + θ / q₁` with `0 ≤ θ ≤ 1` and nonzero exponents `q₀, q₁`. -/
theorem norm_toLp_rpow_mul_rpow_le {q₀ q₁ q : ℝ≥0∞} (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2
  have hq_ne : q ≠ 0 := fun h ↦
    (hq.symm ▸ ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 hq₀),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 hq₁)⟩) (by simp [h])
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have h : ENNReal.ofReal ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ENNReal.ofReal ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ENNReal.ofReal ‖WithLp.toLp q₁ b‖ ^ θ := by
    rw [ofReal_norm_toLp_eq_eLpNorm_count hq_ne, ofReal_norm_toLp_eq_eLpNorm_count hq₀,
      ofReal_norm_toLp_eq_eLpNorm_count hq₁]
    refine MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow_of_ae_le hθ hq
      Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable
      Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun i ↦ ?_)
    rw [Real.eNorm_eq_ofReal_abs, Real.eNorm_eq_ofReal_abs, Real.eNorm_eq_ofReal_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _)),
      abs_of_nonneg (ha i), abs_of_nonneg (hb i),
      ENNReal.ofReal_mul (Real.rpow_nonneg (ha i) _),
      ← ENNReal.ofReal_rpow_of_nonneg (ha i) h1θ, ← ENNReal.ofReal_rpow_of_nonneg (hb i) hθ.1]
  rw [ENNReal.ofReal_rpow_of_nonneg (PiLp.norm_nonneg' _) h1θ,
    ENNReal.ofReal_rpow_of_nonneg (PiLp.norm_nonneg' _) hθ.1,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (PiLp.norm_nonneg' _) _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg (PiLp.norm_nonneg' _) _)
    (Real.rpow_nonneg (PiLp.norm_nonneg' _) _))).1 h

end TauCeti
