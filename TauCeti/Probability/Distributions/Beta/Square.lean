/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
import TauCeti.Probability.Distributions.Beta.Reflection
import TauCeti.Probability.Distributions.Affine
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Squaring a centered symmetric Beta variable

If `X` has the symmetric Beta law with positive shape `a`, then `(2 * X - 1) ^ 2`
has the Beta law with shapes `1 / 2` and `a`. This converts the magnitude of a symmetric
coordinate into its signed distribution, using
`MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self`.

The density calculation combines `Real.Gamma_mul_Gamma_add_half` (Legendre's duplication formula)
with
`map_abs_withDensity` and `TauCeti.MeasureTheory.map_sq_withDensity_restrict_Ioi`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

private theorem betaPDFReal_centered_sq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    2 * x * betaPDFReal (1 / 2) a (x ^ 2) = betaPDFReal a a ((x + 1) / 2) := by
  by_cases hx₁ : x < 1
  · have hx₂ : 0 < x ^ 2 ∧ x ^ 2 < 1 := ⟨sq_pos_of_pos hx, by nlinarith⟩
    have hxhalf : 0 < (x + 1) / 2 ∧ (x + 1) / 2 < 1 := by constructor <;> linarith
    have hsq : (x ^ 2) ^ ((1 / 2 : ℝ) - 1) = x⁻¹ := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
      norm_num [Real.rpow_neg_one]
    have hprod : ((x + 1) / 2) ^ (a - 1) * (1 - (x + 1) / 2) ^ (a - 1) =
        (1 - x ^ 2) ^ (a - 1) / (2 : ℝ) ^ (2 * a - 2) := by
      rw [← Real.mul_rpow hxhalf.1.le (by linarith)]
      have hid : (x + 1) / 2 * (1 - (x + 1) / 2) = (1 - x ^ 2) / 2 ^ 2 := by ring
      rw [hid, Real.div_rpow (by nlinarith) (by norm_num),
        ← Real.rpow_natCast 2 2, ← Real.rpow_mul (by norm_num)]
      congr 2
      ring
    have hpow : (2 : ℝ) ^ (2 * a - 1) = 2 * (2 : ℝ) ^ (2 * a - 2) := by
      have hexp : 2 * a - 1 = (2 * a - 2) + 1 := by ring
      rw [hexp, Real.rpow_add (by norm_num)]
      simp [mul_comm]
    simp only [betaPDFReal, ite_eq_left hx₂, ite_eq_left hxhalf]
    rw [hsq, mul_assoc (1 / beta a a), hprod,
      beta_one_half_left_eq_two_rpow_mul_beta_self ha, hpow]
    field_simp
  · have hx₁' : 1 ≤ x := le_of_not_gt hx₁
    rw [betaPDFReal, ite_eq_right (by rintro ⟨_, h⟩; nlinarith : ¬ (0 < x ^ 2 ∧ x ^ 2 < 1)),
      betaPDFReal, ite_eq_right (by rintro ⟨_, h⟩; linarith)]
    ring

private theorem affineDensity_centered_beta_add_neg (a x : ℝ) :
    affineDensity (-1) 2 (betaPDF a a) x + affineDensity (-1) 2 (betaPDF a a) (-x) =
      betaPDF a a ((x + 1) / 2) := by
  simp only [affineDensity_apply, sub_neg_eq_add]
  have harg : (-x + 1) / 2 = 1 - (x + 1) / 2 := by ring
  rw [harg, betaPDF_one_sub,
    ← add_mul, ← ENNReal.ofReal_add (inv_nonneg.mpr (abs_nonneg _))
      (inv_nonneg.mpr (abs_nonneg _))]
  norm_num

/-- Squaring a symmetric Beta variable after centering and scaling to `(-1, 1)` gives
a Beta law with first shape one half. -/
theorem betaMeasure_map_centered_sq {a : ℝ} (ha : 0 < a) :
    (betaMeasure a a).map (fun x ↦ (-1 + 2 * x) ^ 2) = betaMeasure (1 / 2) a := by
  let ν := (betaMeasure a a).map (fun x ↦ -1 + 2 * x)
  have hf : Measurable (betaPDF a a) := (measurable_betaPDFReal a a).ennreal_ofReal
  have hfold : ν.map (|·|) =
      volume.withDensity ((Ioi 0).indicator fun x ↦ betaPDF a a ((x + 1) / 2)) := by
    dsimp only [ν]
    rw [betaMeasure,
      map_affine_withDensity_volume _ (by norm_num),
      map_abs_withDensity (f := affineDensity (-1) 2 (betaPDF a a))
        (measurable_affineDensity hf _ _)]
    congr 1
    ext x
    exact congrArg ((Ioi 0).indicator · x)
      (funext fun y ↦ affineDensity_centered_beta_add_neg a y)
  have hweight : (fun x ↦ betaPDF a a ((x + 1) / 2))
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x ↦ ENNReal.ofReal (2 * x) * betaPDF (1 / 2) a (x ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [betaPDF, betaPDF, ← ENNReal.ofReal_mul (mul_pos two_pos hx).le,
      betaPDFReal_centered_sq ha hx]
  calc
    _ = (ν.map (|·|)).map (fun x ↦ x ^ 2) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      ext x
      simp [Function.comp_def]
    _ = _ := by
      rw [hfold, withDensity_indicator measurableSet_Ioi, withDensity_congr_ae hweight,
        TauCeti.MeasureTheory.map_sq_withDensity_restrict_Ioi,
        ← restrict_withDensity measurableSet_Ioi, ← betaMeasure,
        Measure.restrict_eq_self_of_ae_mem
          ((ae_mem_Ioo_betaMeasure (1 / 2) a).mono fun _ hx ↦ hx.1)]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- The centered square of a symmetric Beta random variable is Beta distributed with
shapes `1 / 2` and the original shape. -/
theorem HasLaw.centered_sq_betaMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {a : ℝ}
    (hX : HasLaw X (betaMeasure a a) P) (ha : 0 < a) :
    HasLaw (fun ω ↦ (-1 + 2 * X ω) ^ 2) (betaMeasure (1 / 2) a) P :=
  (HasLaw.mk (by fun_prop) (betaMeasure_map_centered_sq ha)).fun_comp hX

end ProbabilityTheory
