/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener
import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Checks for Wiener's lemma on the line

Checks for `TauCeti.tendsto_average_norm_charFun_sq`: for a finite measure `σ` on `ℝ` with
characteristic function `φ_σ = charFun σ`,
`T⁻¹ ∫₀ᵀ |φ_σ(t)|² dt → Σ_ξ σ({ξ})²`.

* `σ = δ₀`: `|φ_σ|² = 1`, and the limit is `1`.
* `σ = (δ₀ + δ₁)/2`: `|φ_σ(t)|² = (1 + cos t)/2`, and the limit is `1/2 = 1/4 + 1/4`.
* `σ` Lebesgue measure on `[0, 1]`, which is the uniform law `uniformMeasure 0 1`: for `t ≠ 0`,
  `|φ_σ(t)|² = (2 - 2 cos t)/t²`; at `t = 0` the value is `1`; at `t = π` both sides are `4/π²`.
  The limit is `0`, since `σ` has no atoms.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Real Set TauCeti.Probability
open scoped Topology

namespace TauCeti.Examples.Wiener

/-! ### The Dirac mass at `0` -/

/-- For `σ = δ₀`, `|φ_σ|² = 1`. -/
example (t : ℝ) : ‖charFun (Measure.dirac (0 : ℝ)) t‖ ^ 2 = 1 := by
  simp

/-- For `σ = δ₀`, the averages of `|φ_σ|²` tend to `1`. -/
example :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun (Measure.dirac (0 : ℝ)) t‖ ^ 2)
      atTop (𝓝 1) := by
  convert tendsto_average_norm_charFun_sq (Measure.dirac (0 : ℝ)) using 2
  rw [tsum_eq_single 0 fun ξ hξ => by simp [measureReal_def,
    Set.indicator_of_notMem (show (0 : ℝ) ∉ {ξ} from Ne.symm hξ)]]
  simp

/-! ### Two atoms -/

/-- The measure `(δ₀ + δ₁)/2`. -/
def twoAtoms : Measure ℝ := (2⁻¹ : NNReal) • (Measure.dirac 0 + Measure.dirac 1)

/-- The measure `(δ₀ + δ₁)/2` is finite. -/
instance isFiniteMeasure_twoAtoms : IsFiniteMeasure twoAtoms := by
  unfold twoAtoms
  infer_instance

/-- The characteristic function of `(δ₀ + δ₁)/2` is `(1 + e^{it})/2`. -/
theorem charFun_twoAtoms (t : ℝ) : charFun twoAtoms t = (1 + cexp (t * I)) / 2 := by
  have hint (x : ℝ) : Integrable (fun y : ℝ => cexp (t * y * I)) (Measure.dirac x) :=
    integrable_dirac (by simp)
  rw [twoAtoms, charFun_apply_real, integral_smul_nnreal_measure,
    integral_add_measure (hint 0) (hint 1), integral_dirac, integral_dirac]
  simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, ofReal_one, mul_one]
  rw [NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

/-- For `σ = (δ₀ + δ₁)/2`, `|φ_σ(t)|² = (1 + cos t)/2`. -/
example (t : ℝ) : ‖charFun twoAtoms t‖ ^ 2 = (1 + Real.cos t) / 2 := by
  rw [charFun_twoAtoms, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [div_re, div_im, add_re, add_im, one_re, one_im, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im]
  norm_num
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The atoms of `(δ₀ + δ₁)/2` are `0` and `1`, each of mass `1/2`. -/
theorem measureReal_twoAtoms_singleton (ξ : ℝ) :
    twoAtoms.real {ξ} = (if ξ = 0 then 1 / 2 else 0) + (if ξ = 1 then 1 / 2 else 0) := by
  simp only [twoAtoms, measureReal_def, smul_apply, add_apply,
    Measure.dirac_apply' _ (measurableSet_singleton ξ), indicator, mem_singleton_iff]
  split_ifs with h0 h1 h1 <;> subst_vars <;> norm_num [ENNReal.smul_def] at *

/-- For `σ = (δ₀ + δ₁)/2`, the averages of `|φ_σ|²` tend to `1/2 = 1/4 + 1/4`. -/
example :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun twoAtoms t‖ ^ 2) atTop (𝓝 (1 / 2)) := by
  convert tendsto_average_norm_charFun_sq twoAtoms using 2
  rw [tsum_eq_sum (s := {0, 1}) fun ξ hξ => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hξ
    simp [measureReal_twoAtoms_singleton, hξ.1, hξ.2]]
  simp [measureReal_twoAtoms_singleton]
  norm_num

/-! ### Lebesgue measure on `[0, 1]` -/

/-- Lebesgue measure on `[0, 1]` is the uniform law `uniformMeasure 0 1`, which is normalised
Lebesgue measure on `Ioc 0 1`. -/
example : uniformMeasure 0 1 = volume.restrict (Icc (0 : ℝ) 1) := by
  rw [uniformMeasure_eq_smul, sub_zero, ENNReal.ofReal_one, inv_one, one_smul,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- The characteristic function of Lebesgue measure on `[0, 1]` at `t ≠ 0` is
`(e^{it} - 1)/(it)`. -/
example {t : ℝ} (ht : t ≠ 0) :
    charFun (uniformMeasure 0 1) t = (cexp (t * I) - 1) / (t * I) := by
  rw [charFun_uniformMeasure zero_lt_one ht]
  simp [mul_comm]

/-- For Lebesgue measure on `[0, 1]` and `t ≠ 0`, `|φ_σ(t)|² = (2 - 2 cos t)/t²`. -/
private theorem norm_charFun_uniformMeasure_sq {t : ℝ} (ht : t ≠ 0) :
    ‖charFun (uniformMeasure 0 1) t‖ ^ 2 = (2 - 2 * Real.cos t) / t ^ 2 := by
  rw [charFun_uniformMeasure zero_lt_one ht, ← Complex.normSq_eq_norm_sq]
  simp [normSq_apply, ← mul_comm (t : ℂ) I, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, sq]
  linear_combination Real.sin_sq_add_cos_sq t / (t * t)

/-- At `t = 0` the value is `1`, the total mass, which is the limit of `(2 - 2 cos t)/t²` as
`t → 0`; the formula itself evaluates to `0` there because Lean defines `x / 0 = 0`. -/
example : ‖charFun (uniformMeasure 0 1) 0‖ ^ 2 = 1 := by
  simp [charFun_uniformMeasure_zero zero_lt_one]

/-- At `t = π`, `|φ_σ(π)|² = 4/π²`. -/
example : ‖charFun (uniformMeasure 0 1) π‖ ^ 2 = 4 / π ^ 2 := by
  rw [norm_charFun_uniformMeasure_sq Real.pi_ne_zero, Real.cos_pi]
  ring

/-- For Lebesgue measure on `[0, 1]`, which has no atoms, the averages of `|φ_σ|²` tend to `0`. -/
example :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T,
      ‖charFun (uniformMeasure 0 1) t‖ ^ 2) atTop (𝓝 0) :=
  (tendsto_average_norm_charFun_sq_zero_iff _).2 fun ξ => by
    rw [uniformMeasure_apply, measure_mono_null inter_subset_left
      Real.volume_singleton, mul_zero]

end TauCeti.Examples.Wiener
