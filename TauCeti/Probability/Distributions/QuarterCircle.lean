/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
public import TauCeti.Probability.Distributions.Semicircle.LocationScale
public import TauCeti.Probability.Distributions.Semicircle.Moments
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Beta.Symmetric
import TauCeti.Probability.Distributions.MarchenkoPastur.Moments
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# The quarter-circle law

The quarter-circle law is the law of `|X|` for `X` distributed as the semicircle law of variance
one, which is supported on `[-2, 2]`. It has density `π⁻¹ √(4 - s²)` on `[0, 2]`.

It is the limiting law of the singular values of `Xₙ / √n` for a square matrix `Xₙ` with i.i.d.
entries of variance one; correspondingly, the square of a quarter-circle variable has the
Marchenko–Pastur law of ratio one, the limiting eigenvalue law of `Xₙ Xₙ* / n`. Both laws are
carried by compact intervals and have the Catalan numbers as moments, which identifies them. The
symmetric beta realization of the semicircle law gives the real moments of the quarter-circle law
and shows that `marchenkoPastur 1` is the image of `Beta(1 / 2, 3 / 2)` under `t ↦ 4 t`.

## Main definitions

* `TauCeti.Probability.quarterCircle`: the image of `semicircleReal 0 1` under `x ↦ |x|`.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_quarterCircle`: total mass one.
* `TauCeti.Probability.quarterCircle_eq_withDensity`: the density `π⁻¹ √(4 - s²)` on `(0, ∞)`.
* `TauCeti.Probability.ae_mem_Icc_quarterCircle`: the law is carried by `[0, 2]`.
* `TauCeti.Probability.support_quarterCircle`: its topological support is exactly `[0, 2]`.
* `TauCeti.Probability.integral_pow_two_mul_quarterCircle`: even moments agree with those of the
  semicircle law.
* `TauCeti.Probability.integral_sq_quarterCircle`: the second moment is one.
* `TauCeti.Probability.integral_rpow_quarterCircle`: the real moments
  `∫ s ^ q = 2 ^ (q + 1) B((q + 1) / 2, 3 / 2) / π` for `q > -1`.
* `TauCeti.Probability.integral_id_quarterCircle`: the mean is `8 / (3 π)`.
* `TauCeti.Probability.map_sq_quarterCircle`: the square of a quarter-circle variable has law
  `marchenkoPastur 1`.
* `TauCeti.Probability.map_sqrt_marchenkoPastur_one`: conversely, the square root of a
  `marchenkoPastur 1` variable has the quarter-circle law.
* `TauCeti.Probability.marchenkoPastur_one_eq_map_betaMeasure`: `marchenkoPastur 1` is the image of
  `Beta(1 / 2, 3 / 2)` under `t ↦ 4 t`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- The quarter-circle law: the law of `|X|` for `X` a semicircle variable of variance one. -/
def quarterCircle : Measure ℝ := (semicircleReal 0 1).map fun x ↦ |x|

theorem quarterCircle_def : quarterCircle = (semicircleReal 0 1).map fun x ↦ |x| := (rfl)

/-- The quarter-circle law is a probability measure. -/
instance isProbabilityMeasure_quarterCircle : IsProbabilityMeasure quarterCircle :=
  ⟨by rw [quarterCircle_def, Measure.map_apply (continuous_abs.measurable) MeasurableSet.univ]
      simp⟩

/-- The quarter-circle law has density `π⁻¹ √(4 - s²)` on the positive half-line. -/
theorem quarterCircle_eq_withDensity :
    quarterCircle = volume.withDensity
      ((Ioi 0).indicator fun s : ℝ ↦ ENNReal.ofReal (Real.pi⁻¹ * Real.sqrt (4 - s ^ 2))) := by
  rw [quarterCircle_def, semicircleReal_eq_withDensity 0 one_pos,
    map_abs_withDensity (by fun_prop)]
  congr 1
  ext s
  by_cases hs : s ∈ Ioi 0
  · simp only [indicator_of_mem hs, NNReal.coe_one, mul_one, sub_zero, neg_sq]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  · simp [indicator_of_notMem hs]

/-- The quarter-circle law is carried by `[0, 2]`. -/
theorem ae_mem_Icc_quarterCircle : ∀ᵐ s ∂quarterCircle, s ∈ Icc (0 : ℝ) 2 := by
  rw [quarterCircle_def]
  refine (ae_map_iff (continuous_abs.measurable.aemeasurable) measurableSet_Icc).2 ?_
  filter_upwards [ae_mem_Icc_semicircleReal 0 1] with x hx
  simp only [NNReal.coe_one, Real.sqrt_one, mul_one, zero_sub, zero_add, mem_Icc] at hx
  exact ⟨abs_nonneg x, abs_le.2 hx⟩

/-- The `2k`th moment of the quarter-circle law is the Catalan number `catalan k`. -/
@[simp]
theorem integral_pow_two_mul_quarterCircle (k : ℕ) :
    ∫ s, s ^ (2 * k) ∂quarterCircle = catalan k := by
  rw [quarterCircle_def, integral_map continuous_abs.measurable.aemeasurable (by fun_prop)]
  calc
    ∫ x, |x| ^ (2 * k) ∂semicircleReal 0 1 =
        ∫ x, x ^ (2 * k) ∂semicircleReal 0 1 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (even_two_mul k).pow_abs x)
    _ = catalan k := by rw [integral_pow_two_mul_semicircleReal_zero]; norm_num

/-- The second moment of the quarter-circle law is one. -/
@[simp]
theorem integral_sq_quarterCircle : ∫ s, s ^ 2 ∂quarterCircle = 1 := by
  simpa using integral_pow_two_mul_quarterCircle 1

/-- The topological support of the quarter-circle law is `[0, 2]`. -/
@[simp]
theorem support_quarterCircle : quarterCircle.support = Icc 0 2 := by
  have himage : (fun x : ℝ ↦ |x|) '' Icc (-2) 2 = Icc 0 2 := by
    ext s
    refine ⟨?_, fun hs ↦ ⟨s, ⟨by linarith [hs.1], hs.2⟩, abs_of_nonneg hs.1⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨abs_nonneg x, abs_le.2 hx⟩
  rw [quarterCircle_def, Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    continuous_abs, support_semicircleReal]
  norm_num [himage]

/-- The real moments of the quarter-circle law: for `q > -1`,
`∫ s ^ q = 2 ^ (q + 1) B((q + 1) / 2, 3 / 2) / π`, with `B` Euler's beta function. -/
theorem integral_rpow_quarterCircle {q : ℝ} (hq : -1 < q) :
    ∫ s, s ^ q ∂quarterCircle = 2 ^ (q + 1) * beta ((q + 1) / 2) (3 / 2) / π := by
  -- Write the quarter-circle law as the image of the centred `Beta(3/2, 3/2)` law under
  -- `z ↦ |2 z|` and use the absolute moments of the centred symmetric beta law.
  have hmom := integral_abs_rpow_mul_one_sub_sq_rpow_map_centered_betaMeasure
    (a := 3 / 2) (q := q) (r := 0) (by norm_num) hq (by norm_num)
  simp only [rpow_zero, mul_one, add_zero] at hmom
  have hbeta : beta (1 / 2) (3 / 2) = π / 2 := by
    rw [beta_one_half_left_eq_two_rpow_mul_beta_self (by norm_num),
      beta_three_halves_three_halves]
    norm_num
    ring
  rw [quarterCircle_def, integral_map continuous_abs.aemeasurable (by fun_prop),
    semicircleReal_def, integral_map (by fun_prop)
      (continuous_abs.measurable.pow_const q).aestronglyMeasurable,
    semicircleMeasure_eq_map_betaMeasure]
  simp only [NNReal.coe_one, sqrt_one, mul_one, zero_add, abs_mul, abs_two]
  simp_rw [mul_rpow zero_le_two (abs_nonneg _)]
  rw [integral_const_mul, hmom, hbeta, rpow_add_one two_ne_zero]
  field_simp

/-- The mean of the quarter-circle law is `8 / (3 π)`. -/
@[simp]
theorem integral_id_quarterCircle : ∫ s, s ∂quarterCircle = 8 / (3 * π) := by
  have h := integral_rpow_quarterCircle (q := 1) (by norm_num)
  norm_num at h
  rw [h, div_div]

/-- The square of a quarter-circle variable has the Marchenko–Pastur law of ratio one. -/
@[simp]
theorem map_sq_quarterCircle : quarterCircle.map (· ^ 2) = marchenkoPastur 1 := by
  -- Both laws are carried by `[0, 4]` and have the Catalan numbers as moments.
  have hsq : ∀ᵐ x ∂quarterCircle.map (· ^ 2), x ∈ Icc (0 : ℝ) 4 := by
    refine (ae_map_iff (by fun_prop) measurableSet_Icc).2 ?_
    filter_upwards [ae_mem_Icc_quarterCircle] with s hs
    exact ⟨sq_nonneg s, by nlinarith [hs.1, hs.2]⟩
  have hmp : ∀ᵐ x ∂marchenkoPastur 1, x ∈ Icc (0 : ℝ) 4 := by
    filter_upwards [ae_mem_Icc_zero_marchenkoPastur 1] with x hx
    norm_num at hx
    exact hx
  refine Measure.ext_of_forall_integral_pow_eq_of_support isCompact_Icc
    (ae_iff.1 hsq) (ae_iff.1 hmp) fun n ↦ ?_
  rw [integral_map (by fun_prop) (by fun_prop), integral_pow_marchenkoPastur_one]
  simp_rw [← pow_mul]
  exact integral_pow_two_mul_quarterCircle n

/-- The square root of a `marchenkoPastur 1` variable has the quarter-circle law. -/
@[simp]
theorem map_sqrt_marchenkoPastur_one : (marchenkoPastur 1).map sqrt = quarterCircle := by
  rw [← map_sq_quarterCircle, Measure.map_map continuous_sqrt.measurable (by fun_prop)]
  have h : (sqrt ∘ fun s : ℝ ↦ s ^ 2) =ᵐ[quarterCircle] id := by
    filter_upwards [ae_mem_Icc_quarterCircle] with s hs
    simp [sqrt_sq hs.1]
  rw [Measure.map_congr h, Measure.map_id]

/-- The Marchenko–Pastur law of ratio one is the image of `Beta(1 / 2, 3 / 2)` under `t ↦ 4 t`. -/
theorem marchenkoPastur_one_eq_map_betaMeasure :
    marchenkoPastur 1 = (betaMeasure (1 / 2) (3 / 2)).map (4 * ·) := by
  rw [← map_sq_quarterCircle, ← betaMeasure_map_centered_sq (by norm_num),
    quarterCircle_def, semicircleReal_def, semicircleMeasure_eq_map_betaMeasure]
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, NNReal.coe_one, sqrt_one, sq_abs]
  ring

end TauCeti.Probability
