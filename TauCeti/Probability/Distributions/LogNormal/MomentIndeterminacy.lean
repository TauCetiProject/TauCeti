/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LogNormal.Basic

/-!
# Moment-indeterminate perturbations of the log-normal distribution

This file constructs the classical Stieltjes family obtained by multiplying the standard
log-normal density by

`1 + ε * sin (2 * π * log x)`.

For `|ε| ≤ 1` this is a probability density.  All members of the family have the same natural
moments as the standard log-normal law, while distinct parameters give distinct measures.  Thus
the natural moments do not determine the log-normal distribution.

The vanishing oscillatory moments are proved from the complex moment-generating function of the
standard Gaussian: at the frequency `2 * π`, the imaginary part vanishes after every integral
shift of the real exponent.

## Main definitions and results

* `logNormalMomentPerturbationPDFReal` and `logNormalMomentPerturbationPDF` are the real- and
  `ℝ≥0∞`-valued perturbed densities.
* `logNormalMomentPerturbation` is the resulting measure.
* `integral_pow_logNormalMomentPerturbation` proves that its `n`th moment is `exp (n² / 2)`.
* `injOn_logNormalMomentPerturbation` proves that different parameters give different laws.

## Reference

C. C. Heyde, *On a Property of the Lognormal Distribution*, Journal of the Royal Statistical
Society, Series B 25(2), 392--393, 1963.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- The bounded oscillatory factor used in the log-normal Stieltjes family. -/
private def logNormalMomentOscillation (x : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * Real.log x)

@[fun_prop]
private theorem measurable_logNormalMomentOscillation :
    Measurable logNormalMomentOscillation := by
  unfold logNormalMomentOscillation
  fun_prop

private theorem logNormalMomentOscillation_abs_le_one (x : ℝ) :
    |logNormalMomentOscillation x| ≤ 1 := by
  simpa [logNormalMomentOscillation] using Real.abs_sin_le_one (2 * Real.pi * Real.log x)

/-- The real-valued density in the log-normal Stieltjes family. -/
@[expose]
def logNormalMomentPerturbationPDFReal (ε x : ℝ) : ℝ :=
  logNormalPDFReal 0 1 x * (1 + ε * Real.sin (2 * Real.pi * Real.log x))

@[simp]
theorem logNormalMomentPerturbationPDFReal_apply (ε x : ℝ) :
    logNormalMomentPerturbationPDFReal ε x =
      logNormalPDFReal 0 1 x * (1 + ε * Real.sin (2 * Real.pi * Real.log x)) := rfl

/-- The `ℝ≥0∞`-valued density in the log-normal Stieltjes family. -/
@[expose]
def logNormalMomentPerturbationPDF (ε x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (logNormalMomentPerturbationPDFReal ε x)

@[simp]
theorem logNormalMomentPerturbationPDF_apply (ε x : ℝ) :
    logNormalMomentPerturbationPDF ε x =
      ENNReal.ofReal
        (logNormalPDFReal 0 1 x * (1 + ε * Real.sin (2 * Real.pi * Real.log x))) := rfl

/-- The log-normal Stieltjes family, obtained by weighting the standard log-normal law by
`1 + ε sin (2π log x)`.  The `ENNReal.ofReal` totalization makes this a measure for every real
`ε`; it is a probability measure when `|ε| ≤ 1`. -/
@[expose]
def logNormalMomentPerturbation (ε : ℝ) : Measure ℝ :=
  (logNormalMeasure 0 1).withDensity fun x =>
    ENNReal.ofReal (1 + ε * Real.sin (2 * Real.pi * Real.log x))

theorem logNormalMomentPerturbation_eq_withDensity_logNormal (ε : ℝ) :
    logNormalMomentPerturbation ε =
      (logNormalMeasure 0 1).withDensity fun x =>
        ENNReal.ofReal (1 + ε * Real.sin (2 * Real.pi * Real.log x)) := rfl

private theorem logNormalMomentPerturbation_mul_abs_le_one {ε : ℝ} (hε : |ε| ≤ 1) (x : ℝ) :
    |ε * logNormalMomentOscillation x| ≤ 1 := by
  rw [abs_mul]
  calc
    |ε| * |logNormalMomentOscillation x| ≤ |ε| * 1 :=
      mul_le_mul_of_nonneg_left (logNormalMomentOscillation_abs_le_one x) (abs_nonneg ε)
    _ ≤ 1 := by simpa using hε

/-- The perturbing weight is nonnegative when `|ε| ≤ 1`. -/
private theorem logNormalMomentPerturbation_weight_nonneg {ε : ℝ} (hε : |ε| ≤ 1) (x : ℝ) :
    0 ≤ 1 + ε * logNormalMomentOscillation x := by
  linarith [neg_abs_le (ε * logNormalMomentOscillation x),
    logNormalMomentPerturbation_mul_abs_le_one hε x]

/-- The real-valued perturbed density is nonnegative on the valid parameter interval. -/
theorem logNormalMomentPerturbationPDFReal_nonneg {ε : ℝ} (hε : |ε| ≤ 1) (x : ℝ) :
    0 ≤ logNormalMomentPerturbationPDFReal ε x :=
  mul_nonneg (logNormalPDFReal_nonneg 0 1 x)
    (logNormalMomentPerturbation_weight_nonneg hε x)

@[fun_prop]
theorem measurable_logNormalMomentPerturbationPDFReal (ε : ℝ) :
    Measurable (logNormalMomentPerturbationPDFReal ε) := by
  unfold logNormalMomentPerturbationPDFReal
  fun_prop

@[fun_prop]
theorem measurable_logNormalMomentPerturbationPDF (ε : ℝ) :
    Measurable (logNormalMomentPerturbationPDF ε) := by
  unfold logNormalMomentPerturbationPDF
  exact (measurable_logNormalMomentPerturbationPDFReal ε).ennreal_ofReal

/-- The Stieltjes-family measure has the displayed density against Lebesgue measure. -/
theorem logNormalMomentPerturbation_eq_withDensity (ε : ℝ) :
    logNormalMomentPerturbation ε =
      volume.withDensity (logNormalMomentPerturbationPDF ε) := by
  rw [logNormalMomentPerturbation, logNormalMeasure_eq_withDensity (v := 1) 0 one_ne_zero]
  change ((volume.withDensity (logNormalPDF 0 1)).withDensity fun x =>
    ENNReal.ofReal (1 + ε * logNormalMomentOscillation x)) = _
  rw [← MeasureTheory.withDensity_mul volume (measurable_logNormalPDF 0 1)
    (measurable_logNormalMomentOscillation.const_mul ε |>.const_add 1 |>.ennreal_ofReal)]
  congr with x
  have hpdf : logNormalPDF 0 1 x = ENNReal.ofReal (logNormalPDFReal 0 1 x) := by
    by_cases hx : x ≤ 0
    · rw [logNormalPDF_of_nonpos hx, logNormalPDFReal_of_nonpos hx, ENNReal.ofReal_zero]
    · rw [logNormalPDF_of_pos (lt_of_not_ge hx), logNormalPDFReal_of_pos (lt_of_not_ge hx)]
  rw [Pi.mul_apply, logNormalMomentPerturbationPDF, logNormalMomentPerturbationPDFReal, hpdf,
    ENNReal.ofReal_mul (logNormalPDFReal_nonneg 0 1 x)]
  rfl

private theorem integral_exp_nat_mul_sin_gaussianReal (n : ℕ) :
    ∫ y, Real.exp ((n : ℝ) * y) * Real.sin (2 * Real.pi * y) ∂gaussianReal 0 1 = 0 := by
  let z : ℂ := (n : ℝ) + (2 * Real.pi : ℝ) * Complex.I
  have hzint : Integrable (fun y : ℝ => Complex.exp (z * y)) (gaussianReal 0 1) := by
    apply integrable_cexp_mul_of_re_mem_integrableExpSet measurable_id.aemeasurable
    simp [z]
  calc
    _ = ∫ y, (Complex.exp (z * y)).im ∂gaussianReal 0 1 := by
      congr with y
      rw [Complex.exp_im]
      simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.ofReal_im, zero_add,
        Complex.mul_im, zero_mul, add_zero]
      congr 2
      ring_nf
    _ = (∫ y, Complex.exp (z * y) ∂gaussianReal 0 1).im := integral_im hzint
    _ = (complexMGF id (gaussianReal 0 1) z).im := by rfl
    _ = (Complex.exp (z * 0 + (1 : ℂ) * z ^ 2 / 2)).im := by
      convert congrArg Complex.im (complexMGF_id_gaussianReal (μ := 0) (v := 1) z) using 1
      norm_num
    _ = 0 := by
      rw [Complex.exp_im]
      have harg : z * 0 + (1 : ℂ) * z ^ 2 / 2 =
          (((n : ℝ) ^ 2 - (2 * Real.pi) ^ 2) / 2 : ℝ) +
            ((n : ℝ) * (2 * Real.pi) : ℝ) * Complex.I := by
        apply Complex.ext
        · simp [z, pow_two]
        · simp [z, pow_two]
          ring_nf
      rw [harg]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add]
      have hsin : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
        convert Real.sin_nat_mul_pi (2 * n) using 1
        push_cast
        ring_nf
      simp only [add_zero]
      rw [hsin, mul_zero]

private theorem integral_pow_mul_oscillation_logNormalMeasure (n : ℕ) :
    ∫ x, x ^ n * logNormalMomentOscillation x ∂logNormalMeasure 0 1 = 0 := by
  rw [logNormalMeasure_map_exp, integral_map measurable_exp.aemeasurable (by fun_prop)]
  simpa only [Function.comp_apply, logNormalMomentOscillation, Real.log_exp,
    Real.exp_nat_mul] using integral_exp_nat_mul_sin_gaussianReal n

/-- Every natural power is integrable under a valid log-normal moment perturbation. -/
theorem integrable_pow_logNormalMomentPerturbation {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) :
    Integrable (fun x => x ^ n) (logNormalMomentPerturbation ε) := by
  rw [logNormalMomentPerturbation]
  change Integrable (fun x => x ^ n) ((logNormalMeasure 0 1).withDensity fun x =>
    ENNReal.ofReal (1 + ε * logNormalMomentOscillation x))
  rw [integrable_withDensity_ofReal_iff
      (ρ := fun x => 1 + ε * logNormalMomentOscillation x)
      ((measurable_const.add (measurable_logNormalMomentOscillation.const_mul ε)).aemeasurable)
      (ae_of_all _ (logNormalMomentPerturbation_weight_nonneg hε))]
  refine (integrable_pow_logNormalMeasure 0 1 n).bdd_smul 2
    ((measurable_const.add
      (measurable_logNormalMomentOscillation.const_mul ε)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  calc
    ‖1 + ε * logNormalMomentOscillation x‖ = |1 + ε * logNormalMomentOscillation x| := rfl
    _ = 1 + ε * logNormalMomentOscillation x :=
      abs_of_nonneg (logNormalMomentPerturbation_weight_nonneg hε x)
    _ ≤ 2 := by
      have hmul : ε * logNormalMomentOscillation x ≤ 1 :=
        (le_abs_self _).trans (logNormalMomentPerturbation_mul_abs_le_one hε x)
      linarith

/-- Every member of the valid Stieltjes family has the same natural moments as the standard
log-normal distribution. -/
theorem integral_pow_logNormalMomentPerturbation {ε : ℝ} (hε : |ε| ≤ 1) (n : ℕ) :
    ∫ x, x ^ n ∂logNormalMomentPerturbation ε =
      Real.exp ((n : ℝ) ^ 2 / 2) := by
  rw [logNormalMomentPerturbation]
  change (∫ x, x ^ n ∂(logNormalMeasure 0 1).withDensity fun x =>
    ENNReal.ofReal (1 + ε * logNormalMomentOscillation x)) = _
  rw [integral_withDensity_ofReal
      (ρ := fun x => 1 + ε * logNormalMomentOscillation x)
      ((measurable_const.add (measurable_logNormalMomentOscillation.const_mul ε)).aemeasurable)
      (ae_of_all _ (logNormalMomentPerturbation_weight_nonneg hε)) (fun x => x ^ n)]
  have hpow := integrable_pow_logNormalMeasure 0 1 n
  have hosc : Integrable (fun x => x ^ n * logNormalMomentOscillation x)
      (logNormalMeasure 0 1) :=
    hpow.mul_bdd measurable_logNormalMomentOscillation.aestronglyMeasurable
      (ae_of_all _ logNormalMomentOscillation_abs_le_one)
  calc
    _ = ∫ x, (x ^ n + ε * (x ^ n * logNormalMomentOscillation x))
        ∂logNormalMeasure 0 1 := by
      congr with x
      simp only [smul_eq_mul]
      ring_nf
    _ = (∫ x, x ^ n ∂logNormalMeasure 0 1) +
        ε * ∫ x, x ^ n * logNormalMomentOscillation x ∂logNormalMeasure 0 1 := by
      rw [integral_add hpow (hosc.const_mul ε), integral_const_mul]
    _ = Real.exp ((n : ℝ) ^ 2 / 2) := by
      rw [integral_pow_mul_oscillation_logNormalMeasure, mul_zero, add_zero,
        integral_pow_logNormalMeasure]
      norm_num

/-- A valid log-normal moment perturbation is a probability measure. -/
theorem isProbabilityMeasure_logNormalMomentPerturbation {ε : ℝ} (hε : |ε| ≤ 1) :
    IsProbabilityMeasure (logNormalMomentPerturbation ε) := by
  rw [isProbabilityMeasure_iff_real]
  have h := integral_pow_logNormalMomentPerturbation hε 0
  simpa [integral_const] using h

private theorem integral_cos_gaussianReal (t : ℝ) :
    ∫ y, Real.cos (t * y) ∂gaussianReal 0 1 = Real.exp (-(t ^ 2) / 2) := by
  have hint : Integrable (fun y : ℝ => Complex.exp (t * y * Complex.I))
      (gaussianReal 0 1) := by
    have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) := integrable_const 1
    refine Integrable.mono' (f := fun y : ℝ => Complex.exp (t * y * Complex.I)) hone
      (by fun_prop) (ae_of_all _ fun y => ?_)
    rw [Complex.norm_exp]
    simp
  calc
    _ = ∫ y, (Complex.exp (t * y * Complex.I)).re ∂gaussianReal 0 1 := by
      congr with y
      rw [Complex.exp_re]
      simp
    _ = (∫ y, Complex.exp (t * y * Complex.I) ∂gaussianReal 0 1).re := integral_re hint
    _ = (charFun (gaussianReal 0 1) t).re := by rw [charFun_apply_real]
    _ = (Complex.exp (t * 0 * Complex.I - (1 : ℂ) * t ^ 2 / 2)).re := by
      convert congrArg Complex.re (charFun_gaussianReal (μ := 0) (v := 1) t) using 1
      norm_num
    _ = Real.exp (-(t ^ 2) / 2) := by
      have harg : (t : ℂ) * 0 * Complex.I - (1 : ℂ) * t ^ 2 / 2 =
          ((-(t ^ 2) / 2 : ℝ) : ℂ) := by
        push_cast
        ring_nf
      rw [harg]
      exact Complex.exp_ofReal_re _

private theorem integral_sq_oscillation_logNormalMeasure_pos :
    0 < ∫ x, logNormalMomentOscillation x ^ 2 ∂logNormalMeasure 0 1 := by
  rw [logNormalMeasure_map_exp, integral_map measurable_exp.aemeasurable (by fun_prop)]
  simp only [logNormalMomentOscillation, Real.log_exp]
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) := integrable_const 1
  have hcos : Integrable (fun y : ℝ => Real.cos (4 * Real.pi * y))
      (gaussianReal 0 1) :=
    hconst.mono' (by fun_prop) (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs, mul_one] using Real.abs_cos_le_one (4 * Real.pi * y))
  calc
    0 < (1 - Real.exp (-((4 * Real.pi) ^ 2) / 2)) / 2 := by
      have hsq : 0 < (4 * Real.pi) ^ 2 := sq_pos_of_pos (by positivity)
      have hneg : -((4 * Real.pi) ^ 2) / 2 < 0 := by linarith
      have hexp : Real.exp (-((4 * Real.pi) ^ 2) / 2) < 1 :=
        Real.exp_lt_one_iff.mpr hneg
      linarith
    _ = ∫ y, Real.sin (2 * Real.pi * y) ^ 2 ∂gaussianReal 0 1 := by
      calc
        _ = (∫ y, (1 - Real.cos (4 * Real.pi * y)) / 2 ∂gaussianReal 0 1) := by
          rw [integral_div, integral_sub hconst hcos, integral_const, integral_cos_gaussianReal]
          norm_num
        _ = _ := by
          congr with y
          rw [show 4 * Real.pi * y = 2 * (2 * Real.pi * y) by ring_nf]
          rw [Real.cos_two_mul_eq_one_sub]
          ring_nf

private theorem integral_oscillation_logNormalMomentPerturbation {ε : ℝ} (hε : |ε| ≤ 1) :
    ∫ x, logNormalMomentOscillation x ∂logNormalMomentPerturbation ε =
      ε * ∫ x, logNormalMomentOscillation x ^ 2 ∂logNormalMeasure 0 1 := by
  rw [logNormalMomentPerturbation]
  change (∫ x, logNormalMomentOscillation x ∂(logNormalMeasure 0 1).withDensity fun x =>
    ENNReal.ofReal (1 + ε * logNormalMomentOscillation x)) = _
  rw [integral_withDensity_ofReal
      (ρ := fun x => 1 + ε * logNormalMomentOscillation x)
      ((measurable_const.add (measurable_logNormalMomentOscillation.const_mul ε)).aemeasurable)
      (ae_of_all _ (logNormalMomentPerturbation_weight_nonneg hε))
      logNormalMomentOscillation]
  have hosc : Integrable logNormalMomentOscillation (logNormalMeasure 0 1) :=
    integrable_const 1 |>.mono' measurable_logNormalMomentOscillation.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa using logNormalMomentOscillation_abs_le_one x)
  have hsq : Integrable (fun x => logNormalMomentOscillation x ^ 2)
      (logNormalMeasure 0 1) :=
    integrable_const 1 |>.mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_sq]
      simpa only [sq_abs, one_pow] using
        (sq_le_sq₀ (abs_nonneg _) zero_le_one).2
          (logNormalMomentOscillation_abs_le_one x))
  calc
    _ = ∫ x, (logNormalMomentOscillation x +
        ε * logNormalMomentOscillation x ^ 2) ∂logNormalMeasure 0 1 := by
      congr with x
      simp only [smul_eq_mul]
      ring_nf
    _ = (∫ x, logNormalMomentOscillation x ∂logNormalMeasure 0 1) +
        ε * ∫ x, logNormalMomentOscillation x ^ 2 ∂logNormalMeasure 0 1 := by
      rw [integral_add hosc (hsq.const_mul ε), integral_const_mul]
    _ = _ := by
      rw [show (∫ x, logNormalMomentOscillation x ∂logNormalMeasure 0 1) = 0 by
        simpa using integral_pow_mul_oscillation_logNormalMeasure 0, zero_add]

/-- Distinct valid perturbation parameters give distinct probability measures. -/
theorem injOn_logNormalMomentPerturbation :
    Set.InjOn logNormalMomentPerturbation (Set.Icc (-1) 1) := by
  intro ε hε δ hδ hmeasure
  have hεabs : |ε| ≤ 1 := abs_le.mpr hε
  have hδabs : |δ| ≤ 1 := abs_le.mpr hδ
  have hint := congrArg (fun μ : Measure ℝ => ∫ x, logNormalMomentOscillation x ∂μ) hmeasure
  rw [integral_oscillation_logNormalMomentPerturbation hεabs,
    integral_oscillation_logNormalMomentPerturbation hδabs] at hint
  nlinarith [integral_sq_oscillation_logNormalMeasure_pos]

/-- The family of log-normal moment perturbations is measurable in its real parameter. -/
@[fun_prop]
theorem measurable_logNormalMomentPerturbation :
    Measurable logNormalMomentPerturbation := by
  unfold logNormalMomentPerturbation
  exact measurable_withDensity
    ((measurable_const.add
      (measurable_fst.mul
        (measurable_logNormalMomentOscillation.comp measurable_snd))).ennreal_ofReal)

end TauCeti.Probability
