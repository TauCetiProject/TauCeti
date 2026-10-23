/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Logistic.Basic
public import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.Analysis.SpecialFunctions.Sigmoid
public import TauCeti.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Transforms of the logistic distribution

For a logistic law with location `m` and positive scale `s`, this file identifies the exact
exponential-integrability domain and computes the moment-, cumulant-, and characteristic
functions. The formulas are

`M(t) = exp (m * t) * Γ(1 - s * t) * Γ(1 + s * t)` for `-1 / s < t < 1 / s`, and

`φ(t) = exp (i * m * t) * (π * s * t) / sinh (π * s * t)` for `t ≠ 0`.

The real transform follows by changing variables to the defining uniform law and evaluating a
Beta integral. The characteristic function is obtained by analytic continuation to the imaginary
axis, followed by Euler's reflection formula for the Gamma function.

## Main results

* `integrableExpSet_id_logisticMeasure` gives the exact MGF domain.
* `mgf_id_logisticMeasure` and `cgf_id_logisticMeasure` compute the real transforms.
* `charFun_logisticMeasure` computes the characteristic function away from zero, while
  `charFun_logisticMeasure_zero` gives its value at zero.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 23.
-/

public section

open MeasureTheory ProbabilityTheory Set Real
open scoped Topology

namespace TauCeti.Probability

noncomputable section

variable {m s t : ℝ}

/-- On the open unit interval, the exponential of an affine logit is the Beta-integral
integrand, up to its location factor. -/
private lemma exp_mul_logit_eq (u : ℝ) (hu : u ∈ Ioo 0 1) :
    Real.exp (t * (m + s * Real.log (u / (1 - u)))) =
      Real.exp (t * m) * (u ^ (1 + s * t - 1) * (1 - u) ^ (1 - s * t - 1)) := by
  have hu0 : 0 < u := hu.1
  have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
  rw [mul_add, Real.exp_add]
  congr 1
  rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos hu1,
    ← Real.exp_add, Real.log_div hu0.ne' hu1.ne']
  congr 1
  ring

/-- The pointwise logit identity holds almost everywhere on the restricted unit interval. -/
private lemma ae_exp_mul_logit_eq :
    (fun u : ℝ => Real.exp (t * (m + s * Real.log (u / (1 - u))))) =ᵐ[volume.restrict (Ioo 0 1)]
      fun u => Real.exp (t * m) *
        (u ^ (1 + s * t - 1) * (1 - u) ^ (1 - s * t - 1)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact exp_mul_logit_eq u hu

/-- The exponential integrand for a logistic law is integrable exactly when its parameter lies
strictly between `-1 / s` and `1 / s`. -/
@[simp]
theorem integrable_exp_mul_id_logisticMeasure_iff (hs : 0 < s) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (logisticMeasure m s) ↔
      -1 / s < t ∧ t < 1 / s := by
  rw [logisticMeasure_of_pos hs]
  have hmap :
      Integrable (fun x : ℝ => Real.exp (t * x))
          ((uniformMeasure 0 1).map fun u => m + s * Real.log (u / (1 - u))) ↔
        Integrable (fun u : ℝ => Real.exp (t * (m + s * Real.log (u / (1 - u)))))
          (uniformMeasure 0 1) :=
    integrable_map_measure (by fun_prop) (Real.measurable_logit_affine m s).aemeasurable
  rw [hmap, uniformMeasure_eq_smul]
  norm_num
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  rw [integrable_congr ae_exp_mul_logit_eq]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero (t * m)))]
  rw [← IntegrableOn, TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · rw [div_lt_iff₀ hs]
      nlinarith
    · have h : t < 1 / s := by
        rw [lt_div_iff₀ hs]
        nlinarith
      simpa [one_div] using h
  · rintro ⟨hlo, hhi⟩
    have hlo' := (div_lt_iff₀ hs).1 hlo
    have hhi'' : t < 1 / s := by simpa [one_div] using hhi
    have hhi' := (lt_div_iff₀ hs).1 hhi''
    constructor <;> nlinarith

/-- The exact exponential-integrability domain of a logistic law with positive scale `s` is
`(-1 / s, 1 / s)`. -/
@[simp]
theorem integrableExpSet_id_logisticMeasure (hs : 0 < s) :
    integrableExpSet id (logisticMeasure m s) = Ioo (-1 / s) (1 / s) := by
  ext t
  rw [integrableExpSet, mem_ofPred_eq, mem_Ioo]
  simpa only [id_eq] using
    (integrable_exp_mul_id_logisticMeasure_iff (m := m) (t := t) hs)

/-- The moment-generating function of a logistic law on its exact finiteness domain. -/
theorem mgf_id_logisticMeasure (hs : 0 < s) (ht : t ∈ Ioo (-1 / s) (1 / s)) :
    mgf id (logisticMeasure m s) t =
      Real.exp (m * t) * Real.Gamma (1 - s * t) * Real.Gamma (1 + s * t) := by
  have hlo : 0 < 1 + s * t := by
    have := (div_lt_iff₀ hs).1 ht.1
    nlinarith
  have hhi : 0 < 1 - s * t := by
    have h : t < 1 / s := by simpa [one_div] using ht.2
    have := (lt_div_iff₀ hs).1 h
    nlinarith
  rw [mgf, logisticMeasure_of_pos hs,
    integral_map (Real.measurable_logit_affine m s).aemeasurable (by fun_prop)]
  simp only [id_eq]
  rw [uniformMeasure_eq_smul]
  norm_num
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  rw [integral_congr_ae ae_exp_mul_logit_eq, integral_const_mul]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    TauCeti.integral_rpow_mul_one_sub_rpow hlo hhi]
  rw [ProbabilityTheory.beta]
  have hsum : 1 + s * t + (1 - s * t) = (2 : ℝ) := by ring
  rw [hsum, Real.Gamma_two]
  ring_nf

/-- The cumulant-generating function of a logistic law on its exact finiteness domain. -/
theorem cgf_id_logisticMeasure (hs : 0 < s) (ht : t ∈ Ioo (-1 / s) (1 / s)) :
    cgf id (logisticMeasure m s) t =
      m * t + Real.log (Real.Gamma (1 - s * t)) +
        Real.log (Real.Gamma (1 + s * t)) := by
  have hlo : 0 < 1 + s * t := by
    have := (div_lt_iff₀ hs).1 ht.1
    nlinarith
  have hhi : 0 < 1 - s * t := by
    have h : t < 1 / s := by simpa [one_div] using ht.2
    have := (lt_div_iff₀ hs).1 h
    nlinarith
  rw [cgf, mgf_id_logisticMeasure hs ht,
    Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (Real.Gamma_pos_of_pos hhi).ne')
      (Real.Gamma_pos_of_pos hlo).ne',
    Real.log_mul (Real.exp_ne_zero _) (Real.Gamma_pos_of_pos hhi).ne', Real.log_exp]

/-- The holomorphic extension of the logistic moment-generating function to its vertical strip. -/
private def logisticComplexMGF (m s : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (m * z) * Complex.Gamma (1 - s * z) * Complex.Gamma (1 + s * z)

/-- The proposed complex MGF is analytic on the vertical strip over the real MGF domain. -/
private theorem analyticOnNhd_logisticComplexMGF (hs : 0 < s) :
    AnalyticOnNhd ℂ (logisticComplexMGF m s)
      {z : ℂ | z.re ∈ Ioo (-1 / s) (1 / s)} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_Ioo.preimage Complex.continuous_re)
  intro z hz
  have hlo : 0 < (1 + (s : ℂ) * z).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hz' := (div_lt_iff₀ hs).1 hz.1
    nlinarith
  have hhi : 0 < (1 - (s : ℂ) * z).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hz' : z.re < 1 / s := hz.2
    rw [lt_div_iff₀ hs] at hz'
    nlinarith
  have hGamma_lo : DifferentiableAt ℂ Complex.Gamma (1 + (s : ℂ) * z) :=
    Complex.differentiableAt_Gamma _ fun n hn ↦ by
      rw [hn] at hlo
      have hnneg : (0 : ℝ) < -(n : ℝ) := by
        simpa only [Complex.neg_re, Complex.natCast_re] using hlo
      exact (not_lt_of_ge (Nat.cast_nonneg n)) (neg_pos.mp hnneg)
  have hGamma_hi : DifferentiableAt ℂ Complex.Gamma (1 - (s : ℂ) * z) :=
    Complex.differentiableAt_Gamma _ fun n hn ↦ by
      rw [hn] at hhi
      have hnneg : (0 : ℝ) < -(n : ℝ) := by
        simpa only [Complex.neg_re, Complex.natCast_re] using hhi
      exact (not_lt_of_ge (Nat.cast_nonneg n)) (neg_pos.mp hnneg)
  unfold logisticComplexMGF
  exact (((Complex.differentiableAt_exp.comp z (by fun_prop)).mul
    (hGamma_hi.comp z (by fun_prop))).mul
      (hGamma_lo.comp z (by fun_prop))).differentiableWithinAt

/-- The proposed complex MGF agrees with the real MGF on the real interval. -/
private theorem logisticComplexMGF_ofReal (hs : 0 < s) {t : ℝ}
    (ht : t ∈ Ioo (-1 / s) (1 / s)) :
    logisticComplexMGF m s t = mgf id (logisticMeasure m s) t := by
  rw [mgf_id_logisticMeasure hs ht, logisticComplexMGF]
  have hexp : Complex.exp ((m : ℂ) * t) = (Real.exp (m * t) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  have hGamma_hi : Complex.Gamma (1 - (s : ℂ) * t) = (Real.Gamma (1 - s * t) : ℂ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul] using
      (Complex.Gamma_ofReal (1 - s * t))
  have hGamma_lo : Complex.Gamma (1 + (s : ℂ) * t) = (Real.Gamma (1 + s * t) : ℂ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul] using
      (Complex.Gamma_ofReal (1 + s * t))
  rw [hexp, hGamma_hi, hGamma_lo]
  norm_cast

/-- The Gamma-product form of the characteristic function, used before applying the reflection
formula. -/
private theorem charFun_logisticMeasure_eq_gamma (hs : 0 < s) (t : ℝ) :
    charFun (logisticMeasure m s) t =
      Complex.exp ((m : ℂ) * t * Complex.I) *
        Complex.Gamma (1 - (s : ℂ) * t * Complex.I) *
          Complex.Gamma (1 + (s : ℂ) * t * Complex.I) := by
  have hsub : Ioo (-1 / s) (1 / s) ⊆ integrableExpSet id (logisticMeasure m s) := by
    rw [integrableExpSet_id_logisticMeasure hs]
  have hEq : Set.EqOn (complexMGF id (logisticMeasure m s)) (logisticComplexMGF m s)
      {z : ℂ | z.re ∈ Ioo (-1 / s) (1 / s)} :=
    TauCeti.eqOn_complexMGF_of_eqOn_mgf isOpen_Ioo (convex_Ioo _ _) hsub
      (analyticOnNhd_logisticComplexMGF hs) fun _ ht ↦ logisticComplexMGF_ofReal hs ht
  have hzero : (0 : ℝ) ∈ Ioo (-1 / s) (1 / s) := by
    have hinv : 0 < 1 / s := one_div_pos.mpr hs
    constructor
    · rw [div_lt_iff₀ hs]
      norm_num
    · exact hinv
  have hit : ((t : ℂ) * Complex.I) ∈ {z : ℂ | z.re ∈ Ioo (-1 / s) (1 / s)} := by
    simpa using hzero
  have h := hEq hit
  rw [complexMGF_id_mul_I] at h
  simpa only [logisticComplexMGF, mul_assoc] using h

/-- The characteristic function of a positive-scale logistic law is one at zero. -/
theorem charFun_logisticMeasure_zero (hs : 0 < s) :
    charFun (logisticMeasure m s) 0 = 1 := by
  have := isProbabilityMeasure_logisticMeasure hs m
  simp [charFun_zero]

/-- The characteristic function of a logistic law away from its removable singularity at zero. -/
@[simp]
theorem charFun_logisticMeasure (hs : 0 < s) (ht : t ≠ 0) :
    charFun (logisticMeasure m s) t =
      Complex.exp (Complex.I * m * t) *
        (Real.pi * s * t / Real.sinh (Real.pi * s * t) : ℝ) := by
  have hst : s * t ≠ 0 := mul_ne_zero hs.ne' ht
  have hz : (s : ℂ) * t * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne')
      (Complex.ofReal_ne_zero.mpr ht)) Complex.I_ne_zero
  have hsinh : Real.sinh (Real.pi * s * t) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero (mul_ne_zero Real.pi_ne_zero hs.ne') ht
  rw [charFun_logisticMeasure_eq_gamma hs]
  have hGamma :
      Complex.Gamma (1 - (s : ℂ) * t * Complex.I) *
          Complex.Gamma (1 + (s : ℂ) * t * Complex.I) =
        (Real.pi * s * t / Real.sinh (Real.pi * s * t) : ℝ) := by
    calc
      Complex.Gamma (1 - (s : ℂ) * t * Complex.I) *
          Complex.Gamma (1 + (s : ℂ) * t * Complex.I) =
          Complex.Gamma (1 - (s : ℂ) * t * Complex.I) *
            ((s : ℂ) * t * Complex.I *
              Complex.Gamma ((s : ℂ) * t * Complex.I)) := by
            rw [show 1 + (s : ℂ) * t * Complex.I =
              (s : ℂ) * t * Complex.I + 1 by ring,
              Complex.Gamma_add_one _ hz]
      _ = ((s : ℂ) * t * Complex.I) *
          (Complex.Gamma ((s : ℂ) * t * Complex.I) *
            Complex.Gamma (1 - (s : ℂ) * t * Complex.I)) := by ring
      _ = ((s : ℂ) * t * Complex.I) *
          ((Real.pi : ℂ) /
            Complex.sin ((Real.pi : ℂ) * ((s : ℂ) * t * Complex.I))) := by
            rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = (Real.pi * s * t / Real.sinh (Real.pi * s * t) : ℝ) := by
            rw [show (Real.pi : ℂ) * ((s : ℂ) * t * Complex.I) =
              (Real.pi * s * t : ℝ) * Complex.I by push_cast; ring,
              Complex.sin_mul_I, ← Complex.ofReal_sinh]
            push_cast
            field_simp
  rw [mul_assoc, hGamma]
  congr 1
  ring_nf

end

end TauCeti.Probability
