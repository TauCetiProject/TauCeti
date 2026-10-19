/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Probability.Moments.ComplexMGF
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Transforms of the Gumbel distribution

For a Gumbel law with location `m` and positive scale `s`, this file identifies the exact
exponential-integrability domain and computes the moment-, cumulant-, and characteristic
functions. The formulas are

`M(t) = exp (m * t) * Gamma (1 - s * t)` for `t < 1 / s`, and

`phi(t) = exp (i * m * t) * Gamma (1 - i * s * t)` for every real `t`.

These identities follow from the exponential-pushforward construction of the Gumbel law: the
exponential transform becomes a real power of a rate-one exponential variable. The characteristic
function is then obtained from the same Gamma formula by analytic continuation.

## Main results

* `integrableExpSet_id_gumbelMeasure` gives the exact MGF domain.
* `mgf_id_gumbelMeasure` and `cgf_id_gumbelMeasure` compute the real transforms.
* `charFun_gumbelMeasure` computes the characteristic function.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 22.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {m s t : ℝ}

/-- On the positive half-line, the exponential transform in the Gumbel construction is a
constant multiple of a real power. -/
private lemma exp_mul_gumbelMap_eq_rpow {e : ℝ} (he : 0 < e) :
    Real.exp (t * (m - s * Real.log e)) = Real.exp (m * t) * e ^ (-s * t) := by
  rw [Real.rpow_def_of_pos he, ← Real.exp_add]
  congr 1
  ring_nf

/-- The exponential integrand for a Gumbel law is integrable exactly below `1 / s`. -/
@[simp]
theorem integrable_exp_mul_id_gumbelMeasure_iff (hs : 0 < s) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gumbelMeasure m s) ↔ t < 1 / s := by
  rw [gumbelMeasure_of_pos hs]
  have hmap :
      Integrable (fun x : ℝ => Real.exp (t * x))
          ((expMeasure 1).map fun e => m - s * Real.log e) ↔
        Integrable (fun e : ℝ => Real.exp (t * (m - s * Real.log e))) (expMeasure 1) :=
    integrable_map_measure (by fun_prop)
      (measurable_const.sub (measurable_const.mul Real.measurable_log)).aemeasurable
  rw [hmap]
  rw [integrable_congr (by
    filter_upwards [ae_pos_expMeasure 1] with e he
    exact exp_mul_gumbelMap_eq_rpow he)]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero (m * t)))]
  rw [integrable_rpow_expMeasure_iff one_pos]
  rw [lt_div_iff₀ hs]
  constructor <;> intro h <;> nlinarith

/-- The exact exponential-integrability domain of a positive-scale Gumbel law is
`(-∞, 1 / s)`. -/
@[simp]
theorem integrableExpSet_id_gumbelMeasure (hs : 0 < s) :
    integrableExpSet id (gumbelMeasure m s) = Iio (1 / s) := by
  ext t
  rw [integrableExpSet, mem_ofPred_eq, mem_Iio]
  simpa only [id_eq] using
    (integrable_exp_mul_id_gumbelMeasure_iff (m := m) (s := s) (t := t) hs)

/-- The moment-generating function of a positive-scale Gumbel law on its exact finiteness
domain. -/
theorem mgf_id_gumbelMeasure (hs : 0 < s) (ht : t < 1 / s) :
    mgf id (gumbelMeasure m s) t = Real.exp (m * t) * Real.Gamma (1 - s * t) := by
  have hshape : 0 < 1 - s * t := by
    rw [lt_div_iff₀ hs] at ht
    nlinarith
  rw [mgf, gumbelMeasure_of_pos hs]
  have hmap :
      ∫ x : ℝ, Real.exp (t * id x) ∂(expMeasure 1).map (fun e => m - s * Real.log e) =
        ∫ e : ℝ, Real.exp (t * id (m - s * Real.log e)) ∂expMeasure 1 :=
    integral_map
      (measurable_const.sub (measurable_const.mul Real.measurable_log)).aemeasurable (by fun_prop)
  rw [hmap]
  simp only [id_eq]
  rw [integral_congr_ae (by
    filter_upwards [ae_pos_expMeasure 1] with e he
    exact exp_mul_gumbelMap_eq_rpow he)]
  rw [integral_const_mul, integral_rpow_expMeasure one_pos (q := -s * t) (by linarith)]
  simp only [one_rpow, div_one]
  congr 2
  ring_nf

/-- The cumulant-generating function of a positive-scale Gumbel law on its exact finiteness
domain. -/
theorem cgf_id_gumbelMeasure (hs : 0 < s) (ht : t < 1 / s) :
    cgf id (gumbelMeasure m s) t = m * t + Real.log (Real.Gamma (1 - s * t)) := by
  have hshape : 0 < 1 - s * t := by
    rw [lt_div_iff₀ hs] at ht
    nlinarith
  rw [cgf, mgf_id_gumbelMeasure hs ht,
    Real.log_mul (Real.exp_ne_zero _) (Real.Gamma_pos_of_pos hshape).ne', Real.log_exp]

/-- The holomorphic extension of the Gumbel moment-generating function to the half-plane over
its real domain. -/
private def gumbelComplexMGF (m s : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (m * z) * Complex.Gamma (1 - s * z)

/-- The proposed complex Gumbel MGF is analytic on its natural half-plane. -/
private theorem analyticOnNhd_gumbelComplexMGF (hs : 0 < s) :
    AnalyticOnNhd ℂ (gumbelComplexMGF m s) {z : ℂ | z.re < 1 / s} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_lt Complex.continuous_re continuous_const)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  have hshape : 0 < (1 - (s : ℂ) * z).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [lt_div_iff₀ hs] at hz
    nlinarith
  have hGamma : DifferentiableAt ℂ Complex.Gamma (1 - (s : ℂ) * z) :=
    Complex.differentiableAt_Gamma _ fun n hn ↦ by
      rw [hn] at hshape
      have hnneg : (0 : ℝ) < -(n : ℝ) := by
        simpa only [Complex.neg_re, Complex.natCast_re] using hshape
      exact (not_lt_of_ge (Nat.cast_nonneg n)) (neg_pos.mp hnneg)
  unfold gumbelComplexMGF
  exact ((Complex.differentiableAt_exp.comp z (by fun_prop)).mul
    (hGamma.comp z (by fun_prop))).differentiableWithinAt

/-- The proposed complex Gumbel MGF agrees with the real MGF on its real domain. -/
private theorem gumbelComplexMGF_ofReal (hs : 0 < s) {t : ℝ} (ht : t < 1 / s) :
    gumbelComplexMGF m s t = mgf id (gumbelMeasure m s) t := by
  rw [mgf_id_gumbelMeasure hs ht, gumbelComplexMGF]
  have hexp : Complex.exp ((m : ℂ) * t) = (Real.exp (m * t) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  have hGamma : Complex.Gamma (1 - (s : ℂ) * t) = (Real.Gamma (1 - s * t) : ℂ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul] using
      (Complex.Gamma_ofReal (1 - s * t))
  rw [hexp, hGamma]
  norm_cast

/-- The characteristic function of a positive-scale Gumbel law. -/
@[simp]
theorem charFun_gumbelMeasure (hs : 0 < s) (t : ℝ) :
    charFun (gumbelMeasure m s) t =
      Complex.exp (Complex.I * m * t) * Complex.Gamma (1 - Complex.I * s * t) := by
  have hsub : Iio (1 / s) ⊆ integrableExpSet id (gumbelMeasure m s) := by
    rw [integrableExpSet_id_gumbelMeasure hs]
  have hEq : Set.EqOn (complexMGF id (gumbelMeasure m s)) (gumbelComplexMGF m s)
      {z : ℂ | z.re < 1 / s} :=
    TauCeti.eqOn_complexMGF_of_eqOn_mgf isOpen_Iio (convex_Iio _) hsub
      (analyticOnNhd_gumbelComplexMGF hs) fun _ ht ↦ gumbelComplexMGF_ofReal hs ht
  have hzero : (0 : ℝ) < 1 / s := one_div_pos.mpr hs
  have hit : ((t : ℂ) * Complex.I) ∈ {z : ℂ | z.re < 1 / s} := by
    simpa using hzero
  have h := hEq hit
  rw [complexMGF_id_mul_I] at h
  rw [h]
  unfold gumbelComplexMGF
  congr 1 <;> ring_nf

end TauCeti.Probability
