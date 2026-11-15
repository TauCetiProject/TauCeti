/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.DiscreteGaussian.Transforms
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Moments of the discrete Gaussian

Every natural moment of an integer Gaussian is absolutely integrable. Its moments are
normalized polynomially weighted Gaussian lattice sums. Differentiating the logarithm of
the normalizer gives the corrections to the mean and variance: the center and squared width
are generally different from those two moments. When twice the center is an integer,
reflection about the center forces the mean to equal the center.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  2020, arXiv:2004.00010.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- Every natural power of the signed count is integrable, also at invalid widths. -/
theorem integrable_pow_intCast_discreteGaussianMeasure (c s : ℝ) (n : ℕ) :
    Integrable (fun k : ℤ => (k : ℝ) ^ n) (discreteGaussianMeasure c s) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := (Int.cast : ℤ → ℝ)) _ n
  simp

/-- Natural moments are normalized polynomially weighted lattice sums. -/
theorem integral_pow_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫ k : ℤ, (k : ℝ) ^ n ∂discreteGaussianMeasure c s =
      (∑' k : ℤ, (k : ℝ) ^ n * exp (-((k : ℝ) - c) ^ 2 / (2 * s ^ 2))) /
        gaussianLatticeSum c s := by
  rw [integral_countable (integrable_pow_intCast_discreteGaussianMeasure c s n),
    ← tsum_div_const]
  congr 1
  ext k
  rw [discreteGaussianMeasure_real_singleton c hs, discreteGaussianWeightReal_def]
  simp only [smul_eq_mul]
  ring

private theorem hasDerivAt_cgf_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ}
    (hs : 0 < s) (t : ℝ) :
    HasDerivAt (cgf (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s))
      (c + s ^ 2 * t + s ^ 2 * deriv (fun x => log (gaussianLatticeSum x s))
        (c + s ^ 2 * t)) t := by
  have hf : Differentiable ℝ (fun x => log (gaussianLatticeSum x s)) :=
    ((contDiff_gaussianLatticeSum s : ContDiff ℝ 1 _).log
      (fun x => (gaussianLatticeSum_pos x hs.ne').ne')).differentiable (by norm_num)
  have harg := ((hasDerivAt_id t).const_mul (s ^ 2)).const_add c
  have hlog := (hf (c + s ^ 2 * t)).hasDerivAt.comp t harg
  have hquad := (((hasDerivAt_id t).pow 2).const_mul (s ^ 2)).div_const 2
  have h := ((((hasDerivAt_id t).const_mul c).add hquad).add hlog).sub_const
    (log (gaussianLatticeSum c s))
  convert h using 1
  · exact funext fun u => cgf_intCast_discreteGaussianMeasure c hs u
  · simp only [id_eq, Nat.cast_ofNat]
    ring

/-- The mean equals the center plus the logarithmic lattice correction. -/
theorem integral_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ k : ℤ, (k : ℝ) ∂discreteGaussianMeasure c s =
      c + s ^ 2 * deriv (fun x => log (gaussianLatticeSum x s)) c := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  have h := (hasDerivAt_cgf_intCast_discreteGaussianMeasure c hs 0).deriv
  have hzero : 0 ∈ interior
      (integrableExpSet (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s)) := by simp
  simpa [deriv_cgf_zero hzero] using h

/-- The variance equals the squared width plus its second logarithmic lattice correction. -/
theorem variance_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) :
    variance (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s) =
      s ^ 2 + s ^ 4 * deriv (deriv (fun x => log (gaussianLatticeSum x s))) c := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  have hf : ContDiff ℝ 2 (fun x => log (gaussianLatticeSum x s)) :=
    (contDiff_gaussianLatticeSum s).log (fun x => (gaussianLatticeSum_pos x hs.ne').ne')
  have hD : deriv (cgf (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s)) =
      fun t => c + s ^ 2 * t + s ^ 2 *
        deriv (fun x => log (gaussianLatticeSum x s)) (c + s ^ 2 * t) :=
    funext fun t => (hasDerivAt_cgf_intCast_discreteGaussianMeasure c hs t).deriv
  have harg := ((hasDerivAt_id (0 : ℝ)).const_mul (s ^ 2)).const_add c
  have hlog := (hf.differentiable_deriv_two (c + s ^ 2 * (0 : ℝ))).hasDerivAt.comp 0 harg
  have hsecond : deriv (deriv (cgf (Int.cast : ℤ → ℝ)
      (discreteGaussianMeasure c s))) 0 =
        s ^ 2 + s ^ 4 * deriv (deriv (fun x => log (gaussianLatticeSum x s))) c := by
    rw [hD]
    have h := ((hasDerivAt_const 0 c).add ((hasDerivAt_id 0).const_mul (s ^ 2))).add
      (hlog.const_mul (s ^ 2))
    have h' : HasDerivAt (fun t : ℝ => c + s ^ 2 * t + s ^ 2 *
        deriv (fun x => log (gaussianLatticeSum x s)) (c + s ^ 2 * t))
        (s ^ 2 + s ^ 4 * deriv (deriv (fun x => log (gaussianLatticeSum x s))) c) 0 := by
      convert h using 1
      · ext t
        simp
      · simp
        ring
    exact h'.deriv
  have hzero : 0 ∈ interior
      (integrableExpSet (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s)) := by simp
  have hvariance := iteratedDeriv_two_cgf hzero
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hvariance
  have hL2 : MemLp (Int.cast : ℤ → ℝ) 2 (discreteGaussianMeasure c s) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (integrable_pow_intCast_discreteGaussianMeasure c s 2)
  rw [variance_eq_sub hL2]
  simpa [deriv_cgf_zero hzero] using hvariance.symm.trans hsecond

/-- An integer or half-integer center is the mean. -/
theorem integral_intCast_discreteGaussianMeasure_of_two_mul_eq_intCast (c : ℝ) {s : ℝ}
    (hs : 0 < s) {m : ℤ} (hm : 2 * c = m) :
    ∫ k : ℤ, (k : ℝ) ∂discreteGaussianMeasure c s = c := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  have hc : -c + m = c := by linarith
  have hmap : (discreteGaussianMeasure c s).map (fun k => -k + m) =
      discreteGaussianMeasure c s := by
    have hcomp := Measure.map_map (μ := discreteGaussianMeasure c s)
      (g := fun k : ℤ => k + m) (f := Neg.neg) (by fun_prop) (by fun_prop)
    simpa [Function.comp_def, map_neg_discreteGaussianMeasure,
      map_add_const_discreteGaussianMeasure, hc] using hcomp.symm
  have h := congrArg (fun μ : Measure ℤ => ∫ k : ℤ, (k : ℝ) ∂μ) hmap
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  simp only [Int.cast_add, Int.cast_neg] at h
  rw [integral_add (by
      simpa using (integrable_pow_intCast_discreteGaussianMeasure c s 1).neg)
    (integrable_const _), integral_neg] at h
  simp at h
  linarith

end TauCeti.Probability
