/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Levy.Transforms
public import TauCeti.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.RCLike.Sqrt
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Levy.Moments
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Characteristic function of the Lévy distribution

The Lévy law with location `m` and positive scale `c` has characteristic function
`exp (I * m * t - sqrt (-2 * I * c * t))`, with the principal complex square root.
This connects the inverse-gamma construction of the law to stable characteristic exponents.

The analytic-continuation argument follows the inverse Gaussian development in
`TauCeti.Probability.Distributions.InverseGaussian.CharFun`. Here the imaginary axis is a
boundary of the exponential-integrability domain, so continuity on the closed left
half-plane is also needed.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

private theorem complexMGF_levyMeasure_zero_one {z : ℂ} (hz : z.re ≤ 0) :
    complexMGF id (levyMeasure 0 1) z = Complex.exp (-Complex.sqrt (-2 * z)) := by
  let _ := isProbabilityMeasure_levyMeasure one_pos 0
  have han : AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.exp (-Complex.sqrt (-2 * z)))
      {z : ℂ | z.re < 0} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_Iio.preimage Complex.continuous_re)
    intro z hz
    have hslit : -2 * z ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simpa using (mul_pos_of_neg_of_neg (by norm_num : (-2 : ℝ) < 0) hz)
    fun_prop (disch := assumption)
  have hEq := eqOn_complexMGF_of_eqOn_mgf isOpen_Iio (convex_Iio (0 : ℝ))
    (fun t ht ↦ by rw [integrableExpSet_id_levyMeasure one_pos 0]; exact ht.le) han
    (fun t ht ↦ by
      rw [mgf_id_levyMeasure one_pos 0 ht.le]
      have harg : (-2 : ℂ) * t = ((-2 * t : ℝ) : ℂ) := by push_cast; ring
      rw [harg, Complex.sqrt_of_nonneg
        (Complex.zero_le_real.mpr (mul_nonneg_of_nonpos_of_nonpos (by norm_num) ht.le))]
      simp)
  have hcont : ContinuousOn (fun z : ℂ ↦ Complex.exp (-Complex.sqrt (-2 * z)))
      {z : ℂ | z.re ≤ 0} := by
    intro z hz
    have hsqrt : ContinuousAt Complex.sqrt (-2 * z) :=
      Complex.continuousAt_sqrt (Or.inl (by simpa using
        (mul_nonneg_of_nonpos_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0) hz)))
    exact (Complex.continuous_exp.continuousAt.comp
      (hsqrt.comp (by fun_prop)).neg).continuousWithinAt
  apply hEq.of_subset_closure
    (TauCeti.continuousOn_complexMGF_of_nonneg measurable_id.aemeasurable
      ((ae_lt_levyMeasure 0 1).mono fun _ hx ↦ hx.le)) hcont (fun _ h ↦ h.le) ?_ hz
  simp only [mem_Iio, Complex.closure_setOfPred_re_lt]
  exact Subset.rfl

/-- The characteristic function of a Lévy law with positive scale. The square root is
principal, and its argument is purely imaginary. -/
@[simp]
theorem charFun_levyMeasure {c : ℝ} (hc : 0 < c) (m t : ℝ) :
    charFun (levyMeasure m c) t =
      Complex.exp ((m * t : ℝ) * Complex.I -
        Complex.sqrt (-2 * Complex.I * (c : ℂ) * t)) := by
  rw [levyMeasure_eq_map_affine_levyMeasure_zero_one hc, charFun_map_affine,
    ← complexMGF_id_mul_I, complexMGF_levyMeasure_zero_one (by simp), ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

end TauCeti.Probability
