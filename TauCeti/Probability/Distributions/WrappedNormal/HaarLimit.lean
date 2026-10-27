/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.WrappedNormal.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier

/-!
# The Haar limit of wrapped normal laws

As the Gaussian variance tends to infinity, its wrapped law tends weakly to Haar probability
on the circle. The nonconstant Fourier moments decay as `exp (-v * n² / 2)`.
Together with the zero-variance Dirac limit, this describes both variance boundaries.

## References

* K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley, 2000, section 3.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Wrapped normal laws tend weakly to Haar probability as the variance tends to infinity. -/
theorem tendsto_wrappedNormalMeasure_atTop_haar (m : AddCircle (2 * π)) :
    Tendsto (fun v : ℝ≥0 ↦ (wrappedNormalMeasure m v).toProbabilityMeasure) atTop
      (𝓝 (@AddCircle.haarAddCircle (2 * π) ⟨two_pi_pos⟩).toProbabilityMeasure) := by
  let : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  apply ProbabilityMeasure.tendsto_haarAddCircle_iff.2
  intro n hn
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hscale : Tendsto (fun v : ℝ≥0 ↦ (v : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hexp := tendsto_exp_neg_atTop_nhds_zero.comp
    (hscale.atTop_mul_const (div_pos (sq_pos_of_ne_zero hnR) two_pos))
  have hcomplex := (Complex.continuous_ofReal.tendsto 0).comp hexp
  simpa only [Measure.coe_toProbabilityMeasure, integral_fourier_wrappedNormalMeasure,
    Complex.ofReal_zero, mul_zero, Function.comp_def, neg_mul, neg_div, mul_div_assoc] using
    hcomplex.const_mul (fourier n m)

end TauCeti.Probability
