/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.WrappedCauchy.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier

/-!
# The Haar limit of wrapped Cauchy laws

As the Cauchy scale tends to infinity, its wrapped law tends weakly to Haar probability on
the circle. Every nonconstant Fourier moment tends to zero, since its modulus is
`exp (-γ * |n|)`. This complements the Dirac limit at scale zero.

## References

* K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley, 2000, section 3.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real TauCeti.Probability Topology
open scoped NNReal

namespace AddCircle

/-- Wrapped Cauchy laws tend weakly to Haar probability as the scale tends to infinity. -/
theorem tendsto_wrappedCauchyMeasure_atTop_haar (m : AddCircle (2 * π)) :
    Tendsto (fun γ : ℝ≥0 ↦ (wrappedCauchyMeasure m γ).toProbabilityMeasure) atTop
      (𝓝 (@AddCircle.haarAddCircle (2 * π) ⟨two_pi_pos⟩).toProbabilityMeasure) := by
  let : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  apply ProbabilityMeasure.tendsto_haarAddCircle_iff.2
  intro n hn
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hscale : Tendsto (fun γ : ℝ≥0 ↦ (γ : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hexp := tendsto_exp_neg_atTop_nhds_zero.comp
    (hscale.atTop_mul_const (abs_pos.mpr hnR))
  have hcomplex := (Complex.continuous_ofReal.tendsto 0).comp hexp
  simpa only [Measure.coe_toProbabilityMeasure, integral_fourier_wrappedCauchyMeasure,
    Complex.ofReal_zero, mul_zero, Function.comp_def] using hcomplex.const_mul (fourier n m)

end AddCircle
