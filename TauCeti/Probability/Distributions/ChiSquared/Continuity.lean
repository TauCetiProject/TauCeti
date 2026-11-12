/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Weak continuity of chi-squared laws

The chi-squared law varies weakly continuously with its nonnegative real degree.
In particular, the positive-degree laws converge to the Dirac mass at zero as the
degree tends to zero. This continuity concerns the topology of `ProbabilityMeasure ℝ`;
the limiting Dirac law has no density with respect to volume.

The formula `charFun_chiSquaredMeasure` holds even at degree zero, where its exponent
vanishes. Mathlib's Lévy convergence theorem,
`ProbabilityMeasure.tendsto_of_tendsto_charFun`, therefore treats this boundary together
with the positive degrees.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Chi-squared laws depend weakly continuously on the nonnegative degree, including
the Dirac law at degree zero. -/
theorem continuous_chiSquaredMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun k : ℝ≥0 ↦
      (⟨chiSquaredMeasure k,
        isProbabilityMeasure_chiSquaredMeasure k.coe_nonneg⟩ : ProbabilityMeasure ℝ)) := by
  apply continuous_iff_seqContinuous.2
  intro k a hk
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    (μ := fun n ↦ ⟨chiSquaredMeasure (k n),
      isProbabilityMeasure_chiSquaredMeasure (k n).coe_nonneg⟩)
  intro t
  simp only [ProbabilityMeasure.coe_mk, charFun_chiSquaredMeasure (k _).coe_nonneg,
    charFun_chiSquaredMeasure a.coe_nonneg]
  have hdeg : Tendsto (fun n ↦ ((k n : ℝ) : ℂ)) atTop (𝓝 ((a : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.tendsto a |>.comp hk)
  refine (hdeg.neg.div_const 2).const_cpow (Or.inl ?_)
  intro h
  have hre : (1 - 2 * Complex.I * (t : ℂ)).re = 1 := by simp
  simp [h] at hre

end TauCeti.Probability
