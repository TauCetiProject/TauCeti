/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Weak continuity of beta laws

The beta law varies jointly weakly continuously with its two positive shape parameters.
The statement uses `ProbabilityMeasure ℝ`, with its topology of weak convergence.

The densities can be unbounded at either endpoint. Locally in parameter space, the beta
kernel is bounded by the integrable kernel with both shapes halved. Dominated convergence
for bounded continuous test functions and continuity of the Gamma normalizer then give
continuity of the laws.

The proof uses Mathlib's bounded-continuous-test-function characterization of weak
convergence and Tau Ceti's real beta integral. For the classical beta density, see
Johnson, Kotz, and Balakrishnan, *Continuous Univariate Distributions*, volume 2, Chapter 25.
-/

public section

open BoundedContinuousFunction Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- Beta laws depend jointly weakly continuously on their positive shape parameters. -/
theorem continuous_betaMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) ↦
      (⟨betaMeasure p.1 p.2,
        isProbabilityMeasureBeta (mem_Ioi.mp p.1.2) (mem_Ioi.mp p.2.2)⟩ :
          ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.2
  intro f
  simp only [ProbabilityMeasure.coe_mk,
    fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) ↦ integral_betaMeasure_eq_one_div_beta_smul p.1.2 p.2.2 f,
    smul_eq_mul]
  exact continuous_one_div_beta.mul (f.continuous_integral_rpow_mul_one_sub_rpow_mul)

end TauCeti.Probability
