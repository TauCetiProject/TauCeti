/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Multiplication of tempered distributions by functions of temperate growth

Mathlib's `TemperedDistribution.smulLeftCLM F g` multiplies a tempered distribution by a function
`g` of temperate growth, through its action `u ↦ g • u` on test functions. This file records that
on the tempered distribution of a Schwartz function `f`, taken against any measure of temperate
growth, it is the tempered distribution of the pointwise product `g • f`, so that it extends
Mathlib's `SchwartzMap.smulLeftCLM`. Mathlib proves the corresponding statement for `g` of
temperate growth lying in `Lᵖ`, acting on `L^q` functions with Hölder exponents
(`MeasureTheory.Lp.toTemperedDistribution_smul_eq`).

Directional derivatives satisfy the Leibniz rule `∂_v (g u) = (∂_v g) u + g ∂_v u`, by duality
from the Leibniz rule on Schwartz functions. This is how multiplication by smooth functions with
bounded derivatives is shown to preserve the Sobolev spaces of integer order.

## Main results

* `TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq`: multiplication by `g` on
  tempered distributions extends multiplication by `g` on Schwartz functions.
* `TemperedDistribution.lineDerivOp_smulLeftCLM`: the Leibniz rule.
-/

public section

namespace TemperedDistribution

open MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Multiplication by a function of temperate growth on tempered distributions extends the
pointwise multiplication of Schwartz functions, for the embedding of Schwartz functions against
any measure of temperate growth. -/
theorem smulLeftCLM_toTemperedDistributionCLM_eq {μ : Measure E} [μ.HasTemperateGrowth]
    {g : E → ℂ} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F g (SchwartzMap.toTemperedDistributionCLM E F μ f) =
      SchwartzMap.toTemperedDistributionCLM E F μ (SchwartzMap.smulLeftCLM F g f) := by
  ext u
  simp only [smulLeftCLM_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, smul_smul, smul_eq_mul, mul_comm]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- **The Leibniz rule for multiplication of tempered distributions by a function of temperate
growth**: `∂_v (g u) = (∂_v g) u + g ∂_v u`. -/
theorem lineDerivOp_smulLeftCLM {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢'(E, F)) (v : E) :
    ∂_{v} (smulLeftCLM F g u) =
      smulLeftCLM F (fun x ↦ fderiv ℝ g x v) u + smulLeftCLM F g (∂_{v} u) := by
  ext φ
  simp [smulLeftCLM_apply_apply, SchwartzMap.lineDerivOp_smulLeftCLM hg]

end TemperedDistribution
