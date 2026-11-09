/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Multiplication of tempered distributions by functions of temperate growth

Mathlib's `TemperedDistribution.smulLeftCLM F g` multiplies a tempered distribution by a function
`g` of temperate growth, through its action `u ↦ g • u` on test functions. This file records that
on the tempered distribution of a Schwartz function `f`, taken against any measure of temperate
growth, it is the tempered distribution of the pointwise product `g • f`, so that it extends
Mathlib's `SchwartzMap.smulLeftCLM`. Mathlib proves the corresponding statement for `g` of
temperate growth lying in `Lᵖ`, acting on `L^q` functions with Hölder exponents
(`MeasureTheory.Lp.toTemperedDistribution_smul_eq`).

Directional derivatives of such products obey the Leibniz rule
`∂_v (g f) = (∂_v g) f + g ∂_v f`, where `∂_v g` is the classical derivative `x ↦ Dg(x) v`, again
a function of temperate growth. By duality this is the Leibniz rule for Schwartz functions
(`SchwartzMap.lineDerivOp_smulLeftCLM`).

## Main results

* `TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq`: multiplication by `g` on
  tempered distributions extends multiplication by `g` on Schwartz functions.
* `TemperedDistribution.lineDerivOp_smulLeftCLM`: the Leibniz rule for the product of a tempered
  distribution with a function of temperate growth.
-/

public section

namespace TemperedDistribution

open MeasureTheory
open scoped SchwartzMap LineDeriv

section Deriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- **The Leibniz rule for tempered distributions**: for `g` of temperate growth,
`∂_v (g f) = (∂_v g) f + g ∂_v f`, where `∂_v g` is the classical derivative `x ↦ Dg(x) v`. -/
theorem lineDerivOp_smulLeftCLM {g : E → ℂ} (hg : g.HasTemperateGrowth) (f : 𝓢'(E, F)) (v : E) :
    ∂_{v} (smulLeftCLM F g f) =
      smulLeftCLM F (fun x ↦ fderiv ℝ g x v) f + smulLeftCLM F g (∂_{v} f) := by
  ext u
  simp [SchwartzMap.lineDerivOp_smulLeftCLM hg, ← map_add]

end Deriv

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

end TemperedDistribution
