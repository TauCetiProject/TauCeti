/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
public import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication

/-!
# Smooth multiples of test functions in `Lᵖ`

Let `φ` be a bounded `C^n` real function on a real normed space `E`, and let `ν` be a measure on
`E` that is finite on compact sets and inner regular. The class in `Lᵖ(ν)` of the test function
`φ η` is the multiplication operator `BoundedContinuousFunction.smulLp` by `φ` applied to the class
of `η` (`TestFunction.ambientToLp_smulLeftCLM`). Weighted energy estimates use this to pass
multiplier identities for test functions to their `Lᵖ` limits.
-/

public section

open MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BoundedContinuousFunction

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {ν : Measure E} [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]

/-- The `Lᵖ` class of a smooth multiple `φ η` of a test function is the multiplication operator by
`φ` applied to the class of `η`. -/
theorem ambientToLp_smulLeftCLM (hp : p ≠ ∞) (φ : E →ᵇ ℝ) (hφ : ContDiff ℝ n φ)
    (η : 𝓓^{n}(Ω, F)) :
    ambientToLp p ν (smulLeftCLM hφ η) = φ.smulLp ν p hp (ambientToLp p ν η) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ambientToLp (p := p) (ν := ν) (smulLeftCLM hφ η),
    BoundedContinuousFunction.coeFn_smulLp hp φ (ambientToLp p ν η),
    coeFn_ambientToLp (p := p) (ν := ν) η] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃, smulLeftCLM_apply]

end TestFunction
