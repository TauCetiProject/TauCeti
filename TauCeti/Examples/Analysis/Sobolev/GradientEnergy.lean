/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.HessianEnergy

/-!
# The solenoidal gradient-energy identity fails for gradient fields

The solenoidal identity `‖∇u‖²_{L²} = ½ ‖∇u - (∇u)†‖²_{L²}` of
`TauCeti.IsSolenoidalOn.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint` needs `div u = 0`. For the
gradient field `u = ∇φ` of a compactly supported `C²` function `φ`, whose derivative is the
Hessian `D²φ`:

* `integral_sq_hilbertSchmidtNorm_hessianOperator_sub_adjoint_div_two_eq_zero`: the right side
  `½ ‖D²φ - (D²φ)†‖²_{L²}` is zero, by `ContDiffAt.hessianOperator_sub_adjoint`;
* the left side is `‖D²φ‖²_{L²} = ‖Δφ‖²_{L²}`, by
  `TauCeti.integral_sq_hilbertSchmidtNorm_hessianOperator_eq_integral_trace_sq`.

When `E` has positive dimension the left side is positive for every nonzero such `φ`, since a
compactly supported harmonic function vanishes; that positivity is not formalized here.
-/

public section

open MeasureTheory ContinuousLinearMap

namespace TauCeti.Examples.GradientEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {φ : E → ℝ}

/-- For a gradient field `u = ∇φ`, the right side `½ ‖∇u - (∇u)†‖²_{L²}` of the solenoidal
gradient-energy identity is zero, because the Hessian `∇u = D²φ` is self-adjoint. -/
theorem integral_sq_hilbertSchmidtNorm_hessianOperator_sub_adjoint_div_two_eq_zero
    (μ : Measure E) (hφ : ContDiff ℝ 2 φ) :
    (∫ x, (hessianOperator φ x - adjoint (hessianOperator φ x)).hilbertSchmidtNorm ^ 2 ∂μ) / 2 =
      0 := by
  simp [fun x ↦ (hφ.contDiffAt (x := x)).hessianOperator_sub_adjoint]

end TauCeti.Examples.GradientEnergy
