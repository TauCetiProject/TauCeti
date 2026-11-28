/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.GradientEnergy
public import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Calculus.Gradient

/-!
# The gradient energy of a gradient field

For the gradient field `u = ∇φ` of a compactly supported `C²` function `φ`, the derivative
`∇u = D²φ` is the Hessian, which is self-adjoint. Its antisymmetric part vanishes, so the
gradient-energy identity `‖∇u‖²_{L²} = ½ ‖∇u - (∇u)†‖²_{L²} + ‖div u‖²_{L²}` of
`TauCeti.HasWeakFDerivOn.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint_add_trace_sq` puts all of
the energy into the divergence `div u = Δφ`:

* `hessianOperator_sub_adjoint`: `D²φ - (D²φ)† = 0`, so the
  vorticity term `½ ‖∇u - (∇u)†‖²_{L²}` is zero;
* `integral_sq_hilbertSchmidtNorm_hessianOperator_eq_integral_trace_sq`:
  the classical `L²` identity `∫ ‖D²φ‖_HS² = ∫ (Δφ)²`.

So the solenoidal identity `‖∇u‖²_{L²} = ½ ‖∇u - (∇u)†‖²_{L²}` of
`TauCeti.IsSolenoidalOn.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint` needs `div u = 0`: for a
gradient field its right side is zero, while its left side is `‖D²φ‖²_{L²} = ‖Δφ‖²_{L²}`, which
is positive for every nonzero `φ`.
-/

public section

open MeasureTheory ContinuousLinearMap
open scoped Gradient

namespace TauCeti.Examples.GradientEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E → ℝ}

/-- The Hessian of a `C²` function has no antisymmetric part: `D²φ - (D²φ)† = 0`. -/
theorem hessianOperator_sub_adjoint (hφ : ContDiff ℝ 2 φ) (x : E) :
    hessianOperator φ x - adjoint (hessianOperator φ x) = 0 := by
  rw [(hφ.contDiffAt.isSelfAdjoint_hessianOperator).adjoint_eq, sub_self]

variable [MeasurableSpace E] [BorelSpace E]

/-- **The `L²` norm of the Hessian is the `L²` norm of the Laplacian.** For a compactly supported
`C²` function `φ`, `∫ ‖D²φ‖_HS² = ∫ (Δφ)²`, where `Δφ = tr D²φ`. -/
theorem integral_sq_hilbertSchmidtNorm_hessianOperator_eq_integral_trace_sq (μ : Measure E)
    [μ.IsAddHaarMeasure] (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ x, (hessianOperator φ x).hilbertSchmidtNorm ^ 2 ∂μ =
      ∫ x, LinearMap.trace ℝ E (hessianOperator φ x).toLinearMap ^ 2 ∂μ := by
  have hgrad : ContDiff ℝ 1 (∇ φ) := hφ.gradient_right (by norm_num)
  have hH : HasCompactSupport (hessianOperator φ) := by
    simpa only [← funext (fderiv_gradient φ)] using hc.gradient.fderiv (𝕜 := ℝ)
  have hweak : HasWeakFDerivOn μ ⊤ (∇ φ) (hessianOperator φ) := by
    simpa only [← funext (fderiv_gradient φ)] using hgrad.contDiffOn.hasWeakFDerivOn_fderiv
  rw [hweak.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint_add_trace_sq
    (hc.memLp_gradient (hφ.of_le (by norm_num)))
    ((hφ.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.memLp_of_hasCompactSupport
      hH)]
  simp [hessianOperator_sub_adjoint hφ]

end TauCeti.Examples.GradientEnergy
