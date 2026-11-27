/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential of the complex structure of a complex normed space

On a finite-dimensional complex normed space `F`, the almost complex structure
`TauCeti.AlmostComplexStructure.ofComplexModule F` is multiplication by `i`. Its real multiples
exponentiate, in the algebra `F →L[ℝ] F` of real-linear maps, to multiplication by unit complex
numbers: `exp (θ i) = e^{iθ}` (`TauCeti.AlmostComplexStructure.exp_smul_ofComplexModule`). In
particular `exp (-π i) = -1` (`TauCeti.AlmostComplexStructure.exp_neg_pi_smul_ofComplexModule`),
the return map of the linear Hamiltonian flow `y' = -π i y` over one period.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open ContinuousLinearMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The exponential of a real multiple of `i`.** In the algebra of real-linear maps of a
finite-dimensional complex normed space, `exp (θ i)` is multiplication by `e^{iθ}`. -/
theorem exp_smul_ofComplexModule (θ : ℝ) :
    NormedSpace.exp (θ • (ofComplexModule F).toLinearMap.toContinuousLinearMap) =
      lsmul ℝ ℂ (Complex.exp (θ * Complex.I)) := by
  -- Multiplication by complex scalars is a continuous ring homomorphism, so it commutes with `exp`.
  let ψ : ℂ →+* (F →L[ℝ] F) :=
    { toFun := fun z ↦ lsmul ℝ ℂ z
      map_one' := by ext; simp
      map_mul' := fun z w ↦ by ext; simp [mul_smul]
      map_zero' := by ext; simp
      map_add' := fun z w ↦ by ext; simp }
  have hψ : Continuous ψ := (lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).continuous
  have hx : (θ : ℂ) * Complex.I ∈ Metric.eball (0 : ℂ) (NormedSpace.expSeries ℝ ℂ).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hψx : ψ ((θ : ℂ) * Complex.I) =
      θ • (ofComplexModule F).toLinearMap.toContinuousLinearMap := by
    ext v
    simp [ψ, ofComplexModule_apply, mul_smul, Complex.coe_smul]
  rw [← hψx, ← NormedSpace.map_exp_of_mem_ball ψ hψ _ hx, ← Complex.exp_eq_exp_ℂ]
  rfl

/-- In the algebra of real-linear maps of a finite-dimensional complex normed space,
`exp (-π i) = -1`. -/
theorem exp_neg_pi_smul_ofComplexModule :
    NormedSpace.exp (-Real.pi • (ofComplexModule F).toLinearMap.toContinuousLinearMap) = -1 := by
  rw [exp_smul_ofComplexModule, Complex.ofReal_neg, neg_mul, Complex.exp_neg,
    Complex.exp_pi_mul_I, inv_neg, inv_one, map_neg]
  ext v
  simp

end TauCeti.AlmostComplexStructure
