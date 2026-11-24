/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Linearization
public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic

/-!
# The derivative of a Hamiltonian vector field is the Hessian

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `ω(·, J ·)` of a
linear compatible almost complex structure `J`. Then `J X_H = ∇H`
(`TauCeti.SymplecticForm.apply_hamiltonianVectorField_eq_gradient`), and differentiating gives
`J dX_H(x) = d(∇H)(x)`, the Hessian operator `TauCeti.hessianOperator H x` of `H`
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianVectorField_eq_hessianOperator`).

This identifies the zeroth-order term `J dX_H(γ)` of the linearized Floer operator along a
time-independent cylinder `(s, t) ↦ γ(s)` with the Hessian term of the linearized gradient equation
`ζ' = d(∇H)(γ) ζ` along the gradient line `γ`.
-/

public section

open scoped Gradient RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- **`J dX_H` is the Hessian of `H`.** If the inner product of `V` is the metric `ω(·, J ·)`, then
`J dX_H(x)` is the Hessian operator `d(∇H)(x)` of `H` at `x`. No regularity is needed: both sides
use Mathlib's totalized derivatives. -/
theorem apply_fderiv_hamiltonianVectorField_eq_hessianOperator (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (H : V → ℝ) (x v : V) :
    J (fderiv ℝ (ω.hamiltonianVectorField H) x v) = hessianOperator H x v := by
  have h : ∇ H = J.linearEquiv.toContinuousLinearEquiv ∘ ω.hamiltonianVectorField H := by
    ext y
    simp [AlmostComplexStructure.linearEquiv_apply, apply_hamiltonianVectorField_eq_gradient hg]
  rw [← fderiv_gradient, h, ContinuousLinearEquiv.comp_fderiv]
  simp [AlmostComplexStructure.linearEquiv_apply]

end TauCeti.SymplecticForm
