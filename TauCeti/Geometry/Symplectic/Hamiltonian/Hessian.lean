/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Linearization
public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The derivative of a Hamiltonian vector field is the Hessian

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `ω(·, J ·)` of a
linear compatible almost complex structure `J`. Then `J X_H = ∇H`
(`TauCeti.SymplecticForm.apply_hamiltonianVectorField_eq_gradient`), and differentiating gives
`J dX_H(x) = d(∇H)(x)`, the Hessian operator `TauCeti.hessianOperator H x` of `H`
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianVectorField_eq_hessianOperator`); equivalently
`-J dX_H(x)` is the Hessian operator of `-H`
(`TauCeti.SymplecticForm.neg_comp_fderiv_hamiltonianVectorField_eq_hessianOperator_neg`).

For the squared norm, `X_H` is the linear field `y ↦ -2 J y`
(`TauCeti.SymplecticForm.hamiltonianVectorField_norm_sq`), whose derivative `-2 J` is constant;
for its multiple `a ‖y‖²`, `X_H` is `y ↦ -2 a J y`
(`TauCeti.SymplecticForm.hamiltonianVectorField_mul_norm_sq`).

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

/-- **`-J dX_H` is the Hessian of `-H`.** If the inner product of `V` is the metric `ω(·, J ·)`,
then `-J dX_H(x)` is the Hessian operator of `-H` at `x`: this is
`TauCeti.SymplecticForm.apply_fderiv_hamiltonianVectorField_eq_hessianOperator` combined with
`TauCeti.hessianOperator_neg`. It identifies the zeroth-order term of the Morse operator of `-H`,
whose negative gradient lines are the time-independent Floer solutions of `H`. -/
theorem neg_comp_fderiv_hamiltonianVectorField_eq_hessianOperator_neg
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (H : V → ℝ) (x : V) :
    -(J.toLinearMap.toContinuousLinearMap ∘L fderiv ℝ (ω.hamiltonianVectorField H) x) =
      hessianOperator (-H) x := by
  ext v
  simp [apply_fderiv_hamiltonianVectorField_eq_hessianOperator hg]

/-- **The Hamiltonian vector field of the squared norm.** If the inner product of `V` is the metric
`ω(·, J ·)`, the Hamiltonian vector field of `y ↦ ‖y‖²` is the linear field `y ↦ -2 J y`. -/
theorem hamiltonianVectorField_norm_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) :
    ω.hamiltonianVectorField (fun y ↦ ‖y‖ ^ 2) =
      ⇑((-2 : ℝ) • J.toLinearMap.toContinuousLinearMap) := by
  funext y
  symm
  rw [eq_hamiltonianVectorField_iff, (hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv]
  intro v
  have h : ω ((-2 : ℝ) • J y) v = -2 * ω (J y) v := LinearMap.map_smul₂ ω.toBilinForm _ _ _
  rw [_root_.smul_apply, LinearMap.coe_toContinuousLinearMap', h, ← ω.neg_eq, hg, real_inner_comm]
  simp only [_root_.smul_apply, innerSL_apply_apply, nsmul_eq_mul]
  push_cast
  ring

/-- **The Hamiltonian vector field of a quadratic Hamiltonian.** If the inner product of `V` is
the metric `ω(·, J ·)`, the Hamiltonian vector field of `y ↦ a ‖y‖²` is the linear field
`y ↦ -2 a J y`. -/
theorem hamiltonianVectorField_mul_norm_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (a : ℝ) :
    ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) = fun y ↦ (-2 * a) • J y := by
  funext y
  rw [hamiltonianVectorField_const_mul, hamiltonianVectorField_norm_sq hg]
  simp [smul_smul, mul_comm]

end TauCeti.SymplecticForm
