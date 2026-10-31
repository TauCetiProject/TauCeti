/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Hamilton's equations on `V × V`

Let `V` be a finite-dimensional real inner product space, and give the phase space `V × V` of
positions `q` and momenta `p` its standard symplectic form
`ω₀((q₁, p₁), (q₂, p₂)) = ⟪q₁, p₂⟫ - ⟪p₁, q₂⟫`, that is `ω₀ = Σ dqᵢ ∧ dpᵢ`.

If a Hamiltonian `H` has derivative `(δq, δp) ↦ ⟪a, δq⟫ + ⟪b, δp⟫` at a point, so that `a` and
`b` are its partial gradients `∇_q H` and `∇_p H`, then its Hamiltonian vector field there is
`(b, -a)`. These are Hamilton's equations `q' = ∇_p H`, `p' = -∇_q H`
(`TauCeti.stdSymplecticForm_hamiltonianVectorField`). In particular, a Hamiltonian
`H(q, p) = h(q)` depending only on position has `X_H(q, p) = (0, -∇h(q))`
(`TauCeti.stdSymplecticForm_hamiltonianVectorField_comp_fst`). Consequently the Poisson bracket
is given by the classical formula `{F, G} = ⟪∇_q F, ∇_p G⟫ - ⟪∇_p F, ∇_q G⟫`
(`TauCeti.stdSymplecticForm_poissonBracket`).

See V. I. Arnold, *Mathematical Methods of Classical Mechanics*, Sections 15 and 40.
-/

public section

namespace TauCeti

open scoped InnerProductSpace Gradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamilton's equations.** If `H` has partial gradients `∇_q H = a` and `∇_p H = b` at `x`,
then its Hamiltonian vector field at `x` is `(b, -a)`. -/
theorem stdSymplecticForm_hamiltonianVectorField {H : V × V → ℝ} {x : V × V} {a b : V}
    (hH : HasFDerivAt H ((innerSL ℝ a).coprod (innerSL ℝ b)) x) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField H x = (b, -a) := by
  rw [eq_comm, SymplecticForm.eq_hamiltonianVectorField_iff, hH.fderiv]
  intro v
  simp [inner_neg_left, add_comm]

/-- In the cotangent model `V × V`, the Hamiltonian vector field of `H(q, p) = h(q)` is
`X_H(q, p) = (0, -∇h(q))`: the flow moves the momentum by `-∇h` and fixes the position. -/
theorem stdSymplecticForm_hamiltonianVectorField_comp_fst {h : V → ℝ} {x : V × V}
    (hh : DifferentiableAt ℝ h x.1) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (fun y ↦ h y.1) x = (0, -∇ h x.1) := by
  have hcomp : HasFDerivAt (fun y : V × V ↦ h y.1)
      ((fderiv ℝ h x.1).comp (ContinuousLinearMap.fst ℝ V V)) x :=
    hh.hasFDerivAt.comp x hasFDerivAt_fst
  refine stdSymplecticForm_hamiltonianVectorField ?_
  convert hcomp using 1
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [inner_gradient_left]

/-- The Poisson bracket on `V × V` in terms of partial gradients:
`{F, G} = ⟪∇_q F, ∇_p G⟫ - ⟪∇_p F, ∇_q G⟫`. -/
theorem stdSymplecticForm_poissonBracket {F G : V × V → ℝ} {x : V × V} {a b c d : V}
    (hF : HasFDerivAt F ((innerSL ℝ a).coprod (innerSL ℝ b)) x)
    (hG : HasFDerivAt G ((innerSL ℝ c).coprod (innerSL ℝ d)) x) :
    (stdSymplecticForm (V := V)).poissonBracket F G x = ⟪a, d⟫_ℝ - ⟪b, c⟫_ℝ := by
  rw [SymplecticForm.poissonBracket_eq_fderiv, stdSymplecticForm_hamiltonianVectorField hG,
    hF.fderiv]
  simp [inner_neg_right, sub_eq_add_neg]

end TauCeti
