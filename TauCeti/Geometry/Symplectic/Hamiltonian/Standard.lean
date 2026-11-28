/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Geometry.Symplectic.Hamiltonian.Transport
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
(`TauCeti.stdSymplecticForm_poissonBracket`). For the linear coordinates `⟪a, q⟫` and `⟪b, p⟫`
the Hamiltonian vector fields are the constants `(0, -a)` and `(b, 0)`, and their Poisson bracket
is `⟪a, b⟫` (`TauCeti.stdSymplecticForm_poissonBracket_inner_fst_inner_snd`); for `V = ℝ` this is
`{q, p} = 1`. If a group acts linearly and isometrically on `V`,
the Hamiltonian vector field of an invariant Hamiltonian commutes with the action
(`TauCeti.stdSymplecticForm_hamiltonianVectorField_smul`).

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
`X_H(q, p) = (0, -∇h(q))`: the flow moves the momentum by `-∇h` and fixes the position. If `h` is
not differentiable at `q`, both sides are `0` by convention. -/
theorem stdSymplecticForm_hamiltonianVectorField_comp_fst {h : V → ℝ} {x : V × V} :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (fun y ↦ h y.1) x = (0, -∇ h x.1) := by
  by_cases hh : DifferentiableAt ℝ h x.1
  · have hcomp : HasFDerivAt (fun y : V × V ↦ h y.1)
        ((fderiv ℝ h x.1).comp (ContinuousLinearMap.fst ℝ V V)) x :=
      hh.hasFDerivAt.comp x hasFDerivAt_fst
    refine stdSymplecticForm_hamiltonianVectorField ?_
    convert hcomp using 1
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [inner_gradient_left]
  · -- Differentiability of `h ∘ fst` at `x` would give that of `h`, along `q ↦ (q, x.2)`.
    have hd : ¬ DifferentiableAt ℝ (fun y : V × V ↦ h y.1) x := fun hd ↦ hh <|
      DifferentiableAt.comp (g := fun y : V × V ↦ h y.1) (f := fun q : V ↦ (q, x.2)) x.1 hd
        (differentiableAt_id.prodMk (differentiableAt_const x.2))
    rw [gradient_eq_zero_of_not_differentiableAt hh,
      (SymplecticForm.hamiltonianVectorField_eq_zero_iff _ _ _).2
        (fderiv_zero_of_not_differentiableAt hd)]
    rw [neg_zero]
    rfl

/-- The Poisson bracket on `V × V` in terms of partial gradients:
`{F, G} = ⟪∇_q F, ∇_p G⟫ - ⟪∇_p F, ∇_q G⟫`. -/
theorem stdSymplecticForm_poissonBracket {F G : V × V → ℝ} {x : V × V} {a b c d : V}
    (hF : HasFDerivAt F ((innerSL ℝ a).coprod (innerSL ℝ b)) x)
    (hG : HasFDerivAt G ((innerSL ℝ c).coprod (innerSL ℝ d)) x) :
    (stdSymplecticForm (V := V)).poissonBracket F G x = ⟪a, d⟫_ℝ - ⟪b, c⟫_ℝ := by
  rw [SymplecticForm.poissonBracket_eq_fderiv, stdSymplecticForm_hamiltonianVectorField hG,
    hF.fderiv]
  simp [inner_neg_right, sub_eq_add_neg]

/-- The linear position coordinate `q ↦ ⟪a, q⟫` has the constant Hamiltonian vector field
`(0, -a)`. -/
@[simp]
theorem stdSymplecticForm_hamiltonianVectorField_inner_fst (a : V) (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (fun y ↦ ⟪a, y.1⟫_ℝ) x = (0, -a) := by
  have h : HasFDerivAt (fun y : V × V ↦ ⟪a, y.1⟫_ℝ) ((innerSL ℝ a).coprod (innerSL ℝ 0)) x := by
    convert ((innerSL ℝ a).coprod (innerSL ℝ (0 : V))).hasFDerivAt using 1
    ext y
    simp
  simp [stdSymplecticForm_hamiltonianVectorField h]

/-- The linear momentum coordinate `p ↦ ⟪b, p⟫` has the constant Hamiltonian vector field
`(b, 0)`. -/
@[simp]
theorem stdSymplecticForm_hamiltonianVectorField_inner_snd (b : V) (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (fun y ↦ ⟪b, y.2⟫_ℝ) x = (b, 0) := by
  have h : HasFDerivAt (fun y : V × V ↦ ⟪b, y.2⟫_ℝ) ((innerSL ℝ 0).coprod (innerSL ℝ b)) x := by
    convert ((innerSL ℝ (0 : V)).coprod (innerSL ℝ b)).hasFDerivAt using 1
    ext y
    simp
  simp [stdSymplecticForm_hamiltonianVectorField h]

/-- **The canonical Poisson bracket.** The linear coordinates `⟪a, q⟫` and `⟪b, p⟫` have Poisson
bracket `⟪a, b⟫`; for `V = ℝ` and `a = b = 1` this is `{q, p} = 1`. -/
@[simp]
theorem stdSymplecticForm_poissonBracket_inner_fst_inner_snd (a b : V) (x : V × V) :
    (stdSymplecticForm (V := V)).poissonBracket (fun y ↦ ⟪a, y.1⟫_ℝ) (fun y ↦ ⟪b, y.2⟫_ℝ) x =
      ⟪a, b⟫_ℝ := by
  simp [SymplecticForm.poissonBracket_def]

/-- **Hamiltonian vector fields of invariant Hamiltonians are equivariant.** Let a group act
linearly and isometrically on `V`, and on positions and momenta of `V × V` alike. If a Hamiltonian
`H` is invariant under `g`, then its Hamiltonian vector field satisfies `X_H(g • x) = g • X_H(x)`.
For example, rotations commute with the Hamiltonian vector field of a central force. -/
theorem stdSymplecticForm_hamiltonianVectorField_smul {G : Type*} [Group G]
    [DistribMulAction G V] [SMulCommClass G ℝ V] [IsIsometricSMul G V] {H : V × V → ℝ} {g : G}
    (hH : ∀ y, H (g • y) = H y) (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField H (g • x) =
      g • (stdSymplecticForm (V := V)).hamiltonianVectorField H x := by
  have he : SymplecticForm.IsSymplectomorphism stdSymplecticForm stdSymplecticForm
      (DistribMulAction.toLinearEquiv ℝ (V × V) g) :=
    SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ stdSymplecticForm_smul g v w
  have hHe : H ∘ (DistribMulAction.toLinearEquiv ℝ (V × V) g).symm = H := by
    funext y
    simpa using (hH (g⁻¹ • y)).symm
  simpa [hHe] using (he.map_hamiltonianVectorField H x).symm

end TauCeti
