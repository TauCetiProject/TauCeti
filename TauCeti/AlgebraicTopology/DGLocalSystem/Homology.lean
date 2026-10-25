/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology

/-!
# The homology of a DG local system as a representation of the fundamental group

Let `𝓕` be a DG local system on a pointed space `(B, b)`, a right DG module over the chain algebra
`C_*(Ω_b B; R)` of the Moore loops. Its homology `H(𝓕)` is a right module over the homology
`H(C_*(Ω_b B; R))`, whose degree-zero part `H₀(Ω_b B; R)` is the group ring `R[π₁(B, b)]`. So the
fundamental group acts on `H(𝓕)`: this is the homology of `𝓕` as a classical local system, the
kind of coefficients `H_q(𝓕)` that appear on the second page of the index spectral sequence of a
twisted complex. The action is on the total homology `H(𝓕)`, the internal direct sum of the
`H_q(𝓕)` (`TauCeti.IsDGRightModule.isInternal_cohomologyGrading`). The group ring sits in degree
zero of `H(C_*(Ω_b B; R))`, so the action preserves degrees and restricts to each `H_q(𝓕)`
(`TauCeti.IsDGRightModule.cohomologyGradingRepresentation`). Through the grading
bridge `C^{-q} = C_q`, the homological degree `q` is the cohomological degree `-q`.

The degree-zero part enters through the algebra map
`TauCeti.groupAlgebraToLoopChainCohomology : R[π₁(B, b)] → H(C_*(Ω_b B; R))`, the inverse of
`TauCeti.loopZeroChainToGroupAlgebra` on classes of zero chains: the class of the point chain of a
Moore loop `γ` is the basis element `MooreLoopSpace.fundamentalGroupHom b γ`. A class `g` of the
fundamental group acts on `H(𝓕)` as the group ring element `g⁻¹` does from the right
(`TauCeti.IsDGRightModule.cohomologyRepresentation`), the convention of
`TauCeti.DGRightModuleCat.IsConcentratedInDegreeZero.representation`, so that the inverse of the
class of `γ` acts as the point chain of `γ`
(`TauCeti.IsDGRightModule.cohomologyRepresentation_fundamentalGroupHom_inv_apply`).

The DG local system is given here unbundled, as a DG right module structure `hM` on a graded
module `ℳ` with differential `dM`, as in `TauCeti.RankOneLocalSystem.twistedCochainComplexIso`.

## Main definitions

* `TauCeti.IsDGRightModule.cohomologyRepresentation`: the representation of `π₁(B, b)` on the
  homology of a DG local system.
* `TauCeti.IsDGRightModule.cohomologyGradingRepresentation`: its restriction to the homology in a
  single degree.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4 and 2.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 4.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

universe u uM

section Representation

variable {B : Type u} [TopologicalSpace B] {b : B} {R : Type u} [CommRing R]
  {M : Type uM} [AddCommGroup M] [Module R M] [Module (loopChainAlgebra B b R)ᵐᵒᵖ M]
  [IsScalarTower R (loopChainAlgebra B b R)ᵐᵒᵖ M] {ℳ : ℤ → Submodule R M}
  [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece ℳ]
  {dM : M →ₗ[R] M}

namespace IsDGRightModule

/-- **The representation of the fundamental group on the homology of a DG local system**: a class
`g` acts on `H(𝓕)` as the group ring element `g⁻¹` does from the right, through
`groupAlgebraToLoopChainCohomology`. So the inverse of the class of a Moore loop `γ` acts as the
point chain of `γ` (`cohomologyRepresentation_fundamentalGroupHom_inv_apply`). -/
def cohomologyRepresentation (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) :
    Representation R (FundamentalGroup B b) hM.Cohomology :=
  (MulEquiv.opOp (Module.End R hM.Cohomology)).symm.toMonoidHom.comp <|
    (((hM.cohomologyAction.comp (groupAlgebraToLoopChainCohomology B b R)).toMonoidHom.comp
      (MonoidAlgebra.of R _)).op.comp (MulEquiv.inv' (FundamentalGroup B b)).toMonoidHom)

variable (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM)

/-- A class `g` acts as the group ring element `g⁻¹` does from the right. -/
theorem cohomologyRepresentation_apply (g : FundamentalGroup B b) :
    hM.cohomologyRepresentation g = (hM.cohomologyAction
      (groupAlgebraToLoopChainCohomology B b R (MonoidAlgebra.of R _ g⁻¹))).unop :=
  (rfl)

/-- The inverse of the class of a Moore loop `γ` acts as the class of `γ` in the group ring does
from the right. -/
theorem cohomologyRepresentation_fundamentalGroupHom_inv (γ : MooreLoopSpace B b) :
    hM.cohomologyRepresentation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ =
      (hM.cohomologyAction (groupAlgebraToLoopChainCohomology B b R
        (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ)))).unop := by
  rw [cohomologyRepresentation_apply, inv_inv]

/-- The inverse of the class of a Moore loop `γ` acts on homology as the point chain of `γ`. -/
theorem cohomologyRepresentation_fundamentalGroupHom_inv_apply (γ : MooreLoopSpace B b)
    (x : hM.Cohomology) :
    hM.cohomologyRepresentation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ x =
      op (⟨cubicalChainLof (MooreLoopSpace B b) R 0
          (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R (SingularCube.point γ)),
        (loopChain_isDGAlgebra B b R).mem_cycles.mpr (cubicalChainDifferential_lof_zero _ _ _)⟩ :
          (loopChain_isDGAlgebra B b R).cycles) • x := by
  rw [cohomologyRepresentation_fundamentalGroupHom_inv,
    groupAlgebraToLoopChainCohomology_of_fundamentalGroupHom, cohomologyAction_mk]

/-- The fundamental group preserves the degrees of the homology of a DG local system. -/
theorem cohomologyRepresentation_apply_mem_cohomologyGrading (g : FundamentalGroup B b) {p : ℤ}
    {x : hM.Cohomology} (hx : x ∈ hM.cohomologyGrading p) :
    hM.cohomologyRepresentation g x ∈ hM.cohomologyGrading p := by
  rw [cohomologyRepresentation_apply]
  simpa only [add_zero] using hM.cohomologyAction_apply_mem_cohomologyGrading
    (groupAlgebraToLoopChainCohomology_mem_cohomologyGrading_zero B b R _) hx

/-- **The homology of a DG local system in a single degree** as a representation of the
fundamental group: the restriction of the representation on `H(𝓕)` to the classes of
cohomological degree `p`. In the homological grading of the source this is `H_q(𝓕)` for
`q = -p`. -/
def cohomologyGradingRepresentation (p : ℤ) :
    Representation R (FundamentalGroup B b) (hM.cohomologyGrading p) :=
  hM.cohomologyRepresentation.subrepresentation _ fun g _ ↦
    hM.cohomologyRepresentation_apply_mem_cohomologyGrading g

/-- A fundamental-group element acts on a class of degree `p` as it does on `H(𝓕)`. -/
@[simp]
theorem coe_cohomologyGradingRepresentation_apply (p : ℤ) (g : FundamentalGroup B b)
    (x : hM.cohomologyGrading p) :
    (hM.cohomologyGradingRepresentation p g x : hM.Cohomology) = hM.cohomologyRepresentation g x :=
  (rfl)

end IsDGRightModule

end Representation

end TauCeti
