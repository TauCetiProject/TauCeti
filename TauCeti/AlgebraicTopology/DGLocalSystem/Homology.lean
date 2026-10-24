/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.HomologyZero
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology

/-!
# The homology of a DG local system as a representation of the fundamental group

Let `𝓕` be a DG local system on a pointed space `(B, b)`, a right DG module over the chain algebra
`C_*(Ω_b B; R)` of the Moore loops. Its homology `H(𝓕)` is a right module over the homology
`H(C_*(Ω_b B; R))`, whose degree-zero part `H₀(Ω_b B; R)` is the group ring `R[π₁(B, b)]`. So the
fundamental group acts on `H(𝓕)`: this is the homology of `𝓕` as a classical local system, the
kind of coefficients `H_q(𝓕)` that appear on the second page of the index spectral sequence of a
twisted complex. The action is on the total homology `H(𝓕)`, the direct sum of the `H_q(𝓕)`.

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

* `TauCeti.groupAlgebraToLoopChainCohomology`: the algebra map
  `R[π₁(B, b)] → H(C_*(Ω_b B; R))`.
* `TauCeti.IsDGRightModule.cohomologyRepresentation`: the representation of `π₁(B, b)` on the
  homology of a DG local system.

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

section GroupAlgebra

variable (B : Type u) [TopologicalSpace B] (b : B) (R : Type u) [CommRing R]

/-- The class of a zero chain of Moore loops in the cohomology of the chain algebra. -/
private def zeroChainToCohomology :
    NormalizedCubicalChain (MooreLoopSpace B b) R 0 →ₗ[R]
      (loopChain_isDGAlgebra B b R).Cohomology where
  toFun a := Ideal.Quotient.mkₐ R _ ⟨cubicalChainLof (MooreLoopSpace B b) R 0 a,
    (loopChain_isDGAlgebra B b R).mem_cycles.mpr (cubicalChainDifferential_lof_zero _ _ a)⟩
  map_add' a a' := by rw [← map_add]; congr 1; ext; simp
  map_smul' r a := by rw [RingHom.id_apply, ← map_smul]; congr 1; ext; simp

private theorem zeroChainToCohomology_apply
    (a : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    zeroChainToCohomology B b R a = Ideal.Quotient.mk _ ⟨cubicalChainLof (MooreLoopSpace B b) R 0 a,
      (loopChain_isDGAlgebra B b R).mem_cycles.mpr (cubicalChainDifferential_lof_zero _ _ a)⟩ :=
  (rfl)

/-- Boundaries of `1`-chains have zero class in the cohomology of the chain algebra. -/
private theorem ker_le_ker_zeroChainToCohomology :
    LinearMap.ker (loopZeroChainToGroupAlgebra B b R) ≤
      LinearMap.ker (zeroChainToCohomology B b R) := fun a ha ↦ by
  obtain ⟨c, rfl⟩ := (loopZeroChainToGroupAlgebra_eq_zero_iff a).1 ha
  rw [LinearMap.mem_ker, zeroChainToCohomology_apply]
  convert (loopChain_isDGAlgebra B b R).quotientMk_map_eq_zero
    (cubicalChainLof (MooreLoopSpace B b) R 1 c) using 3
  rw [cubicalChainDifferential_lof_succ]

/-- The linear map underlying `groupAlgebraToLoopChainCohomology`: the class of a zero chain,
descended along the surjection `loopZeroChainToGroupAlgebra`, whose kernel consists of
boundaries. -/
private def groupAlgebraToLoopChainCohomologyLinear :
    MonoidAlgebra R (FundamentalGroup B b) →ₗ[R] (loopChain_isDGAlgebra B b R).Cohomology :=
  ((LinearMap.ker (loopZeroChainToGroupAlgebra B b R)).liftQ (zeroChainToCohomology B b R)
      (ker_le_ker_zeroChainToCohomology B b R)) ∘ₗ
    ((loopZeroChainToGroupAlgebra B b R).quotKerEquivOfSurjective
      loopZeroChainToGroupAlgebra_surjective).symm.toLinearMap

private theorem groupAlgebraToLoopChainCohomologyLinear_apply
    (a : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    groupAlgebraToLoopChainCohomologyLinear B b R (loopZeroChainToGroupAlgebra B b R a) =
      zeroChainToCohomology B b R a := by
  rw [groupAlgebraToLoopChainCohomologyLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← LinearMap.quotKerEquivOfSurjective_apply_mk _ loopZeroChainToGroupAlgebra_surjective,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]

/-- **The group ring in the cohomology of the loop chain algebra**: the algebra map
`R[π₁(B, b)] → H(C_*(Ω_b B; R))` sending the basis element
`MooreLoopSpace.fundamentalGroupHom b γ` of the class of a Moore loop `γ` to the cohomology class
of the point chain of `γ`. It is the inverse of the identification of `H₀(Ω_b B; R)` with
`R[π₁(B, b)]` by `loopZeroChainToGroupAlgebra`, followed by the inclusion of degree zero. -/
def groupAlgebraToLoopChainCohomology :
    MonoidAlgebra R (FundamentalGroup B b) →ₐ[R] (loopChain_isDGAlgebra B b R).Cohomology :=
  AlgHom.ofLinearMap (groupAlgebraToLoopChainCohomologyLinear B b R)
    (by
      rw [← loopZeroChainToGroupAlgebra_one, groupAlgebraToLoopChainCohomologyLinear_apply,
        zeroChainToCohomology_apply, ← map_one (Ideal.Quotient.mkₐ R _)]
      -- The unit of the chain algebra is the point chain of the unit loop in dimension zero.
      exact congrArg (Ideal.Quotient.mkₐ R _)
        (Subtype.ext (rfl : DirectSum.of _ 0 (NormalizedCubicalChain.one _ R) = 1)))
    (fun x y ↦ by
      obtain ⟨a, rfl⟩ := loopZeroChainToGroupAlgebra_surjective (R := R) (x := b) x
      obtain ⟨a', rfl⟩ := loopZeroChainToGroupAlgebra_surjective (R := R) (x := b) y
      rw [← loopZeroChainToGroupAlgebra_mul, groupAlgebraToLoopChainCohomologyLinear_apply,
        groupAlgebraToLoopChainCohomologyLinear_apply,
        groupAlgebraToLoopChainCohomologyLinear_apply, zeroChainToCohomology_apply,
        zeroChainToCohomology_apply, zeroChainToCohomology_apply, ← map_mul]
      exact congrArg _ (Subtype.ext (cubicalChainLof_mul _ R a a').symm))

/-- `groupAlgebraToLoopChainCohomology` sends the image of a zero chain in the group ring to the
cohomology class of the zero chain. -/
@[simp]
theorem groupAlgebraToLoopChainCohomology_loopZeroChainToGroupAlgebra
    (a : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    groupAlgebraToLoopChainCohomology B b R (loopZeroChainToGroupAlgebra B b R a) =
      Ideal.Quotient.mk _ ⟨cubicalChainLof (MooreLoopSpace B b) R 0 a,
        (loopChain_isDGAlgebra B b R).mem_cycles.mpr (cubicalChainDifferential_lof_zero _ _ a)⟩ :=
  groupAlgebraToLoopChainCohomologyLinear_apply B b R a

variable {B b R} in
/-- `groupAlgebraToLoopChainCohomology` sends the basis element of the class of a Moore loop `γ`
to the cohomology class of the point chain of `γ`. -/
theorem groupAlgebraToLoopChainCohomology_of_fundamentalGroupHom (γ : MooreLoopSpace B b) :
    groupAlgebraToLoopChainCohomology B b R
        (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ)) =
      Ideal.Quotient.mk _ ⟨cubicalChainLof (MooreLoopSpace B b) R 0
          (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R (SingularCube.point γ)),
        (loopChain_isDGAlgebra B b R).mem_cycles.mpr
          (cubicalChainDifferential_lof_zero _ _ _)⟩ := by
  rw [← groupAlgebraToLoopChainCohomology_loopZeroChainToGroupAlgebra,
    loopZeroChainToGroupAlgebra_ofCube, SingularCube.point_apply, MonoidAlgebra.of_apply]

end GroupAlgebra

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

end IsDGRightModule

end Representation

end TauCeti
