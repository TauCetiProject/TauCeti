/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology
public import TauCeti.Algebra.Homology.SquareZero

/-!
# The cohomology of a DG right module as the homology of its differential

The cohomology `H(M)` of a DG right module `M` over a DG algebra `A`
(`TauCeti.IsDGRightModule.Cohomology`) is built from cycles and boundaries that are modules over
the opposite algebra of cycles of `A`, so that `H(A)` acts on it. Forgetting that action, it is the
homology `ker dM ⧸ im dM` of the differential, a square-zero `R`-linear endomorphism of `M`
(`LinearMap.homology`): the two quotients have the same cycles and the same boundaries
(`TauCeti.IsDGRightModule.cohomologyEquivHomology`).

Through this identification the homology of square-zero endomorphisms applies to DG right
modules: an `R`-linear map `f : M → N` commuting with the differentials, between DG right modules
over possibly different DG algebras, induces `LinearMap.homologyMap` on cohomology, and homotopic
such maps induce the same map (`LinearMap.homologyMap_eq_of_sub_eq`). This handles comparisons
that are not module morphisms, such as the homotopy retraction between a DG local system at one
basepoint and its change of basepoint along a path, which relates modules over the chains on the
loops at two different points. For morphisms of DG right modules over one algebra, the map on
cohomology that is linear over the cohomology algebra is `TauCeti.DGRightModuleHom.cohomologyMap`.

The same comparison for `A∞` algebras is `TauCeti.AInfinityAlgebra.cohomologyEquivHomology`.

## Main definitions

* `TauCeti.IsDGRightModule.cohomologyEquivHomology`: the identification
  `H(M) ≃ₗ[R] ker dM ⧸ im dM`.
-/

public section

namespace TauCeti

namespace IsDGRightModule

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  (hM : IsDGRightModule h ℳ dM)

include hM in
/-- The differential of a DG right module squares to zero, as a linear map. -/
theorem comp_self_eq_zero : dM ∘ₗ dM = 0 :=
  LinearMap.ext hM.sq_zero

/-- The cycles of a DG right module, as an `R`-module, are the kernel of its differential. -/
private def cyclesEquivKer : hM.cycles ≃ₗ[R] LinearMap.ker dM where
  toFun z := ⟨z, LinearMap.mem_ker.mpr (hM.mem_cycles.mp z.property)⟩
  invFun z := ⟨z, hM.mem_cycles.mpr (LinearMap.mem_ker.mp z.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem map_cyclesEquivKer_boundaries :
    (hM.boundaries.restrictScalars R).map (cyclesEquivKer hM).toLinearMap =
      dM.boundariesInKer := by
  ext z
  rw [Submodule.mem_map_equiv, Submodule.restrictScalars_mem, mem_boundaries,
    LinearMap.mem_boundariesInKer]
  rfl

/-- **The cohomology of a DG right module is the homology of its differential**: forgetting the
action of the cohomology algebra, `H(M)` is `ker dM ⧸ im dM` as an `R`-module. A class goes to
the class of the same cycle (`TauCeti.IsDGRightModule.cohomologyEquivHomology_mk`). -/
noncomputable def cohomologyEquivHomology :
    hM.Cohomology ≃ₗ[R] dM.homology hM.comp_self_eq_zero :=
  (Submodule.Quotient.restrictScalarsEquiv R hM.boundaries).symm ≪≫ₗ
    Submodule.Quotient.equiv _ _ (cyclesEquivKer hM) (map_cyclesEquivKer_boundaries hM)

/-- The identification sends the class of a cycle to the class of the same element. -/
@[simp]
theorem cohomologyEquivHomology_mk (z : hM.cycles) :
    hM.cohomologyEquivHomology (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨z, LinearMap.mem_ker.mpr (hM.mem_cycles.mp z.property)⟩ :=
  (rfl)

/-- The inverse identification sends the class of an element of the kernel to the class of the
same cycle. -/
@[simp]
theorem cohomologyEquivHomology_symm_mk (z : LinearMap.ker dM) :
    hM.cohomologyEquivHomology.symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨z, hM.mem_cycles.mpr (LinearMap.mem_ker.mp z.property)⟩ :=
  (rfl)

end IsDGRightModule

end TauCeti
