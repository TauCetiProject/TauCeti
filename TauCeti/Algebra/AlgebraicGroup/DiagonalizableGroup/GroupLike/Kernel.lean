/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Kernel
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.GroupLikeEvaluation

/-!
# Kernels in intrinsic character coordinates

For diagonalizable coordinate Hopf algebras, the coordinate algebra of the kernel of a
homomorphism is the group algebra of its character cokernel. Here the characters are the
intrinsic group-like elements, so no presentation of either group as `D(M)` is chosen.
The comparison commutes with the ambient quotient maps. It therefore retains the closed
subgroup structure, including infinitesimal kernels in positive characteristic.

This extends the group-algebra calculation in
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Kernel` using the natural evaluation
isomorphisms of `TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.GroupLikeEvaluation`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(b).
-/

public section

open CategoryTheory

namespace TauCeti.DiagonalizableGroup

universe u

variable {k : Type u} [CommRing k] [IsDomain k]
variable {H K : _root_.CommHopfAlgCat.{u} k}
variable [Module.IsTorsionFree k H] [Module.IsTorsionFree k K]
variable (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤)
variable (hK : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := K))) = ⊤)
variable (f : H ⟶ K)

include hH in
private theorem kernelHopfIdeal_comap_evaluationIso :
    (CommHopfAlgCat.kernelHopfIdeal f).comapOfSurjective
        (CommHopfAlgCat.evaluationIso hK).hom.hom
        (ConcreteCategory.bijective_of_isIso (CommHopfAlgCat.evaluationIso hK).hom).2 =
      CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k
          (TauCeti.GroupLike.map f.hom))) := by
  have h := congrArg CommHopfAlgCat.kernelHopfIdeal
    (CommHopfAlgCat.evaluationIso_naturality hH hK f)
  rw [CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective _
    (ConcreteCategory.bijective_of_isIso (CommHopfAlgCat.evaluationIso hH).hom).2,
    CommHopfAlgCat.kernelHopfIdeal_comp] at h
  rw [h, HopfIdeal.comapOfSurjective_map_of_bijective _ _
    (ConcreteCategory.bijective_of_isIso (CommHopfAlgCat.evaluationIso hK).hom)]

/-- The kernel coordinate algebra of a morphism of diagonalizable groups is the group
algebra of the cokernel of its intrinsic character map. -/
noncomputable def kernelGroupLikeCoordinateIso :
    CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f) ≅
      CommHopfAlgCat.of k
        (MonoidAlgebra k (_root_.GroupLike k K ⧸ (TauCeti.GroupLike.map f.hom).range)) :=
  (CommHopfAlgCat.quotientIsoOfIso (CommHopfAlgCat.evaluationIso hK)
      (CommHopfAlgCat.kernelHopfIdeal f)).symm ≪≫
    eqToIso (congrArg (CommHopfAlgCat.quotient _)
      (kernelHopfIdeal_comap_evaluationIso hH hK f)) ≪≫
    kernelCoordinateIso k (TauCeti.GroupLike.map f.hom)

/-- The intrinsic kernel comparison commutes with the quotient coordinate maps. The
ambient element is first expressed in its intrinsic character coordinates. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_kernelGroupLikeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient K (CommHopfAlgCat.kernelHopfIdeal f) ≫
        (kernelGroupLikeCoordinateIso hH hK f).hom =
      (CommHopfAlgCat.evaluationIso hK).inv ≫
        CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k
          (QuotientGroup.mk' (TauCeti.GroupLike.map f.hom).range)) := by
  simp only [kernelGroupLikeCoordinateIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  simp only [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_inv]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_eqToHom
    (kernelHopfIdeal_comap_evaluationIso hH hK f).symm]
  exact mkQuotient_comp_kernelCoordinateIso_hom k (TauCeti.GroupLike.map f.hom)

end TauCeti.DiagonalizableGroup
