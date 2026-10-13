/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.Generated.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.Solvable

/-!
# Solvability of the generated positive Geck subgroup

The closed subgroup generated over a commutative ring by the positive numbered Geck root
subgroups and the weight torus lies in the scalar extension of the integral positive carrier.
This inclusion is scheme-theoretic: it is represented by a surjective coordinate morphism,
compatible with the ambient general linear group. Consequently all its point groups are
solvable, since the integral positive carrier has a triangular realization.

In particular the smooth positive generated subgroup over a field has solvable geometric
points. This is an input to recognizing it as a Borel subgroup; maximality among smooth
connected solvable closed subgroups is a further requirement.

The containment proof uses the transported positive-root and torus factorizations in
`GeckLattice.Positive.BaseChange`. The solvability argument reuses the integral triangular
realization in `GeckLattice.Positive.Triangular.Basic`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--28.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory

universe v w

noncomputable section

variable (t : DynkinType) (ht : t.Valid) (A : Type v) [CommRing A]

/-- The subgroup generated over the new base by the positive root subgroups and weight torus
lies in the scalar extension of the integral positive carrier. The scalar-tensor ideal is
pulled back to the coordinate algebra of the general linear group over the new base. -/
theorem geckTorusPositiveBaseChangeIdeal_comap_le_geckPositiveGeneratedDefiningIdeal :
    (t.geckTorusPositiveBaseChangeIdeal ht A).comapOfSurjective
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).inv.hom
        (ConcreteCategory.bijective_of_isIso
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).inv).2 ≤
      t.geckPositiveGeneratedDefiningIdeal ht A := by
  rw [t.le_geckPositiveGeneratedDefiningIdeal_iff ht A]
  intro j x hx
  have hzero := (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr
    (HopfIdeal.mem_comapOfSurjective.mp hx)
  rcases j with i | u
  · rw [geckPositiveGeneratorCoordinateMap_inl, geckGeneratorCoordinateMap_inl]
    have hcomp :
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).inv ≫
            CommHopfAlgCat.mkQuotient _ (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
            t.geckRootSubgroupToTorusPositiveBaseChangeCoordinateMap ht A i ≫
            (_root_.CommHopfAlgCat.ofHom
              (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
          t.geckRootSubgroupBaseChangeCoordinateMap ht A (.inl i) := by
      rw [← Category.assoc,
        ← t.mkQuotient_comp_geckTorusPositiveBaseChangeInclusionCoordinateMap ht A,
        Category.assoc, t.geckTorusPositiveBaseChangeInclusionCoordinateMap_comp_root ht A,
        t.mkQuotient_comp_geckRootSubgroupToBaseChangeCoordinateMap ht A]
    have heval := congrArg (fun f => f.hom x) hcomp
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at heval
    rw [hzero, map_zero, map_zero] at heval
    exact RingHom.mem_ker.mpr heval.symm
  · rcases u with ⟨⟩
    rw [geckPositiveGeneratorCoordinateMap_inr, geckGeneratorCoordinateMap_inr]
    have hcomp :
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).inv ≫
            CommHopfAlgCat.mkQuotient _ (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
            t.geckWeightTorusToTorusPositiveBaseChangeCoordinateMap ht A ≫
            (_root_.CommHopfAlgCat.ofHom
              (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
                (G := SplitTorus.characterGroup (Fin t.rank)))) =
          t.geckWeightTorusBaseChangeCoordinateMap ht A := by
      rw [← Category.assoc,
        ← t.mkQuotient_comp_geckTorusPositiveBaseChangeInclusionCoordinateMap ht A,
        Category.assoc,
        t.geckTorusPositiveBaseChangeInclusionCoordinateMap_comp_weightTorus ht A,
        t.mkQuotient_comp_geckWeightTorusToBaseChangeCoordinateMap ht A]
    have heval := congrArg (fun f => f.hom x) hcomp
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at heval
    rw [hzero, map_zero, map_zero] at heval
    exact RingHom.mem_ker.mpr heval.symm

/-- The coordinate morphism of the closed inclusion of the generated positive subgroup into
the scalar extension of the integral positive carrier. -/
def geckTorusPositiveBaseChangeToGeneratedCoordinateMap :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A) ⟶
      t.geckPositiveGeneratedCoordinateHopfAlgebra ht A :=
  (CommHopfAlgCat.quotientIsoOfIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).symm
      (t.geckTorusPositiveBaseChangeIdeal ht A)).inv ≫
    CommHopfAlgCat.quotientMapOfLe _
      (t.geckTorusPositiveBaseChangeIdeal_comap_le_geckPositiveGeneratedDefiningIdeal ht A) ≫
    eqToHom (t.geckPositiveGeneratedCoordinateHopfAlgebra_def ht A).symm

/-- The positive-carrier inclusion agrees with the ambient general linear base-change
comparison on quotient coordinate maps. -/
@[simp]
theorem mkQuotient_comp_geckTorusPositiveBaseChangeToGeneratedCoordinateMap :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A) ≫
        t.geckTorusPositiveBaseChangeToGeneratedCoordinateMap ht A =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).hom ≫
        t.geckPositiveGeneratedCoordinateMap ht A := by
  rw [geckTorusPositiveBaseChangeToGeneratedCoordinateMap, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_inv]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]
  rw [geckPositiveGeneratedCoordinateMap_def, Iso.symm_inv]

/-- The positive-carrier inclusion has a surjective coordinate morphism. -/
theorem geckTorusPositiveBaseChangeToGeneratedCoordinateMap_surjective :
    Function.Surjective (t.geckTorusPositiveBaseChangeToGeneratedCoordinateMap ht A).hom := by
  have hcomp : Function.Surjective
      (((GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).hom ≫
        t.geckPositiveGeneratedCoordinateMap ht A).hom) := by
    simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using
      (t.geckPositiveGeneratedCoordinateMap_surjective ht A).comp
        (ConcreteCategory.bijective_of_isIso
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).hom).2
  rw [← t.mkQuotient_comp_geckTorusPositiveBaseChangeToGeneratedCoordinateMap ht A,
    _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at hcomp
  exact hcomp.of_comp

/-- Every commutative-algebra-valued point group of the generated positive Geck subgroup is
solvable. No field or reducedness hypothesis is needed. -/
theorem isSolvable_points_geckPositiveGenerated (B : CommAlgCat.{w} A) :
    Group.IsSolvable
      (HopfAlgebra.points (R := A) (H := t.geckPositiveGeneratedCoordinateHopfAlgebra ht A) B) := by
  let f := t.geckTorusPositiveBaseChangeToGeneratedCoordinateMap ht A
  let _ : Group.IsSolvable
      (HopfAlgebra.points (R := A)
        (H := CommHopfAlgCat.quotient
          (CommHopfAlgCat.baseChange (K := A)
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
          (t.geckTorusPositiveBaseChangeIdeal ht A)) B) :=
    t.isSolvable_points_geckTorusPositiveBaseChange ht A B
  exact Group.isSolvable_of_isSolvable_injective
    (G := HopfAlgebra.points (R := A)
      (H := t.geckPositiveGeneratedCoordinateHopfAlgebra ht A) B)
    (G' := HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A)) B)
    (f := AlgHom.mapDomain (A := B) f.hom)
    (CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective f
      (t.geckTorusPositiveBaseChangeToGeneratedCoordinateMap_surjective ht A) B)

/-- Over every field, the generated positive Geck subgroup has solvable geometric points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_geckPositiveGeneratedCoordinateHopfAlgebra
    (k : Type v) [Field k] :
    geometricallySolvablePointsCommHopfAlgProperty k
      (t.geckPositiveGeneratedCoordinateHopfAlgebra ht k) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact t.isSolvable_points_geckPositiveGenerated ht k (CommAlgCat.of k (AlgebraicClosure k))

end

end TauCeti.DynkinType
