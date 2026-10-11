/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.GraphAutomorphism

/-!
# The represented type-A graph involution of the special linear group

Signed reverse inverse transpose defines an automorphism of the special linear group scheme
over every commutative ring. Its square is the identity, and it carries each positive or
negative simple-root subgroup to the subgroup at the reversed node, with parameter unchanged.
These coordinate identities hold over the base ring itself, so they retain the scheme
structure in positive characteristic and over nonreduced rings.

The construction recovers the coordinate automorphism from the natural matrix involution
using `TauCeti.CommHopfAlgCat.pointsFunctor`. It uses the determinant-one presentation of
`SLₙ`, independently of a presentation by generators of a Kostant carrier.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapter 12.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* The matrix normalization is `Matrix.SpecialLinearGroup.typeAGraphAutomorphism`.
  The represented construction follows the Yoneda approach of
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.GraphAutomorphism`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u w

variable (R : Type u) [CommRing R] (r : ℕ)

/-- Transport the matrix graph involution to the multiplicative group of coordinate points. -/
private noncomputable def typeAGraphPointsMulEquiv (A : Type u) [CommRing A] [Algebra R A] :
    WithConv (coordinateHopfAlgebra R (r + 1) →ₐ[R] A) ≃*
      WithConv (coordinateHopfAlgebra R (r + 1) →ₐ[R] A) :=
  ((pointsMulEquiv (R := R) (A := A) (r + 1)).trans
    (Matrix.SpecialLinearGroup.typeAGraphAutomorphism r A)).trans
      (pointsMulEquiv (R := R) (A := A) (r + 1)).symm

private theorem pointsMulEquiv_typeAGraphPointsMulEquiv (A : Type u)
    [CommRing A] [Algebra R A] (f : WithConv (coordinateHopfAlgebra R (r + 1) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) (r + 1) (typeAGraphPointsMulEquiv R r A f) =
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism r A
        (pointsMulEquiv (R := R) (A := A) (r + 1) f) := by
  rw [typeAGraphPointsMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

private theorem typeAGraphPointsMulEquiv_natural
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) (f : WithConv (coordinateHopfAlgebra R (r + 1) →ₐ[R] A)) :
    typeAGraphPointsMulEquiv R r B (AlgHom.mapValue φ f) =
      AlgHom.mapValue φ (typeAGraphPointsMulEquiv R r A f) := by
  apply (pointsMulEquiv (R := R) (A := B) (r + 1)).injective
  rw [pointsMulEquiv_typeAGraphPointsMulEquiv, pointsMulEquiv_mapValue,
    pointsMulEquiv_mapValue, pointsMulEquiv_typeAGraphPointsMulEquiv]
  exact (Matrix.SpecialLinearGroup.map_typeAGraphAutomorphism r φ.toRingHom _).symm

/-- The natural graph involution on the group-valued functor represented by `SL_{r+1}`. -/
private noncomputable def typeAGraphPointsNatIso :
    HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R (r + 1)) ≅
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R (r + 1)) :=
  NatIso.ofComponents (fun A ↦ (typeAGraphPointsMulEquiv R r A).toGrpIso) (by
    intro A B φ
    ext f
    -- The newly defined components and categorical maps compute as point equivalences
    -- and postcomposition. The explicitly typed naturality theorem avoids unfolding them.
    exact typeAGraphPointsMulEquiv_natural R r φ.hom f)

/-- The coordinate Hopf-algebra automorphism of `SL_{r+1}` induced by signed reverse
inverse transpose. It is defined over every commutative base ring. -/
noncomputable def typeAGraphCoordinateIso :
    coordinateHopfAlgebra R (r + 1) ≅ coordinateHopfAlgebra R (r + 1) :=
  ((CommHopfAlgCat.pointsFunctor (R := R)).preimageIso (typeAGraphPointsNatIso R r)).unop

private theorem pointsMulEquiv_mapPointsFunctor_typeAGraphCoordinateIso_sameUniverse
    (A : Type u) [CommRing A] [Algebra R A]
    (f : WithConv (coordinateHopfAlgebra R (r + 1) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) (r + 1)
        ((CommHopfAlgCat.mapPointsFunctor (typeAGraphCoordinateIso R r).hom).app
          (CommAlgCat.of R A) f) =
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism r A
        (pointsMulEquiv (R := R) (A := A) (r + 1) f) := by
  have hmap := (CommHopfAlgCat.pointsFunctor (R := R)).map_preimage
    (typeAGraphPointsNatIso R r).hom
  have happ := congrArg (fun α => α.app (CommAlgCat.of R A) f) hmap
  have hcoordinate : (typeAGraphCoordinateIso R r).hom.op =
      (CommHopfAlgCat.pointsFunctor (R := R)).preimage
        (typeAGraphPointsNatIso R r).hom := rfl
  -- The opposite-category presentation of the Yoneda map is definitionally the
  -- named map on points; expose it to use `map_preimage`.
  change pointsMulEquiv (R := R) (A := A) (r + 1)
      (((CommHopfAlgCat.pointsFunctor (R := R)).map
        (typeAGraphCoordinateIso R r).hom.op).app (CommAlgCat.of R A) f) = _
  rw [hcoordinate, happ]
  -- The newly defined natural-isomorphism component computes as its point equivalence.
  exact pointsMulEquiv_typeAGraphPointsMulEquiv R r A f

/-- Precomposition with the coordinate graph automorphism realizes the signed matrix
graph automorphism on points over an algebra in any universe. -/
@[simp]
theorem pointsMulEquiv_comp_typeAGraphCoordinateIso (A : Type w)
    [CommRing A] [Algebra R A] (f : WithConv (coordinateHopfAlgebra R (r + 1) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) (r + 1)
        (toConv (f.ofConv.comp (typeAGraphCoordinateIso R r).hom.hom.toAlgHom)) =
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism r A
        (pointsMulEquiv (R := R) (A := A) (r + 1) f) := by
  let H := coordinateHopfAlgebra R (r + 1)
  let q : WithConv (H →ₐ[R] H) := toConv (AlgHom.id R H)
  have h := pointsMulEquiv_mapPointsFunctor_typeAGraphCoordinateIso_sameUniverse R r H q
  have hc := congrArg (pointsMulEquiv (R := R) (A := H) (r + 1))
    (CommHopfAlgCat.mapPointsFunctor_app_apply (typeAGraphCoordinateIso R r).hom
      (CommAlgCat.of R H) q)
  have hraw := hc.symm.trans h
  have hmap := congrArg (Matrix.SpecialLinearGroup.map f.ofConv.toRingHom) hraw
  rw [Matrix.SpecialLinearGroup.map_typeAGraphAutomorphism] at hmap
  -- The value-algebra universes occur under `max` in the point equivalence, so give
  -- the coefficient types explicitly when applying its naturality theorem.
  rw [← pointsMulEquiv_mapValue (R := R) (A := H) (B := A) (r + 1) f.ofConv
      (toConv (q.ofConv.comp (typeAGraphCoordinateIso R r).hom.hom.toAlgHom)),
    ← pointsMulEquiv_mapValue (R := R) (A := H) (B := A) (r + 1) f.ofConv q] at hmap
  have hqid : q.ofConv = AlgHom.id R H := ofConv_toConv _
  have hq : AlgHom.mapValue f.ofConv q = f := by
    rw [AlgHom.mapValue_apply, hqid]
    exact (congrArg toConv (AlgHom.comp_id f.ofConv)).trans (toConv_ofConv f)
  rw [hq] at hmap
  simpa only [q, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_assoc,
    AlgHom.id_comp] using hmap

/-- The coordinate graph automorphism is involutive over the base ring. -/
@[simp]
theorem typeAGraphCoordinateIso_hom_comp_self :
    (typeAGraphCoordinateIso R r).hom ≫ (typeAGraphCoordinateIso R r).hom =
      𝟙 (coordinateHopfAlgebra R (r + 1)) := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor (R := R)).map_injective
  rw [op_comp, Functor.map_comp]
  ext A f
  -- Faithfulness presents points through the opaque categorical functor; name the
  -- underlying algebra-homomorphism type before applying point computations.
  change WithConv (coordinateHopfAlgebra R (r + 1) →ₐ[R] A) at f
  apply (pointsMulEquiv (R := R) (A := A) (r + 1)).injective
  -- Opposite composition acts by nested precomposition; use the direct algebra-hom
  -- presentation so point computations do not unfold the categorical functor.
  change pointsMulEquiv (R := R) (A := A) (r + 1)
      (toConv ((f.ofConv.comp (typeAGraphCoordinateIso R r).hom.hom.toAlgHom).comp
        (typeAGraphCoordinateIso R r).hom.hom.toAlgHom)) =
    pointsMulEquiv (R := R) (A := A) (r + 1) f
  rw [pointsMulEquiv_comp_typeAGraphCoordinateIso, pointsMulEquiv_comp_typeAGraphCoordinateIso]
  exact Matrix.SpecialLinearGroup.typeAGraphAutomorphism_typeAGraphAutomorphism r A _

/-- The inverse coordinate graph automorphism equals its forward morphism. -/
@[simp]
theorem typeAGraphCoordinateIso_inv :
    (typeAGraphCoordinateIso R r).inv = (typeAGraphCoordinateIso R r).hom := by
  rw [← cancel_epi (typeAGraphCoordinateIso R r).hom]
  simp

/-- Lift a matrix identity between two root subgroups to their coordinate morphisms. -/
private theorem typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap_of_transvection
    {i j k l : Fin (r + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (h : ∀ (A : Type u) [CommRing A] (c : A),
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism r A
        (Matrix.SpecialLinearGroup.transvection hij c) =
          Matrix.SpecialLinearGroup.transvection hkl c) :
    (typeAGraphCoordinateIso R r).hom ≫ rootSubgroupCoordinateMap (R := R) hij =
      rootSubgroupCoordinateMap (R := R) hkl := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor (R := R)).map_injective
  rw [op_comp, Functor.map_comp]
  ext A f
  -- The categorical point functor is opaque; its underlying value is an algebra homomorphism.
  change WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) at f
  apply (pointsMulEquiv (R := R) (A := A) (r + 1)).injective
  let x := rootSubgroupCoordinateMap (R := R) hij
  let y := rootSubgroupCoordinateMap (R := R) hkl
  have hx : toConv (f.ofConv.comp x.hom.toAlgHom) = rootSubgroupPoints hij f :=
    (CommHopfAlgCat.mapPointsFunctor_app_apply x (CommAlgCat.of R A) f).symm.trans
      (mapPointsFunctor_rootSubgroupCoordinateMap_app _ (CommAlgCat.of R A) f)
  have hy : toConv (f.ofConv.comp y.hom.toAlgHom) = rootSubgroupPoints hkl f :=
    (CommHopfAlgCat.mapPointsFunctor_app_apply y (CommAlgCat.of R A) f).symm.trans
      (mapPointsFunctor_rootSubgroupCoordinateMap_app _ (CommAlgCat.of R A) f)
  -- The opposite composite acts by precomposition of its algebra-homomorphism components.
  change pointsMulEquiv (R := R) (A := A) (r + 1)
      (toConv ((f.ofConv.comp x.hom.toAlgHom).comp
        (typeAGraphCoordinateIso R r).hom.hom.toAlgHom)) =
    pointsMulEquiv (R := R) (A := A) (r + 1) (toConv (f.ofConv.comp y.hom.toAlgHom))
  rw [pointsMulEquiv_comp_typeAGraphCoordinateIso, hx, hy,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  exact h A _

/-- The graph automorphism reverses the positive simple-root maps with their parameters
unchanged. This is an equality of coordinate morphisms over the base ring. -/
@[reassoc (attr := simp)]
theorem typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap (i : Fin r) :
    (typeAGraphCoordinateIso R r).hom ≫
        rootSubgroupCoordinateMap (R := R) (Fin.castSucc_lt_succ (i := i)).ne =
      rootSubgroupCoordinateMap (R := R) (Fin.castSucc_lt_succ (i := i.rev)).ne := by
  apply typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap_of_transvection
  intro A _ c
  exact Matrix.SpecialLinearGroup.typeAGraphAutomorphism_transvection r A i c

/-- The graph automorphism also reverses the negative simple-root maps without a sign. -/
@[reassoc (attr := simp)]
theorem typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap_lower (i : Fin r) :
    (typeAGraphCoordinateIso R r).hom ≫
        rootSubgroupCoordinateMap (R := R) (Fin.castSucc_lt_succ (i := i)).ne' =
      rootSubgroupCoordinateMap (R := R) (Fin.castSucc_lt_succ (i := i.rev)).ne' := by
  apply typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap_of_transvection
  intro A _ c
  exact Matrix.SpecialLinearGroup.typeAGraphAutomorphism_transvection_lower r A i c

/-- The signed type-A graph automorphism as an isomorphism of special-linear group schemes
over the base ring. -/
noncomputable def typeAGraphIso : groupScheme R (r + 1) ≅ groupScheme R (r + 1) :=
  eqToIso (groupScheme_def R (r + 1)) ≪≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
      (typeAGraphCoordinateIso R r).op ≪≫
    (eqToIso (groupScheme_def R (r + 1))).symm

/-- The group-scheme graph automorphism is relative spectrum of the coordinate automorphism. -/
theorem typeAGraphIso_hom :
    (typeAGraphIso R r).hom =
      eqToHom (groupScheme_def R (r + 1)) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (typeAGraphCoordinateIso R r).hom.op ≫
        eqToHom (groupScheme_def R (r + 1)).symm :=
  (rfl)

/-- The represented group-scheme graph automorphism is involutive. -/
@[simp]
theorem typeAGraphIso_hom_comp_self :
    (typeAGraphIso R r).hom ≫ (typeAGraphIso R r).hom = 𝟙 (groupScheme R (r + 1)) := by
  simp only [typeAGraphIso_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Functor.map_comp_assoc, ← op_comp, typeAGraphCoordinateIso_hom_comp_self]
  simp

/-- The inverse group-scheme graph automorphism equals its forward morphism. -/
@[simp]
theorem typeAGraphIso_inv :
    (typeAGraphIso R r).inv = (typeAGraphIso R r).hom := by
  rw [← cancel_epi (typeAGraphIso R r).hom]
  simp

/-- The group-scheme graph automorphism reverses positive simple-root subgroups, with the
additive parameter unchanged. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_typeAGraphIso_hom (i : Fin r) :
    rootSubgroup (R := R) (Fin.castSucc_lt_succ (i := i)).ne ≫
        (typeAGraphIso R r).hom =
      rootSubgroup (R := R) (Fin.castSucc_lt_succ (i := i.rev)).ne := by
  simp only [rootSubgroup_def, typeAGraphIso_hom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc, ← op_comp,
    typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap]

/-- The group-scheme graph automorphism also reverses negative simple-root subgroups without
changing their parameters. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_typeAGraphIso_hom_lower (i : Fin r) :
    rootSubgroup (R := R) (Fin.castSucc_lt_succ (i := i)).ne' ≫
        (typeAGraphIso R r).hom =
      rootSubgroup (R := R) (Fin.castSucc_lt_succ (i := i.rev)).ne' := by
  simp only [rootSubgroup_def, typeAGraphIso_hom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc, ← op_comp,
    typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap_lower]

end TauCeti.SpecialLinear
