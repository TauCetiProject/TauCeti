/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.Monoidal
public import TauCeti.Condensed.Light.NullSequence.Basic

import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Families of null sequences

Sections over `T` of the internal Hom out of the free module on a light profinite set `S` are
sections over `S ⊗ T`. Consequently, maps from the null-sequence module tensored with the free
module on `S` correspond to sections over `S ⊗ C` vanishing over `S ⊗ {∞}`, where `C` is the
convergent sequence: these are the null sequences parametrized by `S`. Precomposition with the
null shift restricts such a section along the successor map on `C`.

This is the family version of the null-sequence test in Rodríguez Camargo,
*Notes on Solid Geometry*, Definition 3.2.1.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory MonoidalClosed LightCondensed Opposite
  Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : Type u} [CommRing R]

namespace LightProfinite

/-- Sections over `T` of the internal Hom out of the free module on `S` are the sections over
`S ⊗ T`, through the free-module mapping property and the monoidal structure of the free
functor. -/
noncomputable def ihomFreeSectionsEquiv (S T : LightProfinite.{u}) (B : LightCondMod.{u} R) :
    ((ihom ((free R).obj S.toCondensed)).obj B).obj.obj (op T) ≃+ B.obj.obj (op (S ⊗ T)) :=
  let i := Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ free R) S T
  let e : (_ ⟶ B) ≃+ (_ ⟶ B) :=
    { toFun g := i.inv ≫ g
      invFun g := i.hom ≫ g
      left_inv g := by simp
      right_inv g := by simp
      map_add' g h := by simp }
  T.freeModuleHomEquiv.symm.trans <|
    ((ihom.adjunction _).homAddEquiv _ _).symm.trans <| e.trans (S ⊗ T).freeModuleHomEquiv

/-- The section over `S ⊗ T` is the free-section comparison of the uncurried map, after the
monoidal comparison of free modules. -/
lemma ihomFreeSectionsEquiv_apply (S T : LightProfinite.{u}) (B : LightCondMod.{u} R)
    (y : ((ihom ((free R).obj S.toCondensed)).obj B).obj.obj (op T)) :
    ihomFreeSectionsEquiv S T B y = (S ⊗ T).freeModuleHomEquiv
      ((Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ free R) S T).inv ≫
        uncurry (T.freeModuleHomEquiv.symm y)) := (rfl)

/-- The section comparison is natural in the test space: restriction along `π` corresponds to
restriction along `S ◁ π`. -/
lemma ihomFreeSectionsEquiv_map {S T T' : LightProfinite.{u}} (π : T' ⟶ T)
    (B : LightCondMod.{u} R) (y : ((ihom ((free R).obj S.toCondensed)).obj B).obj.obj (op T)) :
    ihomFreeSectionsEquiv S T' B (((ihom ((free R).obj S.toCondensed)).obj B).obj.map π.op y) =
      B.obj.map (S ◁ π).op (ihomFreeSectionsEquiv S T B y) := by
  have h : T'.freeModuleHomEquiv.symm
      (((ihom ((free R).obj S.toCondensed)).obj B).obj.map π.op y) =
        (free R).map (lightProfiniteToLightCondSet.map π) ≫ T.freeModuleHomEquiv.symm y := by
    rw [AddEquiv.symm_apply_eq, freeModuleHomEquiv_comp, AddEquiv.apply_symm_apply]
  rw [ihomFreeSectionsEquiv_apply, ihomFreeSectionsEquiv_apply, h, uncurry_natural_left,
    ← freeModuleHomEquiv_comp]
  congr 1
  simpa using δ_natural_right_assoc (lightProfiniteToLightCondSet ⋙ free R) S π
    (uncurry (T.freeModuleHomEquiv.symm y))

end LightProfinite

namespace TauCeti

open LightProfinite

variable (R) in
/-- Maps from the null-sequence module tensored with the free module on `S` correspond to
sections over `S ⊗ C` vanishing over `S ⊗ {∞}`, where `C` is the convergent sequence. -/
noncomputable def nullSeqTensorFreeHomEquiv (S : LightProfinite.{u}) (B : LightCondMod.{u} R) :
    (nullSeq R ⊗ (free R).obj S.toCondensed ⟶ B) ≃+
      (B.obj.map (S ◁ inftyPoint.{u}).op).hom.toAddMonoidHom.ker :=
  let braid : (nullSeq R ⊗ (free R).obj S.toCondensed ⟶ B) ≃+
      ((free R).obj S.toCondensed ⊗ nullSeq R ⟶ B) :=
    { toFun g := (β_ _ _).hom ≫ g
      invFun g := (β_ _ _).inv ≫ g
      left_inv g := by simp
      right_inv g := by simp
      map_add' g h := by simp }
  have mem_ker_iff
      (y : ((ihom ((free R).obj S.toCondensed)).obj B).obj.obj (op liftedSequence.{u})) :
      y ∈ (((ihom ((free R).obj S.toCondensed)).obj B).obj.map
        inftyPoint.{u}.op).hom.toAddMonoidHom.ker ↔
        ihomFreeSectionsEquiv S liftedSequence.{u} B y ∈
          (B.obj.map (S ◁ inftyPoint.{u}).op).hom.toAddMonoidHom.ker := by
    simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, ← ihomFreeSectionsEquiv_map,
      AddEquivClass.map_eq_zero_iff]
  let restrict : (((ihom ((free R).obj S.toCondensed)).obj B).obj.map
      inftyPoint.{u}.op).hom.toAddMonoidHom.ker ≃+
      (B.obj.map (S ◁ inftyPoint.{u}).op).hom.toAddMonoidHom.ker :=
    { toEquiv := (ihomFreeSectionsEquiv S liftedSequence.{u} B).toEquiv.subtypeEquiv mem_ker_iff
      map_add' y z :=
        Subtype.ext (map_add (ihomFreeSectionsEquiv S liftedSequence.{u} B) y.val z.val) }
  braid.trans <| ((ihom.adjunction _).homAddEquiv _ _).trans <|
    (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) _).trans restrict

/-- The section of a map is computed by currying it after the braiding. -/
lemma nullSeqTensorFreeHomEquiv_apply_val (S : LightProfinite.{u}) (B : LightCondMod.{u} R)
    (g : nullSeq R ⊗ (free R).obj S.toCondensed ⟶ B) :
    (nullSeqTensorFreeHomEquiv R S B g).val = ihomFreeSectionsEquiv S liftedSequence.{u} B
      (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) _ (curry ((β_ _ _).hom ≫ g))).val :=
  (rfl)

/-- Precomposition with the null shift restricts the section along successor on the sequence. -/
@[simp↓]
lemma nullSeqTensorFreeHomEquiv_nullShift_val (S : LightProfinite.{u}) (B : LightCondMod.{u} R)
    (g : nullSeq R ⊗ (free R).obj S.toCondensed ⟶ B) :
    (nullSeqTensorFreeHomEquiv R S B (nullShift R ▷ _ ≫ g)).val =
      B.obj.map (S ◁ natShift.{u}).op (nullSeqTensorFreeHomEquiv R S B g).val := by
  rw [nullSeqTensorFreeHomEquiv_apply_val, nullSeqTensorFreeHomEquiv_apply_val,
    ← ihomFreeSectionsEquiv_map, ← reducedLightFreeHomEquiv_nullShift_val, ← curry_natural_left,
    BraidedCategory.braiding_naturality_right_assoc]

end TauCeti
