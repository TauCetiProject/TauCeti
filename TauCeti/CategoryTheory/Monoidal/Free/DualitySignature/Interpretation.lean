/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Basic
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Interpretations of a duality signature

An interpretation of a duality signature `S` in a rigid monoidal category `D` assigns an object of
`D` to every generating object and, to every coupon, a morphism between the evaluations
(`TauCeti.RigidObject.eval`) of its source and target, which are formal rigid objects: their
formal duals are read as the chosen duals of `D`. A morphism of interpretations is a family of
isomorphisms of the generating objects which commutes with the coupons, after extension to
formal rigid objects by `TauCeti.RigidObject.evalIso`; at a dual this extension is the adjoint
mate of the inverse isomorphism. Interpretations and their morphisms form a groupoid
`TauCeti.DualitySignature.Interpretation S D`.

Restricting a strong monoidal functor out of the free rigid monoidal category `S.FreeRigid` to the
generators gives an interpretation, and `FreeRigid.lift` extends an interpretation to such a
functor. The main result is that restriction and extension are inverse equivalences between the
groupoid of interpretations and the groupoid of strong monoidal functors `S.FreeRigid ⥤ D` and
monoidal natural isomorphisms. Neither the target nor the functors are assumed strict, and no
pivotal structure is involved. Strong monoidal functors preserve duals up to the canonical
comparisons `CategoryTheory.Functor.mapRightDualIso` and `CategoryTheory.Functor.mapLeftDualIso`,
so no separate preservation condition on duals is imposed.

## Main definitions and results

* `DualitySignature.Interpretation S D`: the groupoid of interpretations of `S` in `D`.
* `DualitySignature.Interpretation.extension` and `DualitySignature.Interpretation.restriction`:
  extension of interpretations and restriction of strong monoidal functors.
* `DualitySignature.Interpretation.equivCoreMonoidalFunctor`: the equivalence of groupoids
  between interpretations of `S` in `D` and strong monoidal functors `S.FreeRigid ⥤ D`.

This is the universal property of the free autonomous category on an autonomous tensor scheme in
its groupoid form (Joyal–Street, *Planar diagrams and tensor algebra*, §2). The construction
follows the corresponding statement for tensor signatures,
`TauCeti.TensorSignature.Interpretation.equivCoreMonoidalFunctor`.

## References

* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, unpublished manuscript (1988), §2.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §4.1.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory

namespace TauCeti.DualitySignature

variable (S : DualitySignature.{u, v}) (D : Type u') [Category.{v'} D] [MonoidalCategory D]
  [RigidCategory D]

/-- An interpretation of a duality signature `S` in a rigid monoidal category `D`: an object for
every generating object and, for every coupon, a morphism between the evaluations of its source
and target at these objects. -/
structure Interpretation where
  /-- The interpretations of the generating objects. -/
  obj : S.Obj → D
  /-- The interpretations of the coupons. -/
  coupon (g : S.Coupon) : RigidObject.eval obj (S.src g) ⟶ RigidObject.eval obj (S.tgt g)

namespace Interpretation

variable {S D}

/-- A morphism of interpretations: isomorphisms of the interpretations of the generating objects
which commute with the interpretations of the coupons, after extension to formal rigid objects by
`RigidObject.evalIso`. -/
@[ext]
structure Hom (I J : Interpretation S D) where
  /-- The isomorphisms between the interpretations of the generating objects. -/
  iso (a : S.Obj) : I.obj a ≅ J.obj a
  /-- Compatibility with the coupons. -/
  comm (g : S.Coupon) :
    I.coupon g ≫ (RigidObject.evalIso iso (S.tgt g)).hom =
      (RigidObject.evalIso iso (S.src g)).hom ≫ J.coupon g

/-- The groupoid of interpretations of `S` in `D`. -/
instance : Groupoid (Interpretation S D) where
  Hom := Hom
  id I := ⟨fun a ↦ Iso.refl (I.obj a), fun g ↦ by simp⟩
  comp φ ψ := ⟨fun a ↦ φ.iso a ≪≫ ψ.iso a, fun g ↦ by simp [reassoc_of% φ.comm, ψ.comm]⟩
  inv φ := ⟨fun a ↦ (φ.iso a).symm, fun g ↦ by
    rw [RigidObject.evalIso_symm, RigidObject.evalIso_symm, Iso.symm_hom, Iso.symm_hom,
      Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, φ.comm]⟩
  inv_comp φ := Hom.ext (funext fun a ↦ (φ.iso a).symm_self_id)
  comp_inv φ := Hom.ext (funext fun a ↦ (φ.iso a).self_symm_id)

@[ext]
theorem hom_ext {I J : Interpretation S D} {φ ψ : I ⟶ J} (h : ∀ a, (φ.iso a).hom = (ψ.iso a).hom) :
    φ = ψ :=
  Hom.ext (funext fun a ↦ Iso.ext (h a))

@[simp]
theorem id_iso (I : Interpretation S D) (a : S.Obj) : Hom.iso (𝟙 I) a = Iso.refl (I.obj a) :=
  (rfl)

@[simp]
theorem comp_iso {I J K : Interpretation S D} (φ : I ⟶ J) (ψ : J ⟶ K) (a : S.Obj) :
    (φ ≫ ψ).iso a = φ.iso a ≪≫ ψ.iso a :=
  (rfl)

@[simp]
theorem inv_iso {I J : Interpretation S D} (φ : I ⟶ J) (a : S.Obj) :
    (inv φ).iso a = (φ.iso a).symm := by
  rw [← Groupoid.inv_eq_inv]
  rfl

end Interpretation

namespace Interpretation

open FreeRigid

variable {S D} in
/-- A morphism of interpretations commutes with the coupons through the `wordIso` of the lifts.
This is the hypothesis of `FreeRigid.monoidalNatIso` for the lifts. -/
theorem lift_map_coupon_comp_wordIso_hom {I J : Interpretation S D} (φ : I ⟶ J)
    (g : S.Coupon) : (lift I.obj I.coupon).map (FreeRigid.coupon g) ≫
      (wordIso (lift I.obj I.coupon) (lift J.obj J.coupon) φ.iso (S.tgt g)).hom =
      (wordIso (lift I.obj I.coupon) (lift J.obj J.coupon) φ.iso (S.src g)).hom ≫
        (lift J.obj J.coupon).map (FreeRigid.coupon g) := by
  rw [wordIso_lift_lift, wordIso_lift_lift, lift_map_coupon, lift_map_coupon]
  exact φ.comm g

/-- Extension of interpretations of `S` to strong monoidal functors out of the free rigid monoidal
category, by `FreeRigid.lift`, and of their morphisms to monoidal natural isomorphisms, by
`FreeRigid.monoidalNatIso`. -/
@[expose, simps obj_of]
def extension : Interpretation S D ⥤ Core (MonoidalFunctor S.FreeRigid D) where
  obj I := ⟨.of (lift I.obj I.coupon)⟩
  -- Instance search cannot unify the type of `φ.iso` with the objects of the lifts, so the
  -- monoidality of `monoidalNatIso` is supplied explicitly.
  map φ := ⟨@MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) (.of _)
    (monoidalNatIso (lift_map_coupon_comp_wordIso_hom φ))
    (isMonoidal_monoidalNatIso_hom (lift_map_coupon_comp_wordIso_hom φ))⟩
  -- `simp` cannot use `MonoidalFunctor.isoMk_hom` on these components, as their monoidality is
  -- supplied explicitly. By definition of `Core`, `isoMk` and `homMk`, the components at the
  -- generating objects are those of `monoidalNatIso`, given by `monoidalNatIso_hom_app_of`.
  map_id _ := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦
    monoidalNatIso_hom_app_of _ a
  map_comp φ ψ := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦
    (monoidalNatIso_hom_app_of _ a).trans <| congrArg₂ (· ≫ ·)
      (monoidalNatIso_hom_app_of (lift_map_coupon_comp_wordIso_hom φ) a).symm
      (monoidalNatIso_hom_app_of (lift_map_coupon_comp_wordIso_hom ψ) a).symm

variable {S D} in
/-- The components of the extension of a morphism of interpretations are the extensions of its
isomorphisms to formal rigid objects. -/
theorem extension_map_iso_hom_hom_hom_app {I J : Interpretation S D} (φ : I ⟶ J)
    (X : S.FreeRigid) :
    ((extension S D).map φ).iso.hom.hom.hom.app X = (RigidObject.evalIso φ.iso X.as).hom :=
  (monoidalNatIso_hom_app _ X).trans (congrArg Iso.hom (wordIso_lift_lift _ _ φ.iso X.as))

variable {S D} in
/-- The inverses of the components of the extension of a morphism of interpretations are the
inverses of the extensions of its isomorphisms to formal rigid objects. -/
theorem extension_map_iso_inv_hom_hom_app {I J : Interpretation S D} (φ : I ⟶ J)
    (X : S.FreeRigid) :
    ((extension S D).map φ).iso.inv.hom.hom.app X = (RigidObject.evalIso φ.iso X.as).inv := by
  rw [← MonoidalFunctor.toFunctorIso_inv, ← Iso.app_inv]
  exact congrArg Iso.inv (Iso.ext (extension_map_iso_hom_hom_hom_app φ X))

variable {S D} in
/-- The components of the extension of a morphism of interpretations at the generating objects
are its isomorphisms. -/
@[simp]
theorem extension_map_iso_hom_hom_hom_app_of {I J : Interpretation S D} (φ : I ⟶ J)
    (a : S.Obj) : ((extension S D).map φ).iso.hom.hom.hom.app (of a) = (φ.iso a).hom :=
  -- `(of a).as` is the formal rigid object `.of a` by definition.
  (extension_map_iso_hom_hom_hom_app φ (of a)).trans
    (congrArg Iso.hom (RigidObject.evalIso_of φ.iso a))

variable {S D} in
/-- The inverses of the components of the extension of a morphism of interpretations at the
generating objects are the inverses of its isomorphisms. -/
@[simp]
theorem extension_map_iso_inv_hom_hom_app_of {I J : Interpretation S D} (φ : I ⟶ J)
    (a : S.Obj) : ((extension S D).map φ).iso.inv.hom.hom.app (of a) = (φ.iso a).inv :=
  -- `(of a).as` is the formal rigid object `.of a` by definition.
  (extension_map_iso_inv_hom_hom_app φ (of a)).trans
    (congrArg Iso.inv (RigidObject.evalIso_of φ.iso a))

/-- Restriction of strong monoidal functors out of the free rigid monoidal category to
interpretations of `S`: the images of the generating objects, and the images of the coupons
conjugated by the comparisons `FreeRigid.mapWordIso`. Monoidal natural isomorphisms restrict to
their components at the generating objects. -/
@[expose, simps obj_obj obj_coupon map_iso]
noncomputable def restriction : Core (MonoidalFunctor S.FreeRigid D) ⥤ Interpretation S D where
  obj F :=
    { obj a := F.of.obj (of a)
      coupon g := (mapWordIso F.of.toFunctor (S.src g)).inv ≫ F.of.map (FreeRigid.coupon g) ≫
        (mapWordIso F.of.toFunctor (S.tgt g)).hom }
  map {F G} α :=
    { iso a := (MonoidalFunctor.toFunctorIso α.iso).app (of a)
      comm g := by
        rw [evalIso_app, evalIso_app]
        simp }
  map_id F := hom_ext fun a ↦ by simp
  map_comp α β := hom_ext fun a ↦ by simp

variable {S D} in
/-- Restricting the extension of an interpretation gives back its coupons. -/
theorem restriction_obj_extension_obj_coupon (I : Interpretation S D) (g : S.Coupon) :
    ((restriction S D).obj ((extension S D).obj I)).coupon g = I.coupon g := by
  -- The restricted coupon is stated for the objects of the restriction; `change` exposes it as
  -- the conjugate of the coupon of `lift I.obj I.coupon`, whose objects are those of `I` only
  -- after unfolding `lift`, so neither `rw` nor `dsimp` can reach this form.
  change (mapWordIso (lift I.obj I.coupon) (S.src g)).inv ≫
    (lift I.obj I.coupon).map (FreeRigid.coupon g) ≫
      (mapWordIso (lift I.obj I.coupon) (S.tgt g)).hom = I.coupon g
  rw [mapWordIso_lift, mapWordIso_lift, lift_map_coupon, Iso.refl_inv, Iso.refl_hom]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The unit of the equivalence: restricting the extension of an interpretation gives back the
interpretation. -/
noncomputable def unitIso : 𝟭 (Interpretation S D) ≅ extension S D ⋙ restriction S D :=
  NatIso.ofComponents
    (fun I ↦ (Groupoid.isoEquivHom _ _).symm ⟨fun a ↦ Iso.refl (I.obj a), fun g ↦ by
      have h (X : RigidObject S.Obj) :
          (RigidObject.evalIso (g := ((restriction S D).obj ((extension S D).obj I)).obj)
            (fun a ↦ Iso.refl (I.obj a)) X).hom = 𝟙 (RigidObject.eval I.obj X) :=
        congrArg Iso.hom (RigidObject.evalIso_refl X)
      rw [h, h]
      -- The identities are typed at the objects of `I`, which are those of the restriction of its
      -- extension only after unfolding `lift`.
      exact (Category.comp_id _).trans
        ((restriction_obj_extension_obj_coupon I g).symm.trans (Category.id_comp _).symm)⟩)
    -- The components of `restriction.map` and of identities and composites of interpretations are
    -- by definition the components at `of a` and the identities and composites of isomorphisms; the
    -- identities are typed at the objects of `I`, which are those of the restriction of its
    -- extension only after unfolding `lift`, so `simp` cannot cancel them.
    fun φ ↦ hom_ext fun a ↦
      (Category.comp_id _).trans
        ((extension_map_iso_hom_hom_hom_app_of φ a).symm.trans (Category.id_comp _).symm)

variable {S D} in
@[simp]
theorem unitIso_hom_app_iso (I : Interpretation S D) (a : S.Obj) :
    ((unitIso S D).hom.app I).iso a = Iso.refl (I.obj a) :=
  (rfl)

variable {S D} in
@[simp]
theorem unitIso_inv_app_iso (I : Interpretation S D) (a : S.Obj) :
    ((unitIso S D).inv.app I).iso a = Iso.refl (I.obj a) :=
  (rfl)

/-- The coupons of the lift of the restriction of a strong monoidal functor `F` commute with those
of `F` through the identities of the generating objects: the hypothesis of
`FreeRigid.monoidalNatIso` for the counit of the equivalence. -/
private theorem lift_map_coupon_comp_wordIso_refl_hom {S : DualitySignature.{u, v}}
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D] (F : S.FreeRigid ⥤ D)
    [F.Monoidal] (g : S.Coupon) :
    (lift (fun a ↦ F.obj (of a)) fun g ↦ (mapWordIso F (S.src g)).inv ≫
        F.map (FreeRigid.coupon g) ≫ (mapWordIso F (S.tgt g)).hom).map
        (FreeRigid.coupon g) ≫
      (wordIso (lift (fun a ↦ F.obj (of a)) fun g ↦ (mapWordIso F (S.src g)).inv ≫
        F.map (FreeRigid.coupon g) ≫ (mapWordIso F (S.tgt g)).hom) F
        (fun a ↦ Iso.refl (F.obj (of a))) (S.tgt g)).hom =
      (wordIso (lift (fun a ↦ F.obj (of a)) fun g ↦ (mapWordIso F (S.src g)).inv ≫
        F.map (FreeRigid.coupon g) ≫ (mapWordIso F (S.tgt g)).hom) F
        (fun a ↦ Iso.refl (F.obj (of a))) (S.src g)).hom ≫ F.map (FreeRigid.coupon g) := by
  rw [← Iso.eq_comp_inv, Category.assoc, wordIso_lift_refl, wordIso_lift_refl]
  exact lift_map_coupon _ _ g

variable {S D} in
/-- The component of the counit of the equivalence at a strong monoidal functor `F`: the
monoidal natural isomorphism from the extension of the restriction of `F` to `F` which is the
identity at the generating objects. -/
private noncomputable def counitApp (F : Core (MonoidalFunctor S.FreeRigid D)) :
    (extension S D).obj ((restriction S D).obj F) ≅ F :=
  -- As for `extension`, the monoidality of `monoidalNatIso` is supplied explicitly.
  Core.isoMk <| @MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) F.of
    (monoidalNatIso (lift_map_coupon_comp_wordIso_refl_hom F.of.toFunctor))
    (isMonoidal_monoidalNatIso_hom (lift_map_coupon_comp_wordIso_refl_hom F.of.toFunctor))

/-- The counit of the equivalence: the extension of the restriction of a strong monoidal functor
is isomorphic to it, by the identities at the generating objects. -/
noncomputable def counitIso :
    restriction S D ⋙ extension S D ≅ 𝟭 (Core (MonoidalFunctor S.FreeRigid D)) :=
  NatIso.ofComponents counitApp fun α ↦ Core.hom_ext <| MonoidalFunctor.hom_ext <|
    natTrans_ext fun a ↦ by
      have h (F : Core (MonoidalFunctor S.FreeRigid D)) :
          (counitApp F).hom.iso.hom.hom.hom.app (of a) = 𝟙 (F.of.obj (of a)) :=
        monoidalNatIso_hom_app_of _ a
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, coreCategory_comp_iso,
        Iso.trans_hom, MonoidalFunctor.comp_hom, LaxMonoidalFunctor.comp_hom, NatTrans.comp_app,
        extension_map_iso_hom_hom_hom_app_of, restriction_map_iso, Iso.app_hom,
        MonoidalFunctor.toFunctorIso_hom, h, Functor.id_map]
      -- The identities are typed at the objects of the source and target of `α`, which are those
      -- of the extensions of their restrictions only after unfolding `lift`.
      exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {S D} in
/-- The counit of the equivalence at a formal rigid object is the inverse of the comparison
`FreeRigid.mapWordIso`. -/
theorem counitIso_hom_app_iso_hom_hom_hom_app (F : Core (MonoidalFunctor S.FreeRigid D))
    (X : S.FreeRigid) :
    ((counitIso S D).hom.app F).iso.hom.hom.hom.app X = (mapWordIso F.of.toFunctor X.as).inv :=
  (monoidalNatIso_hom_app _ X).trans (congrArg Iso.hom (wordIso_lift_refl _ _ X.as))

variable {S D} in
/-- The inverse of the counit of the equivalence at a formal rigid object is the comparison
`FreeRigid.mapWordIso`. -/
theorem counitIso_hom_app_iso_inv_hom_hom_app (F : Core (MonoidalFunctor S.FreeRigid D))
    (X : S.FreeRigid) :
    ((counitIso S D).hom.app F).iso.inv.hom.hom.app X = (mapWordIso F.of.toFunctor X.as).hom := by
  rw [← MonoidalFunctor.toFunctorIso_inv, ← Iso.app_inv, ← Iso.symm_inv (mapWordIso _ _)]
  exact congrArg Iso.inv (Iso.ext (counitIso_hom_app_iso_hom_hom_hom_app F X))

variable {S D} in
/-- The counit of the equivalence is the identity at the generating objects. -/
@[simp]
theorem counitIso_hom_app_iso_hom_hom_hom_app_of (F : Core (MonoidalFunctor S.FreeRigid D))
    (a : S.Obj) :
    ((counitIso S D).hom.app F).iso.hom.hom.hom.app (of a) = 𝟙 (F.of.obj (of a)) :=
  -- `(of a).as` is the formal rigid object `.of a` by definition.
  (counitIso_hom_app_iso_hom_hom_hom_app F (of a)).trans
    ((congrArg Iso.inv (mapWordIso_of F.of.toFunctor a)).trans (Iso.refl_inv _))

variable {S D} in
/-- The inverse of the counit of the equivalence is the identity at the generating objects. -/
@[simp]
theorem counitIso_hom_app_iso_inv_hom_hom_app_of (F : Core (MonoidalFunctor S.FreeRigid D))
    (a : S.Obj) :
    ((counitIso S D).hom.app F).iso.inv.hom.hom.app (of a) = 𝟙 (F.of.obj (of a)) :=
  -- `(of a).as` is the formal rigid object `.of a` by definition.
  (counitIso_hom_app_iso_inv_hom_hom_app F (of a)).trans
    ((congrArg Iso.hom (mapWordIso_of F.of.toFunctor a)).trans (Iso.refl_hom _))

variable {S D} in
/-- The inverse of the counit of the equivalence is given by the inverse isomorphisms. -/
@[simp]
theorem counitIso_inv_app_iso (F : Core (MonoidalFunctor S.FreeRigid D)) :
    ((counitIso S D).inv.app F).iso = ((counitIso S D).hom.app F).iso.symm :=
  (rfl)

/-- **The universal property of the free rigid monoidal category on a duality signature**, in its
groupoid form: extension and restriction are inverse equivalences between the interpretations of
`S` in `D` and the strong monoidal functors `S.FreeRigid ⥤ D` with monoidal natural isomorphisms. -/
@[expose, simps functor inverse unitIso counitIso]
noncomputable def equivCoreMonoidalFunctor :
    Interpretation S D ≌ Core (MonoidalFunctor S.FreeRigid D) where
  functor := extension S D
  inverse := restriction S D
  unitIso := unitIso S D
  counitIso := counitIso S D
  functor_unitIso_comp _ := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦ by
    simp only [coreCategory_comp_iso, Iso.trans_hom, MonoidalFunctor.comp_hom,
      LaxMonoidalFunctor.comp_hom, NatTrans.comp_app, extension_map_iso_hom_hom_hom_app_of,
      unitIso_hom_app_iso, Iso.refl_hom, counitIso_hom_app_iso_hom_hom_hom_app_of,
      coreCategory_id_iso, MonoidalFunctor.id_hom, LaxMonoidalFunctor.id_hom, NatTrans.id_app]
    -- The first identity is typed at the object of the interpretation, which is that of its
    -- extension only after unfolding `lift`, so `simp` cannot cancel it.
    exact Category.id_comp _

end Interpretation

end TauCeti.DualitySignature
