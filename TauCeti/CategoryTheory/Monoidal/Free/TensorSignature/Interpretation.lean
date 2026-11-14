/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import TauCeti.CategoryTheory.Monoidal.Free.ProjectObj
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Interpretations of a tensor signature

An interpretation of a tensor signature `S` in a monoidal category `D` assigns an object of `D`
to every generating object and, to every coupon, a morphism between the interpretations of its
source and target words. A morphism of interpretations is a family of isomorphisms of the
generating objects which commutes with the coupons, after extension to tensor words by
`CategoryTheory.FreeMonoidalCategory.projectObjIso`. Interpretations and their morphisms form a
groupoid `TauCeti.TensorSignature.Interpretation S D`.

Restricting a strong monoidal functor out of the free monoidal category `S.FreeMonoidal` to the
generators gives an interpretation, and `FreeMonoidal.lift` extends an interpretation to such a
functor. The main result is that restriction and extension are inverse equivalences between the
groupoid of interpretations and the groupoid of strong monoidal functors
`S.FreeMonoidal ⥤ D` and monoidal natural isomorphisms. Neither the target nor the functors are
assumed strict.

## Main definitions and results

* `TensorSignature.Interpretation S D`: the groupoid of interpretations of `S` in `D`.
* `TensorSignature.FreeMonoidal.mapWordIso F X`: the comparison between the image of a tensor
  word under a strong monoidal functor `F` and the word interpreted on the images of the
  generators, built from the tensorators and the unit comparison of `F`.
* `TensorSignature.FreeMonoidal.wordIso_eq_mapWordIso`: the isomorphisms `FreeMonoidal.wordIso`
  between two strong monoidal functors factor through these comparisons.
* `TensorSignature.FreeMonoidal.wordIso_app`: a monoidal natural isomorphism out of the free
  monoidal category is the `wordIso` of its components at the generating objects.
* `TensorSignature.Interpretation.extension` and `TensorSignature.Interpretation.restriction`:
  extension of interpretations and restriction of strong monoidal functors.
* `TensorSignature.Interpretation.equivCoreMonoidalFunctor`: the equivalence of groupoids
  between interpretations of `S` in `D` and strong monoidal functors `S.FreeMonoidal ⥤ D`.

This is the universal property of the free monoidal category on a tensor scheme in its
groupoid form (Joyal–Street, *The geometry of tensor calculus I*, §1).

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991).
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v}) (D : Type u') [Category.{v'} D] [MonoidalCategory D]

/-- An interpretation of a tensor signature `S` in a monoidal category `D`: an object for every
generating object and, for every coupon, a morphism between the interpretations of its source
and target words. -/
structure Interpretation where
  /-- The interpretations of the generating objects. -/
  obj : S.Obj → D
  /-- The interpretations of the coupons. -/
  coupon (g : S.Coupon) : projectObj obj (S.src g) ⟶ projectObj obj (S.tgt g)

namespace Interpretation

variable {S D}

/-- A morphism of interpretations: isomorphisms of the interpretations of the generating objects
which commute with the interpretations of the coupons, after extension to tensor words. -/
@[ext]
structure Hom (I J : Interpretation S D) where
  /-- The isomorphisms between the interpretations of the generating objects. -/
  iso (a : S.Obj) : I.obj a ≅ J.obj a
  /-- Compatibility with the coupons. -/
  comm (g : S.Coupon) :
    I.coupon g ≫ (projectObjIso iso (S.tgt g)).hom = (projectObjIso iso (S.src g)).hom ≫ J.coupon g

/-- The groupoid of interpretations of `S` in `D`. -/
instance : Groupoid (Interpretation S D) where
  Hom := Hom
  id I := ⟨fun a ↦ Iso.refl (I.obj a), fun g ↦ by simp⟩
  comp φ ψ := ⟨fun a ↦ φ.iso a ≪≫ ψ.iso a, fun g ↦ by simp [reassoc_of% φ.comm, ψ.comm]⟩
  inv φ := ⟨fun a ↦ (φ.iso a).symm, fun g ↦ by
    rw [projectObjIso_symm, projectObjIso_symm, Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq,
      Category.assoc, Iso.eq_inv_comp, φ.comm]⟩
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

namespace FreeMonoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {S D}

/-- The comparison between the image of a tensor word under a strong monoidal functor `F` out of
the free monoidal category and the word interpreted on the images of the generating objects,
built from the tensorators and the unit comparison of `F`. -/
def mapWordIso (F : S.FreeMonoidal ⥤ D) [F.Monoidal] :
    ∀ X : FreeMonoidalCategory S.Obj, F.obj ⟨X⟩ ≅ projectObj (fun a ↦ F.obj (of a)) X
  | .of _ => Iso.refl _
  | .unit => (Functor.Monoidal.εIso F).symm
  | .tensor X Y => (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (mapWordIso F X ⊗ᵢ mapWordIso F Y)

section mapWordIso

variable (F : S.FreeMonoidal ⥤ D) [F.Monoidal]

@[simp]
theorem mapWordIso_of (a : S.Obj) : mapWordIso F (of a).as = Iso.refl (F.obj (of a)) :=
  (rfl)

@[simp]
theorem mapWordIso_tensorUnit_hom : (mapWordIso F (𝟙_ S.FreeMonoidal).as).hom = η F :=
  (rfl)

@[simp]
theorem mapWordIso_tensor_hom (X Y : S.FreeMonoidal) :
    (mapWordIso F (X ⊗ Y).as).hom =
      δ F X Y ≫ ((mapWordIso F X.as).hom ⊗ₘ (mapWordIso F Y.as).hom) :=
  (rfl)

end mapWordIso

/-- For the strong monoidal functor `lift fo fc`, whose tensorators and unit comparison are
identities, the comparison `mapWordIso` is the identity. -/
@[simp]
theorem mapWordIso_lift (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))
    (X : FreeMonoidalCategory S.Obj) : mapWordIso (lift fo fc) X = Iso.refl (projectObj fo X) := by
  ext
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY =>
    refine (mapWordIso_tensor_hom (lift fo fc) ⟨X⟩ ⟨Y⟩).trans ?_
    dsimp only
    rw [hX, hY, Iso.refl_hom, Iso.refl_hom]
    -- The tensorator of `lift fo fc` is the identity (`lift_δ`), but its source and target are
    -- only definitionally equal to `projectObj fo X ⊗ projectObj fo Y`, so `rw` cannot use it.
    exact (Category.id_comp _).trans (id_tensorHom_id _ _)

/-- The isomorphisms `wordIso F G e` between two strong monoidal functors out of the free monoidal
category are the comparisons `mapWordIso` composed with the extension of `e` to tensor words. -/
theorem wordIso_eq_mapWordIso (F G : S.FreeMonoidal ⥤ D) [F.Monoidal] [G.Monoidal]
    (e : ∀ a, F.obj (of a) ≅ G.obj (of a)) (X : FreeMonoidalCategory S.Obj) :
    wordIso F G e X = mapWordIso F X ≪≫ projectObjIso e X ≪≫ (mapWordIso G X).symm := by
  ext
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  induction X with
  | of a =>
    refine (congrArg Iso.hom (wordIso_of F G e a)).trans ?_
    dsimp only [mapWordIso, projectObjIso, Iso.refl_hom, Iso.refl_inv]
    -- The identities are typed at `F.obj ⟨.of a⟩`, which is `F.obj (of a)` only after unfolding
    -- `of`, so `simp` cannot cancel them.
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  | unit =>
    refine (wordIso_tensorUnit_hom F G e).trans ?_
    dsimp only [mapWordIso, projectObjIso, projectObj]
    simp
  | tensor X Y hX hY =>
    refine (wordIso_tensor_hom F G e ⟨X⟩ ⟨Y⟩).trans ?_
    -- Unfolding `projectObj` at the tensor word aligns the objects of the composites.
    dsimp only [mapWordIso, projectObjIso, projectObj] at hX hY ⊢
    rw [hX, hY]
    simp

/-- A monoidal natural isomorphism between strong monoidal functors out of the free monoidal
category is the `wordIso` of its components at the generating objects. -/
theorem wordIso_app {F G : S.FreeMonoidal ⥤ D} [F.Monoidal] [G.Monoidal] (α : F ≅ G)
    [NatTrans.IsMonoidal α.hom] (X : FreeMonoidalCategory S.Obj) :
    wordIso F G (fun a ↦ α.app (of a)) X = α.app ⟨X⟩ := by
  ext
  induction X with
  | of a => exact congrArg Iso.hom (wordIso_of F G _ a)
  | unit =>
    refine (wordIso_tensorUnit_hom F G _).trans ?_
    rw [← NatTrans.IsMonoidal.unit (τ := α.hom), Functor.Monoidal.η_ε_assoc, Iso.app_hom]
    -- `𝟙_ S.FreeMonoidal` is `⟨.unit⟩` by definition.
    rfl
  | tensor X Y hX hY =>
    refine (wordIso_tensor_hom F G _ ⟨X⟩ ⟨Y⟩).trans ?_
    dsimp only
    rw [hX, hY, Iso.app_hom, Iso.app_hom, ← NatTrans.IsMonoidal.tensor,
      Functor.Monoidal.δ_μ_assoc, Iso.app_hom]
    -- `⟨X⟩ ⊗ ⟨Y⟩` is `⟨X.tensor Y⟩` by definition.
    rfl

/-- Between two lifts, `wordIso` is the extension of the isomorphisms of generators to tensor
words. -/
@[simp]
theorem wordIso_lift_lift {fo fo' : S.Obj → D}
    (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))
    (fc' : ∀ g : S.Coupon, projectObj fo' (S.src g) ⟶ projectObj fo' (S.tgt g))
    (e : ∀ a, fo a ≅ fo' a) (X : FreeMonoidalCategory S.Obj) :
    wordIso (lift fo fc) (lift fo' fc') e X = projectObjIso e X := by
  refine (wordIso_eq_mapWordIso (lift fo fc) (lift fo' fc') e X).trans ?_
  ext
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, mapWordIso_lift, mapWordIso_lift]
  -- The identities are typed at `projectObj (fun a ↦ (lift fo fc).obj (of a)) X`, which is only
  -- definitionally `projectObj fo X`, so `simp` cannot cancel them.
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- From the lift of the generator images of `F` to `F`, `wordIso` of the identities is the
inverse of the comparison `mapWordIso F`. -/
theorem wordIso_lift_refl (F : S.FreeMonoidal ⥤ D) [F.Monoidal]
    (fc : ∀ g : S.Coupon, projectObj (fun a ↦ F.obj (of a)) (S.src g) ⟶
      projectObj (fun a ↦ F.obj (of a)) (S.tgt g)) (X : FreeMonoidalCategory S.Obj) :
    wordIso (lift (fun a ↦ F.obj (of a)) fc) F (fun a ↦ Iso.refl (F.obj (of a))) X =
      (mapWordIso F X).symm := by
  ext
  -- In each case the tensorator or unit comparison of `lift _ fc` contributes an identity typed
  -- at the objects of `lift _ fc`, which agree with those of `F` only definitionally; the
  -- remaining composites coincide after unfolding `mapWordIso`.
  induction X with
  | of a => exact congrArg Iso.hom (wordIso_of _ F _ a)
  | unit => exact (wordIso_tensorUnit_hom _ F _).trans (Category.id_comp _)
  | tensor X Y hX hY =>
    refine (wordIso_tensor_hom _ F _ ⟨X⟩ ⟨Y⟩).trans ?_
    dsimp only
    rw [hX, hY]
    exact Category.id_comp _

/-- The extension to tensor words of the components of a monoidal natural isomorphism at the
generating objects is its component at the word, conjugated by the comparisons `mapWordIso`. -/
theorem projectObjIso_app {F G : S.FreeMonoidal ⥤ D} [F.Monoidal] [G.Monoidal] (α : F ≅ G)
    [NatTrans.IsMonoidal α.hom] (X : FreeMonoidalCategory S.Obj) :
    projectObjIso (fun a ↦ α.app (of a)) X =
      (mapWordIso F X).symm ≪≫ α.app ⟨X⟩ ≪≫ mapWordIso G X := by
  rw [← wordIso_app α X, wordIso_eq_mapWordIso]
  ext
  simp

end FreeMonoidal

namespace Interpretation

open FreeMonoidal

variable {S D} in
/-- A morphism of interpretations commutes with the coupons through the `wordIso` of the lifts.
This is the hypothesis of `FreeMonoidal.monoidalNatIso` for the lifts. -/
theorem lift_map_coupon_comp_wordIso_hom {I J : Interpretation S D} (φ : I ⟶ J)
    (g : S.Coupon) : (lift I.obj I.coupon).map (FreeMonoidal.coupon g) ≫
      (wordIso (lift I.obj I.coupon) (lift J.obj J.coupon) φ.iso (S.tgt g)).hom =
      (wordIso (lift I.obj I.coupon) (lift J.obj J.coupon) φ.iso (S.src g)).hom ≫
        (lift J.obj J.coupon).map (FreeMonoidal.coupon g) := by
  rw [wordIso_lift_lift, wordIso_lift_lift, lift_map_coupon, lift_map_coupon]
  exact φ.comm g

/-- Extension of interpretations of `S` to strong monoidal functors out of the free monoidal
category, by `FreeMonoidal.lift`, and of their morphisms to monoidal natural isomorphisms, by
`FreeMonoidal.monoidalNatIso`. -/
@[expose, simps obj_of]
def extension : Interpretation S D ⥤ Core (MonoidalFunctor S.FreeMonoidal D) where
  obj I := ⟨.of (lift I.obj I.coupon)⟩
  -- Instance search cannot unify the type of `φ.iso` with the objects of the lifts, so the
  -- monoidality of `monoidalNatIso` is supplied explicitly.
  map φ := ⟨@MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) (.of _)
    (monoidalNatIso (lift_map_coupon_comp_wordIso_hom φ))
    (isMonoidal_monoidalNatIso_hom (lift_map_coupon_comp_wordIso_hom φ))⟩
  map_id _ := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦
    monoidalNatIso_hom_app_of _ a
  map_comp φ ψ := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦
    (monoidalNatIso_hom_app_of _ a).trans <| congrArg₂ (· ≫ ·)
      (monoidalNatIso_hom_app_of (lift_map_coupon_comp_wordIso_hom φ) a).symm
      (monoidalNatIso_hom_app_of (lift_map_coupon_comp_wordIso_hom ψ) a).symm

variable {S D} in
/-- The components of the extension of a morphism of interpretations are the extensions of its
isomorphisms to tensor words. -/
@[simp]
theorem extension_map_iso_hom_hom_app {I J : Interpretation S D} (φ : I ⟶ J)
    (X : S.FreeMonoidal) :
    ((extension S D).map φ).iso.hom.hom.app X = (projectObjIso φ.iso X.as).hom :=
  (monoidalNatIso_hom_app _ X).trans (congrArg Iso.hom (wordIso_lift_lift _ _ φ.iso X.as))

/-- Restriction of strong monoidal functors out of the free monoidal category to interpretations
of `S`: the images of the generating objects, and the images of the coupons conjugated by the
comparisons `FreeMonoidal.mapWordIso`. Monoidal natural isomorphisms restrict to their
components at the generating objects. -/
@[expose, simps obj_obj obj_coupon map_iso]
def restriction : Core (MonoidalFunctor S.FreeMonoidal D) ⥤ Interpretation S D where
  obj F :=
    { obj a := F.of.obj (of a)
      coupon g := (mapWordIso F.of.toFunctor (S.src g)).inv ≫ F.of.map (FreeMonoidal.coupon g) ≫
        (mapWordIso F.of.toFunctor (S.tgt g)).hom }
  map {F G} α :=
    { iso a := (MonoidalFunctor.toFunctorIso α.iso).app (of a)
      comm g := by
        rw [projectObjIso_app, projectObjIso_app]
        simp }
  map_id F := hom_ext fun a ↦ rfl
  map_comp α β := hom_ext fun a ↦ rfl

variable {S D} in
/-- Restricting the extension of an interpretation gives back its coupons. -/
theorem restriction_obj_extension_obj_coupon (I : Interpretation S D) (g : S.Coupon) :
    ((restriction S D).obj ((extension S D).obj I)).coupon g = I.coupon g := by
  -- The restricted coupon is stated for the objects of the restriction; `change` exposes it as
  -- the conjugate of the coupon of `lift I.obj I.coupon`, whose objects are those of `I` only
  -- after unfolding `lift`, so `rw` cannot reach this form.
  change (mapWordIso (lift I.obj I.coupon) (S.src g)).inv ≫
    (lift I.obj I.coupon).map (FreeMonoidal.coupon g) ≫
      (mapWordIso (lift I.obj I.coupon) (S.tgt g)).hom = I.coupon g
  rw [mapWordIso_lift, mapWordIso_lift, lift_map_coupon, Iso.refl_inv, Iso.refl_hom]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The unit of the equivalence: restricting the extension of an interpretation gives back the
interpretation. -/
def unitIso : 𝟭 (Interpretation S D) ≅ extension S D ⋙ restriction S D :=
  NatIso.ofComponents
    (fun I ↦ (Groupoid.isoEquivHom _ _).symm ⟨fun a ↦ Iso.refl (I.obj a), fun g ↦ by
      have h (X : FreeMonoidalCategory S.Obj) :
          (projectObjIso (g := ((restriction S D).obj ((extension S D).obj I)).obj)
            (fun a ↦ Iso.refl (I.obj a)) X).hom = 𝟙 (projectObj I.obj X) :=
        congrArg Iso.hom (projectObjIso_refl X)
      rw [h, h]
      -- The identities are typed at the objects of `I`, which are those of the restriction of its
      -- extension only after unfolding `lift`.
      exact (Category.comp_id _).trans
        ((restriction_obj_extension_obj_coupon I g).symm.trans (Category.id_comp _).symm)⟩)
    fun φ ↦ hom_ext fun a ↦
      (Category.comp_id _).trans
        ((extension_map_iso_hom_hom_app φ (of a)).symm.trans (Category.id_comp _).symm)

/-- The coupons of the lift of the restriction of a strong monoidal functor `F` commute with those
of `F` through the identities of the generating objects: the hypothesis of
`FreeMonoidal.monoidalNatIso` for the counit of the equivalence. -/
private theorem lift_map_coupon_comp_wordIso_refl_hom {S : TensorSignature.{u, v}} {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] (F : S.FreeMonoidal ⥤ D) [F.Monoidal]
    (g : S.Coupon) :
    (lift (fun a ↦ F.obj (of a)) fun g ↦ (mapWordIso F (S.src g)).inv ≫
        F.map (FreeMonoidal.coupon g) ≫ (mapWordIso F (S.tgt g)).hom).map
        (FreeMonoidal.coupon g) ≫
      (wordIso (lift (fun a ↦ F.obj (of a)) fun g ↦ (mapWordIso F (S.src g)).inv ≫
        F.map (FreeMonoidal.coupon g) ≫ (mapWordIso F (S.tgt g)).hom) F
        (fun a ↦ Iso.refl (F.obj (of a))) (S.tgt g)).hom =
      (wordIso (lift (fun a ↦ F.obj (of a)) fun g ↦ (mapWordIso F (S.src g)).inv ≫
        F.map (FreeMonoidal.coupon g) ≫ (mapWordIso F (S.tgt g)).hom) F
        (fun a ↦ Iso.refl (F.obj (of a))) (S.src g)).hom ≫ F.map (FreeMonoidal.coupon g) := by
  rw [← Iso.eq_comp_inv, Category.assoc, wordIso_lift_refl, wordIso_lift_refl]
  exact lift_map_coupon _ _ g

variable {S D} in
/-- The component of the counit of the equivalence at a strong monoidal functor `F`: the
monoidal natural isomorphism from the extension of the restriction of `F` to `F` which is the
identity at the generating objects. -/
private def counitApp (F : Core (MonoidalFunctor S.FreeMonoidal D)) :
    (extension S D).obj ((restriction S D).obj F) ≅ F :=
  -- As for `extension`, the monoidality of `monoidalNatIso` is supplied explicitly.
  Core.isoMk <| @MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) F.of
    (monoidalNatIso (lift_map_coupon_comp_wordIso_refl_hom F.of.toFunctor))
    (isMonoidal_monoidalNatIso_hom (lift_map_coupon_comp_wordIso_refl_hom F.of.toFunctor))

variable {S D} in
private theorem counitApp_hom_iso_hom_hom_app_of (F : Core (MonoidalFunctor S.FreeMonoidal D))
    (a : S.Obj) : (counitApp F).hom.iso.hom.hom.app (of a) = 𝟙 (F.of.obj (of a)) :=
  monoidalNatIso_hom_app_of _ a

/-- The counit of the equivalence: the extension of the restriction of a strong monoidal functor
is isomorphic to it, by the identities at the generating objects. -/
def counitIso : restriction S D ⋙ extension S D ≅ 𝟭 (Core (MonoidalFunctor S.FreeMonoidal D)) :=
  NatIso.ofComponents counitApp fun α ↦ Core.hom_ext <| MonoidalFunctor.hom_ext <|
    natTrans_ext fun a ↦ by
      simp only [Functor.comp_map, Functor.id_map, coreCategory_comp_iso, Iso.trans_hom,
        MonoidalFunctor.comp_hom, NatTrans.comp_app, extension_map_iso_hom_hom_app,
        counitApp_hom_iso_hom_hom_app_of]
      -- The extension of the restriction of `α` at a generating object is the component of `α`,
      -- by unfolding `projectObjIso` there; the identities are typed at objects of the lift.
      exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The universal property of the free monoidal category on a tensor signature**, in its groupoid
form: extension and restriction are inverse equivalences between the interpretations of `S` in
`D` and the strong monoidal functors `S.FreeMonoidal ⥤ D` with monoidal natural isomorphisms. -/
@[expose, simps! functor inverse]
def equivCoreMonoidalFunctor : Interpretation S D ≌ Core (MonoidalFunctor S.FreeMonoidal D) :=
  .mk (extension S D) (restriction S D) (unitIso S D) (counitIso S D)

end Interpretation

end TauCeti.TensorSignature
