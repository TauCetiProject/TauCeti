/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
public import TauCeti.CategoryTheory.Monoidal.EqToHom

/-!
# Functorial pullback of line bundles

Pulling back an invertible sheaf along an identity morphism leaves it unchanged, and pullback
along a composite agrees with successive pullback. These comparisons make the pullback operation
on isomorphism classes of line bundles contravariantly functorial. Pullback also preserves the
class of the trivial line bundle (`LineBundleClass.pullback_one`), through
the comparison `Scheme.Modules.pullbackObjUnitIso : f^* 𝒪_Y ≅ 𝒪_X`, and tensor products of line
bundles (`LineBundleClass.pullback_mul`), through the tensor comparison
`InvertibleSheaf.pullbackTensorProductIso : f^*(L ⊗ K) ≅ f^*L ⊗ f^*K`. On underlying sheaves this
is the oplax tensor comparison `δ` of module pullback, read through canonical identifications of
its source and target: on the source, the transport along `InvertibleSheaf.pullback_obj_obj` and
the pullback of `InvertibleSheaf.tensorProductObjIso L K`; on the target, the transports along
`InvertibleSheaf.pullback_obj_obj` on both factors and the inverse of `tensorProductObjIso`. The
comparison `δ` is the field `Functor.OplaxMonoidal.δ` of Mathlib's oplax monoidal functors, for
Tau Ceti's oplax monoidal structure `Scheme.Modules.pullbackOplaxMonoidal` on module pullback; it
is invertible because line bundles are quasicoherent
(`Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent`). So pullback is a homomorphism of Picard
groups (`LineBundleClass.pullbackHom`), as needed for the Picard functor `T ↦ Pic(X_T)`, a
`ℤ`-linear map on the additively written Picard groups (`LineBundleClass.pullbackLinearMap`), and an
isomorphism of schemes induces an equivalence of categories of line bundles
(`InvertibleSheaf.pullbackEquiv`) and a group isomorphism of Picard groups
(`LineBundleClass.pullbackEquiv`).

The identity and composition comparisons are restrictions of Mathlib's
`Scheme.Modules.pullbackId` and `Scheme.Modules.pullbackComp`. The tensor comparison is natural
with respect to isomorphisms in either factor, transported by `tensorProductCongrLeft` and
`tensorProductCongrRight` (`InvertibleSheaf.pullbackTensorProductIso_hom_naturality_left` and
`InvertibleSheaf.pullbackTensorProductIso_hom_naturality_right`), and compatible with the identity
and composition comparisons (`InvertibleSheaf.pullbackTensorProductIso_id` and
`InvertibleSheaf.pullbackTensorProductIso_comp`), through Tau Ceti's identities
`Scheme.Modules.pullback_id_δ` and `Scheme.Modules.pullback_comp_δ` of module pullback.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X Y Z : Scheme.{u}}

/-- Pullback of a line bundle along the identity morphism is naturally isomorphic to the
original line bundle. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (InvertibleSheaf X) :=
  NatIso.ofComponents (fun L ↦
    ObjectProperty.isoMk (SheafOfModules.isInvertible X)
      ((eqToIso (pullback_obj_obj (𝟙 X) L)) ≪≫
        (Scheme.Modules.pullbackId X).app L.obj)) (by
    intro L K f
    apply ObjectProperty.hom_ext
    simp [ObjectProperty.isoMk, ObjectProperty.homMk, pullback_map,
      Category.assoc, (Scheme.Modules.pullbackId X).hom.naturality f.hom])

/-- On underlying modules, the identity comparison is Mathlib's pullback identity comparison. -/
@[simp]
theorem pullbackId_hom_app_hom (X : Scheme.{u}) (L : InvertibleSheaf X) :
    ((pullbackId X).hom.app L).hom =
      eqToHom (pullback_obj_obj (𝟙 X) L) ≫ (Scheme.Modules.pullbackId X).hom.app L.obj := by
  simp only [pullbackId, NatIso.ofComponents_hom_app, ObjectProperty.isoMk_hom,
    Iso.trans_hom, eqToIso.hom, ObjectProperty.homMk_hom, Iso.app_hom]

/-- The inverse identity comparison on underlying modules is Mathlib's inverse comparison. -/
@[simp]
theorem pullbackId_inv_app_hom (X : Scheme.{u}) (L : InvertibleSheaf X) :
    ((pullbackId X).inv.app L).hom =
      (Scheme.Modules.pullbackId X).inv.app L.obj ≫ eqToHom (pullback_obj_obj (𝟙 X) L).symm := by
  simp only [pullbackId, NatIso.ofComponents_inv_app, ObjectProperty.isoMk_inv,
    Iso.trans_inv, eqToIso.inv, ObjectProperty.homMk_hom, Iso.app_inv]

/-- The underlying module of successive line-bundle pullbacks is the corresponding successive
module pullback. -/
private lemma pullbackComp_obj_obj (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((pullback g ⋙ pullback f).obj L).obj =
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj L.obj :=
  (pullback_obj_obj f ((pullback g).obj L)).trans
    (congrArg (Scheme.Modules.pullback f).obj (pullback_obj_obj g L))

/-- Pullback along a composite is naturally isomorphic to successive pullback of line
bundles. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents (fun L ↦
    ObjectProperty.isoMk (SheafOfModules.isInvertible X)
      ((eqToIso (pullbackComp_obj_obj f g L)) ≪≫
        (Scheme.Modules.pullbackComp f g).app L.obj ≪≫
        eqToIso (pullback_obj_obj (f ≫ g) L).symm)) (by
    intro L K φ
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.isoMk_hom,
      Iso.trans_hom, eqToIso.hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      pullback_map, Functor.map_comp, Category.assoc, ObjectProperty.homMk_hom,
      eqToHom_trans_assoc, eqToHom_refl, eqToHom_map, eqToHom_trans,
      Category.id_comp]
    -- The outer transports are shared; regroup inside them to apply module-pullback naturality.
    conv_lhs =>
      enter [2]
      rw [← Category.assoc]
    have h := (Scheme.Modules.pullbackComp f g).hom.naturality φ.hom
    simp only [Functor.comp_map] at h
    rw [h]
    simp only [Category.assoc])

/-- On underlying modules, the composition comparison is Mathlib's pullback composition
comparison. -/
@[simp]
theorem pullbackComp_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((pullbackComp f g).hom.app L).hom =
      eqToHom (by simp only [Functor.comp_obj, pullback_obj_obj]) ≫
        (Scheme.Modules.pullbackComp f g).hom.app L.obj ≫
        eqToHom (pullback_obj_obj (f ≫ g) L).symm := by
  simp only [pullbackComp, NatIso.ofComponents_hom_app, ObjectProperty.isoMk_hom,
    Iso.trans_hom, eqToIso.hom, ObjectProperty.homMk_hom, Iso.app_hom]

/-- The inverse composition comparison on underlying modules is Mathlib's inverse comparison. -/
@[simp]
theorem pullbackComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((pullbackComp f g).inv.app L).hom =
      eqToHom (pullback_obj_obj (f ≫ g) L) ≫ (Scheme.Modules.pullbackComp f g).inv.app L.obj ≫
        eqToHom (by simp only [Functor.comp_obj, pullback_obj_obj]) := by
  simp only [pullbackComp, NatIso.ofComponents_inv_app, ObjectProperty.isoMk_inv,
    Iso.trans_inv, eqToIso.inv, ObjectProperty.homMk_hom, Iso.app_inv, Category.assoc]

/-- **Pullback commutes with tensor products of line bundles**: `f^*(L ⊗ K) ≅ f^*L ⊗ f^*K`. On
underlying sheaves it is the oplax tensor comparison `δ` of module pullback, which is invertible
because line bundles are quasicoherent, preceded by the transport along `pullback_obj_obj` and the
pullback of `tensorProductObjIso L K`, and followed by the transports along `pullback_obj_obj` on
both factors and the inverse of `tensorProductObjIso` of the pulled-back line bundles. -/
def pullbackTensorProductIso (f : X ⟶ Y) (L K : InvertibleSheaf Y) :
    (pullback f).obj (tensorProduct L K) ≅
      tensorProduct ((pullback f).obj L) ((pullback f).obj K) :=
  ObjectProperty.isoMk _
    (eqToIso (pullback_obj_obj f (tensorProduct L K)) ≪≫
      (Scheme.Modules.pullback f).mapIso (tensorProductObjIso L K) ≪≫
      asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L.obj K.obj) ≪≫
      (eqToIso (pullback_obj_obj f L).symm ⊗ᵢ eqToIso (pullback_obj_obj f K).symm) ≪≫
      (tensorProductObjIso ((pullback f).obj L) ((pullback f).obj K)).symm)

/-- On underlying sheaves, `pullbackTensorProductIso` is the tensor comparison of module
pullback, read through `tensorProductObjIso` on both sides. -/
@[simp]
lemma pullbackTensorProductIso_hom_hom (f : X ⟶ Y) (L K : InvertibleSheaf Y) :
    (pullbackTensorProductIso f L K).hom.hom =
      eqToHom (pullback_obj_obj f (tensorProduct L K)) ≫
        (Scheme.Modules.pullback f).map (tensorProductObjIso L K).hom ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L.obj K.obj ≫
        (eqToHom (pullback_obj_obj f L).symm ⊗ₘ eqToHom (pullback_obj_obj f K).symm) ≫
        (tensorProductObjIso ((pullback f).obj L) ((pullback f).obj K)).inv := by
  simp [pullbackTensorProductIso]

/-- On underlying sheaves, the inverse of `pullbackTensorProductIso` is the inverse of the tensor
comparison of module pullback, read through `tensorProductObjIso` on both sides. -/
@[simp]
lemma pullbackTensorProductIso_inv_hom (f : X ⟶ Y) (L K : InvertibleSheaf Y) :
    (pullbackTensorProductIso f L K).inv.hom =
      (tensorProductObjIso ((pullback f).obj L) ((pullback f).obj K)).hom ≫
        (eqToHom (pullback_obj_obj f L) ⊗ₘ eqToHom (pullback_obj_obj f K)) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L.obj K.obj) ≫
        (Scheme.Modules.pullback f).map (tensorProductObjIso L K).inv ≫
        eqToHom (pullback_obj_obj f (tensorProduct L K)).symm := by
  simp [pullbackTensorProductIso]

/-- Postcomposing `pullbackTensorProductIso` with `tensorProductObjIso` removes the identification
of the target: the result is the tensor comparison `δ` of module pullback, still preceded by the
identification of the source (the transport along `pullback_obj_obj` and the pullback of
`tensorProductObjIso L K`) and followed by the transports along `pullback_obj_obj` on both
factors. -/
@[reassoc]
lemma pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom (f : X ⟶ Y)
    (L K : InvertibleSheaf Y) :
    (pullbackTensorProductIso f L K).hom.hom ≫
        (tensorProductObjIso ((pullback f).obj L) ((pullback f).obj K)).hom =
      eqToHom (pullback_obj_obj f (tensorProduct L K)) ≫
        (Scheme.Modules.pullback f).map (tensorProductObjIso L K).hom ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L.obj K.obj ≫
        (eqToHom (pullback_obj_obj f L).symm ⊗ₘ eqToHom (pullback_obj_obj f K).symm) := by
  simp [pullbackTensorProductIso_hom_hom]

/-- `pullbackTensorProductIso` is natural with respect to isomorphisms in the first factor,
transported through the tensor product by `tensorProductCongrLeft`. -/
@[reassoc]
lemma pullbackTensorProductIso_hom_naturality_left (f : X ⟶ Y)
    {L L' : InvertibleSheaf Y} (e : L ≅ L') (K : InvertibleSheaf Y) :
    (pullback f).map (tensorProductCongrLeft (K := K) e).hom ≫
        (pullbackTensorProductIso f L' K).hom =
      (pullbackTensorProductIso f L K).hom ≫
        (tensorProductCongrLeft (K := (pullback f).obj K) ((pullback f).mapIso e)).hom := by
  apply ObjectProperty.hom_ext
  rw [← cancel_mono (tensorProductObjIso ((pullback f).obj L') ((pullback f).obj K)).hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom,
    tensorProductCongrLeft_hom_hom_comp_tensorProductObjIso_hom,
    pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom_assoc, pullback_map,
    Functor.mapIso_hom]
  simp only [eqToHom_refl, Category.id_comp, eqToHom_trans_assoc, ← Functor.map_comp_assoc,
    tensorProductCongrLeft_hom_hom_comp_tensorProductObjIso_hom]
  rw [Functor.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
    whiskerRight_comp_tensorHom_eqToHom (pullback_obj_obj f L).symm]

/-- `pullbackTensorProductIso` is natural with respect to isomorphisms in the second factor,
transported through the tensor product by `tensorProductCongrRight`. -/
@[reassoc]
lemma pullbackTensorProductIso_hom_naturality_right (f : X ⟶ Y)
    (L : InvertibleSheaf Y) {K K' : InvertibleSheaf Y} (e : K ≅ K') :
    (pullback f).map (tensorProductCongrRight (L := L) e).hom ≫
        (pullbackTensorProductIso f L K').hom =
      (pullbackTensorProductIso f L K).hom ≫
        (tensorProductCongrRight (L := (pullback f).obj L) ((pullback f).mapIso e)).hom := by
  apply ObjectProperty.hom_ext
  rw [← cancel_mono (tensorProductObjIso ((pullback f).obj L) ((pullback f).obj K')).hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom,
    tensorProductCongrRight_hom_hom_comp_tensorProductObjIso_hom,
    pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom_assoc, pullback_map,
    Functor.mapIso_hom]
  simp only [eqToHom_refl, Category.id_comp, eqToHom_trans_assoc, ← Functor.map_comp_assoc,
    tensorProductCongrRight_hom_hom_comp_tensorProductObjIso_hom]
  rw [Functor.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural_right_assoc,
    whiskerLeft_comp_tensorHom_eqToHom _ (pullback_obj_obj f K).symm]

/-- Along the identity, `pullbackTensorProductIso` followed by the identity comparisons
`pullbackId` on both factors is the identity comparison of the tensor product. -/
lemma pullbackTensorProductIso_id (L K : InvertibleSheaf X) :
    (pullbackTensorProductIso (𝟙 X) L K).hom ≫
        (tensorProductCongrLeft (L' := L) ((pullbackId X).app L)).hom ≫
        (tensorProductCongrRight (K' := K) ((pullbackId X).app K)).hom =
      (pullbackId X).hom.app (tensorProduct L K) := by
  apply ObjectProperty.hom_ext
  rw [← cancel_mono (tensorProductObjIso L K).hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    tensorProductCongrRight_hom_hom_comp_tensorProductObjIso_hom,
    tensorProductCongrLeft_hom_hom_comp_tensorProductObjIso_hom_assoc,
    pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom_assoc]
  simp only [Iso.app_hom, pullbackId_hom_app_hom, ← tensorHom_def, tensorHom_comp_tensorHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Scheme.Modules.pullback_id_δ]
  have h := (Scheme.Modules.pullbackId X).hom.naturality (tensorProductObjIso L K).hom
  rw [Functor.id_map] at h
  rw [h, Category.assoc]

/-- `pullbackTensorProductIso` is compatible with composition: the comparison for `g` pulled
back along `f`, followed by the comparison for `f` and the composition comparisons `pullbackComp`
on both factors, is the composition comparison of the tensor product followed by the comparison
for `f ≫ g`. -/
lemma pullbackTensorProductIso_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (L K : InvertibleSheaf Z) :
    (pullback f).map (pullbackTensorProductIso g L K).hom ≫
        (pullbackTensorProductIso f ((pullback g).obj L) ((pullback g).obj K)).hom ≫
        (tensorProductCongrLeft (L := (pullback f).obj ((pullback g).obj L))
          (L' := (pullback (f ≫ g)).obj L) ((pullbackComp f g).app L)).hom ≫
        (tensorProductCongrRight (K := (pullback f).obj ((pullback g).obj K))
          (K' := (pullback (f ≫ g)).obj K) ((pullbackComp f g).app K)).hom =
      (pullbackComp f g).hom.app (tensorProduct L K) ≫
        (pullbackTensorProductIso (f ≫ g) L K).hom := by
  apply ObjectProperty.hom_ext
  rw [← cancel_mono
    (tensorProductObjIso ((pullback (f ≫ g)).obj L) ((pullback (f ≫ g)).obj K)).hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    tensorProductCongrRight_hom_hom_comp_tensorProductObjIso_hom,
    tensorProductCongrLeft_hom_hom_comp_tensorProductObjIso_hom_assoc,
    pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom_assoc,
    pullbackTensorProductIso_hom_hom_comp_tensorProductObjIso_hom]
  simp only [pullback_map, pullbackTensorProductIso_hom_hom, Functor.map_comp, Category.assoc,
    eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_map_assoc,
    Iso.app_hom, pullbackComp_hom_app_hom, ← tensorHom_def, tensorHom_comp_tensorHom]
  -- Move the composition comparison past the tensor comparisons of `f^*`, `g^*` and `(f ≫ g)^*`.
  have h := (Scheme.Modules.pullbackComp f g).hom.naturality (tensorProductObjIso L K).hom
  simp only [Functor.comp_map] at h
  rw [← reassoc_of% h, pullbackComp_hom_app_comp_δ_assoc,
    ← Functor.OplaxMonoidal.δ_natural_assoc]
  simp only [eqToHom_map, tensorHom_comp_tensorHom, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

/-- An isomorphism of schemes induces an equivalence between their categories of line bundles,
with forward functor `pullback e.hom` and inverse functor `pullback e.inv`. -/
def pullbackEquiv (e : X ≅ Y) : InvertibleSheaf Y ≌ InvertibleSheaf X :=
  CategoryTheory.Equivalence.mk (pullback e.hom) (pullback e.inv)
    ((pullbackId Y).symm ≪≫ eqToIso (congrArg pullback e.inv_hom_id.symm) ≪≫
      (pullbackComp e.inv e.hom).symm)
    (pullbackComp e.hom e.inv ≪≫ eqToIso (congrArg pullback e.hom_inv_id) ≪≫ pullbackId X)

/-- The forward functor of `pullbackEquiv e` is `pullback e.hom`. -/
@[simp]
theorem pullbackEquiv_functor (e : X ≅ Y) : (pullbackEquiv e).functor = pullback e.hom :=
  (rfl)

/-- The inverse functor of `pullbackEquiv e` is `pullback e.inv`. -/
@[simp]
theorem pullbackEquiv_inverse (e : X ≅ Y) : (pullbackEquiv e).inverse = pullback e.inv :=
  (rfl)

end InvertibleSheaf

namespace LineBundleClass

variable {X Y Z : Scheme.{u}}

/-- Pullback of an isomorphism class of line bundles along a scheme morphism. It is a group
homomorphism by `LineBundleClass.pullback_mul`, bundled as `LineBundleClass.pullbackHom`. -/
def pullback (f : X ⟶ Y) (a : LineBundleClass Y) : LineBundleClass X :=
  lift (fun L ↦ mk ((InvertibleSheaf.pullback f).obj L)) (fun _ _ ⟨e⟩ ↦
    mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible X).ι.mapIso
      ((InvertibleSheaf.pullback f).mapIso
        (ObjectProperty.isoMk (SheafOfModules.isInvertible Y) e))⟩) a

/-- Pulling back the class of `L` gives the class of its pulled-back line bundle. -/
@[simp]
lemma pullback_mk (f : X ⟶ Y) (L : InvertibleSheaf Y) :
    pullback f (mk L) = mk ((InvertibleSheaf.pullback f).obj L) :=
  lift_mk L

/-- Pullback by the identity acts identically on line-bundle classes. -/
@[simp]
lemma pullback_id (a : LineBundleClass X) : pullback (𝟙 X) a = a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible X).ι.mapIso
    ((InvertibleSheaf.pullbackId X).app L)⟩

/-- Pullback of line-bundle classes is contravariantly functorial under composition. -/
@[simp]
lemma pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a : LineBundleClass Z) :
    pullback f (pullback g a) = pullback (f ≫ g) a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  simp only [pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible X).ι.mapIso
    ((InvertibleSheaf.pullbackComp f g).app L)⟩

/-- Pullback preserves the class of the trivial line bundle. -/
@[simp]
lemma pullback_one (f : X ⟶ Y) : pullback f 1 = 1 := by
  rw [← mk_trivial, pullback_mk, mk_eq_one_iff]
  exact ⟨(Scheme.Modules.pullback f).mapIso
    (InvertibleSheaf.trivialObjIsoUnit Y) ≪≫
      Scheme.Modules.pullbackObjUnitIso f⟩

/-- Pullback of line-bundle classes is compatible with tensor product:
`[f^*(L ⊗ K)] = [f^*L] [f^*K]`. -/
@[simp]
lemma pullback_mul (f : X ⟶ Y) (a b : LineBundleClass Y) :
    pullback f (a * b) = pullback f a * pullback f b := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  obtain ⟨K, rfl⟩ := mk_surjective b
  simp only [← mk_tensorProduct, pullback_mk, mk_eq_mk_iff]
  exact ⟨(SheafOfModules.isInvertible X).ι.mapIso (InvertibleSheaf.pullbackTensorProductIso f L K)⟩

/-- Pullback of line-bundle classes along a scheme morphism, as a homomorphism of Picard
groups. -/
def pullbackHom (f : X ⟶ Y) : LineBundleClass Y →* LineBundleClass X :=
  MonoidHom.mk' (pullback f) (pullback_mul f)

/-- The Picard group homomorphism `pullbackHom f` is pullback of line-bundle classes. -/
@[simp]
lemma pullbackHom_apply (f : X ⟶ Y) (a : LineBundleClass Y) : pullbackHom f a = pullback f a :=
  (rfl)

/-- Pullback of line-bundle classes is compatible with inverses: `[f^*L⁻¹] = [f^*L]⁻¹`. -/
@[simp]
lemma pullback_inv (f : X ⟶ Y) (a : LineBundleClass Y) : pullback f a⁻¹ = (pullback f a)⁻¹ := by
  simpa only [pullbackHom_apply] using map_inv (pullbackHom f) a

/-- Pullback of line-bundle classes is compatible with natural powers: `[f^*(L^n)] = [f^*L]^n`. -/
@[simp]
lemma pullback_pow (f : X ⟶ Y) (a : LineBundleClass Y) (n : ℕ) :
    pullback f (a ^ n) = pullback f a ^ n := by
  simpa only [pullbackHom_apply] using map_pow (pullbackHom f) a n

/-- Pullback of line-bundle classes is compatible with integer powers: `[f^*(L^n)] = [f^*L]^n`. -/
@[simp]
lemma pullback_zpow (f : X ⟶ Y) (a : LineBundleClass Y) (n : ℤ) :
    pullback f (a ^ n) = pullback f a ^ n := by
  simpa only [pullbackHom_apply] using map_zpow (pullbackHom f) a n

/-- Pullback of Picard groups along the identity is the identity. -/
@[simp]
lemma pullbackHom_id (X : Scheme.{u}) : pullbackHom (𝟙 X) = MonoidHom.id _ :=
  MonoidHom.ext pullback_id

/-- Pullback of Picard groups is contravariantly functorial under composition. -/
@[simp]
lemma pullbackHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackHom f).comp (pullbackHom g) = pullbackHom (f ≫ g) :=
  MonoidHom.ext (pullback_comp f g)

/-- An isomorphism of schemes `e : X ≅ Y` induces a group isomorphism
`LineBundleClass Y ≃* LineBundleClass X` by pullback along `e.hom`, with inverse pullback along
`e.inv`. -/
def pullbackEquiv (e : X ≅ Y) : LineBundleClass Y ≃* LineBundleClass X where
  toFun := pullback e.hom
  invFun := pullback e.inv
  left_inv a := by rw [pullback_comp, e.inv_hom_id, pullback_id]
  right_inv a := by rw [pullback_comp, e.hom_inv_id, pullback_id]
  map_mul' := pullback_mul e.hom

/-- `pullbackEquiv e` acts by pullback along `e.hom`. -/
@[simp]
lemma pullbackEquiv_apply (e : X ≅ Y) (a : LineBundleClass Y) :
    pullbackEquiv e a = pullback e.hom a :=
  (rfl)

/-- The inverse of `pullbackEquiv e` is `pullbackEquiv e.symm`. -/
@[simp]
lemma pullbackEquiv_symm (e : X ≅ Y) : (pullbackEquiv e).symm = pullbackEquiv e.symm :=
  MulEquiv.ext fun _ ↦ rfl

/-- The underlying group homomorphism of `pullbackEquiv e` is `pullbackHom e.hom`. -/
@[simp]
lemma toMonoidHom_pullbackEquiv (e : X ≅ Y) :
    (pullbackEquiv e : LineBundleClass Y →* LineBundleClass X) = pullbackHom e.hom :=
  MonoidHom.ext fun _ ↦ rfl

/-- `pullbackEquiv` of the identity scheme isomorphism is the identity group equivalence. -/
@[simp]
lemma pullbackEquiv_refl (X : Scheme.{u}) :
    pullbackEquiv (Iso.refl X) = MulEquiv.refl (LineBundleClass X) :=
  MulEquiv.ext pullback_id

/-- `pullbackEquiv` reverses composition of scheme isomorphisms. -/
@[simp]
lemma pullbackEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    pullbackEquiv (e ≪≫ f) = (pullbackEquiv f).trans (pullbackEquiv e) :=
  MulEquiv.ext fun a ↦ (pullback_comp e.hom f.hom a).symm

/-- Pullback of line-bundle classes along a scheme morphism `f : X ⟶ Y`, packaged as a `ℤ`-linear
map on the additively written Picard groups. -/
def pullbackLinearMap (f : X ⟶ Y) :
    Additive (LineBundleClass Y) →ₗ[ℤ] Additive (LineBundleClass X) :=
  (MonoidHom.toAdditive (pullbackHom f)).toIntLinearMap

/-- `pullbackLinearMap f` acts on underlying multiplicative classes by
`LineBundleClass.pullback`. -/
@[simp]
lemma toMul_pullbackLinearMap_apply (f : X ⟶ Y) (a : Additive (LineBundleClass Y)) :
    (pullbackLinearMap f a).toMul = pullback f a.toMul := by
  simp [pullbackLinearMap]

/-- `pullbackLinearMap f` sends `Additive.ofMul a` to `Additive.ofMul (pullback f a)`. -/
@[simp]
lemma pullbackLinearMap_ofMul (f : X ⟶ Y) (a : LineBundleClass Y) :
    pullbackLinearMap f (Additive.ofMul a) = Additive.ofMul (pullback f a) := by
  simp [pullbackLinearMap]

/-- Pullback along the identity morphism is the identity `ℤ`-linear map. -/
@[simp]
lemma pullbackLinearMap_id (X : Scheme.{u}) :
    pullbackLinearMap (𝟙 X) = LinearMap.id := by
  ext a
  simp

/-- `pullbackLinearMap` is contravariantly functorial under composition of scheme morphisms. -/
@[simp]
lemma pullbackLinearMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackLinearMap (f ≫ g) = pullbackLinearMap f ∘ₗ pullbackLinearMap g := by
  ext a
  simp [pullback_comp]

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
