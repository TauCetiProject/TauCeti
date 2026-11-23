/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Closure
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Associator
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Tensor products of line bundles

The sheafified tensor product of `𝒪_X`-modules sends two line bundles to a line bundle. This file
packages that operation in the category `InvertibleSheaf X`, together with the unit computations
for the trivial line bundle.

## Main declarations

* `InvertibleSheaf.tensorProduct` packages the tensor product of two line bundles;
* `InvertibleSheaf.trivialObjIsoUnit` identifies the trivial line bundle with the monoidal unit;
* `InvertibleSheaf.tensorProduct_obj` identifies its underlying sheaf, and
  `InvertibleSheaf.tensorProductObjIso` identifies it with the monoidal tensor product of the
  underlying sheaves, through `SheafOfModules.tensorProductIso` and
  `SheafOfModules.tensorUnderlyingIso` (`InvertibleSheaf.tensorProductObjIso_hom`);
* `InvertibleSheaf.tensorProductCongrLeft` and `InvertibleSheaf.tensorProductCongrRight` transport
  isomorphisms through either tensor factor, so `InvertibleSheaf.isIsomorphic_tensorProduct`
  shows that tensor product respects isomorphism; through `tensorProductObjIso` these transports
  are whiskerings of the monoidal tensor product
  (`InvertibleSheaf.tensorProductCongrLeft_hom_hom_comp_tensorProductObjIso_hom` and
  `InvertibleSheaf.tensorProductCongrRight_hom_hom_comp_tensorProductObjIso_hom`); both
  transports respect identities and composition, and they commute with each other
  (`InvertibleSheaf.tensorProductCongrLeft_trans_tensorProductCongrRight`);
* `InvertibleSheaf.tensorProductComm` exchanges the two tensor factors;
* `InvertibleSheaf.tensorProductAssoc` is the associativity isomorphism;
* `InvertibleSheaf.tensorTrivialLeftIso` and `InvertibleSheaf.tensorTrivialRightIso` are the
  unit isomorphisms in the full category of invertible sheaves.

The underlying sheaf is exposed by `tensorProduct_obj`, while the congruence, symmetry,
associativity, and unit isomorphisms provide the categorical API for manipulating tensor products
of line bundles.
-/

public section

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- The trivial line bundle is isomorphic to the monoidal unit of `X.Modules`.
Here `𝟙_ X.Modules` unfolds to `SheafOfModules.unit X.ringCatSheaf`. -/
def trivialObjIsoUnit (X : Scheme.{u}) : (trivial X).obj ≅ 𝟙_ X.Modules :=
  (trivial_obj X) ▸ TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf

/-- The tensor product of two line bundles on a scheme. -/
def tensorProduct (L K : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨SheafOfModules.tensorProduct X.sheaf L.obj K.obj,
    by
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) K.obj := K.property
      exact SheafOfModules.IsInvertible.tensorProduct (R := X.sheaf) (M := L.obj) (N := K.obj)⟩

/-- The underlying sheaf of `tensorProduct L K` is the sheafified tensor product of the
underlying sheaves of `L` and `K`. -/
@[simp]
lemma tensorProduct_obj (L K : InvertibleSheaf X) :
    (tensorProduct L K).obj = SheafOfModules.tensorProduct X.sheaf L.obj K.obj :=
  (rfl)

/-- The underlying sheaf of the tensor product of two line bundles is the tensor product of their
underlying sheaves in the monoidal category of `𝒪_X`-modules. -/
def tensorProductObjIso (L K : InvertibleSheaf X) :
    (tensorProduct L K).obj ≅ L.obj ⊗ K.obj :=
  eqToIso (tensorProduct_obj L K) ≪≫ SheafOfModules.tensorProductIso X.sheaf L.obj K.obj ≪≫
    (L.obj.tensorUnderlyingIso K.obj).symm

/-- The sheaf isomorphism underlying transport through the first tensor factor. -/
def tensorProductCongrLeftIso {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct L' K).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductCongrLeft (N := K.obj) X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e))

/-- An isomorphism of the first factor transports through the tensor product. -/
def tensorProductCongrLeft {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    tensorProduct L K ≅ tensorProduct L' K :=
  ObjectProperty.isoMk _ (tensorProductCongrLeftIso e)

@[simp]
lemma tensorProductCongrLeft_hom_hom {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    (tensorProductCongrLeft (K := K) e).hom.hom =
      (tensorProductCongrLeftIso e).hom :=
  (rfl)

@[simp]
lemma tensorProductCongrLeft_inv_hom {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    (tensorProductCongrLeft (K := K) e).inv.hom =
      (tensorProductCongrLeftIso e).inv :=
  (rfl)

/-- The sheaf isomorphism underlying transport through the second tensor factor. -/
def tensorProductCongrRightIso {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct L K').obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductCongrRight (M := L.obj) X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e))

/-- An isomorphism of the second factor transports through the tensor product. -/
def tensorProductCongrRight {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    tensorProduct L K ≅ tensorProduct L K' :=
  ObjectProperty.isoMk _ (tensorProductCongrRightIso e)

@[simp]
lemma tensorProductCongrRight_hom_hom {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).hom.hom =
      (tensorProductCongrRightIso e).hom :=
  (rfl)

@[simp]
lemma tensorProductCongrRight_inv_hom {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).inv.hom =
      (tensorProductCongrRightIso e).inv :=
  (rfl)

/-- `tensorProductObjIso` is the transport along `tensorProduct_obj`, followed by the defining
identification `SheafOfModules.tensorProductIso` and the inverse of `tensorUnderlyingIso`. -/
lemma tensorProductObjIso_hom (L K : InvertibleSheaf X) :
    (tensorProductObjIso L K).hom = eqToHom (tensorProduct_obj L K) ≫
      (SheafOfModules.tensorProductIso X.sheaf L.obj K.obj).hom ≫
        (L.obj.tensorUnderlyingIso K.obj).inv :=
  (rfl)

/-- Read through `tensorProductObjIso`, transport through the first tensor factor is whiskering
of the monoidal tensor product of underlying sheaves. -/
@[reassoc]
lemma tensorProductCongrLeft_hom_hom_comp_tensorProductObjIso_hom {L L' : InvertibleSheaf X}
    (e : L ≅ L') (K : InvertibleSheaf X) :
    (tensorProductCongrLeft (K := K) e).hom.hom ≫ (tensorProductObjIso L' K).hom =
      (tensorProductObjIso L K).hom ≫ e.hom.hom ▷ K.obj := by
  have hc : (tensorProductCongrLeft (K := K) e).hom.hom =
      (TauCeti.SheafOfModules.tensorProductCongrLeft X.sheaf (N := K.obj)
        ((SheafOfModules.isInvertible X).ι.mapIso e)).hom :=
    tensorProductCongrLeft_hom_hom e
  -- The transports along `tensorProduct_obj`, which is `rfl`, are identities.
  have h₁ : (tensorProductObjIso L K).hom = (SheafOfModules.tensorProductIso X.sheaf _ _).hom ≫
      (L.obj.tensorUnderlyingIso K.obj).inv := by
    rw [tensorProductObjIso_hom]
    exact Category.id_comp _
  have h₂ : (tensorProductObjIso L' K).hom = (SheafOfModules.tensorProductIso X.sheaf _ _).hom ≫
      (L'.obj.tensorUnderlyingIso K.obj).inv := by
    rw [tensorProductObjIso_hom]
    exact Category.id_comp _
  open TauCeti.SheafOfModules in
  have h := tensorProductCongrLeft_hom_comp_tensorProductIso_hom_comp_tensorUnderlyingIso_inv
      (R := X.sheaf) (N := K.obj) ((SheafOfModules.isInvertible X).ι.mapIso e)
  rw [Functor.mapIso_hom, ObjectProperty.ι_map] at h
  rw [hc, h₁, h₂]
  -- `h` is the goal, read in the category `X.Modules` of sheaves of `X.ringCatSheaf`-modules.
  exact h

/-- Read through `tensorProductObjIso`, transport through the second tensor factor is whiskering
of the monoidal tensor product of underlying sheaves. -/
@[reassoc]
lemma tensorProductCongrRight_hom_hom_comp_tensorProductObjIso_hom (L : InvertibleSheaf X)
    {K K' : InvertibleSheaf X} (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).hom.hom ≫ (tensorProductObjIso L K').hom =
      (tensorProductObjIso L K).hom ≫ L.obj ◁ e.hom.hom := by
  have hc : (tensorProductCongrRight (L := L) e).hom.hom =
      (TauCeti.SheafOfModules.tensorProductCongrRight X.sheaf (M := L.obj)
        ((SheafOfModules.isInvertible X).ι.mapIso e)).hom :=
    tensorProductCongrRight_hom_hom e
  -- The transports along `tensorProduct_obj`, which is `rfl`, are identities.
  have h₁ : (tensorProductObjIso L K).hom = (SheafOfModules.tensorProductIso X.sheaf _ _).hom ≫
      (L.obj.tensorUnderlyingIso K.obj).inv := by
    rw [tensorProductObjIso_hom]
    exact Category.id_comp _
  have h₂ : (tensorProductObjIso L K').hom = (SheafOfModules.tensorProductIso X.sheaf _ _).hom ≫
      (L.obj.tensorUnderlyingIso K'.obj).inv := by
    rw [tensorProductObjIso_hom]
    exact Category.id_comp _
  open TauCeti.SheafOfModules in
  have h := tensorProductCongrRight_hom_comp_tensorProductIso_hom_comp_tensorUnderlyingIso_inv
      (R := X.sheaf) (M := L.obj) ((SheafOfModules.isInvertible X).ι.mapIso e)
  rw [Functor.mapIso_hom, ObjectProperty.ι_map] at h
  rw [hc, h₁, h₂]
  -- As for the first factor, `h` is the goal, read in the category `X.Modules`.
  exact h

/-- Tensor product preserves isomorphism of line bundles in both variables. -/
lemma isIsomorphic_tensorProduct {L L' K K' : InvertibleSheaf X}
    (hL : IsIsomorphic L L') (hK : IsIsomorphic K K') :
    IsIsomorphic (tensorProduct L K) (tensorProduct L' K') := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := hK
  exact ⟨tensorProductCongrLeft e ≪≫ tensorProductCongrRight f⟩

/-- Two isomorphisms of line bundles agree once their underlying morphisms of presheaves of
modules agree. -/
private lemma iso_ext_val {L K : InvertibleSheaf X} {e e' : L ≅ K}
    (h : e.hom.hom.val = e'.hom.hom.val) : e = e' :=
  Iso.ext (ObjectProperty.hom_ext _ (_root_.SheafOfModules.Hom.ext h))

/-- Transport through the first tensor factor sends the identity to the identity. -/
@[simp]
lemma tensorProductCongrLeft_refl (L K : InvertibleSheaf X) :
    tensorProductCongrLeft (K := K) (Iso.refl L) = Iso.refl _ := by
  refine iso_ext_val ?_
  have h := congrArg (fun e ↦ e.hom.val)
    (TauCeti.SheafOfModules.tensorProductCongrLeft_refl X.sheaf L.obj K.obj)
  simp only [Iso.refl_hom, _root_.SheafOfModules.id_val] at h
  rw [tensorProductCongrLeft_hom_hom]
  exact h

/-- Transport through the first tensor factor respects composition. -/
@[simp]
lemma tensorProductCongrLeft_trans {L L' L'' K : InvertibleSheaf X} (e : L ≅ L')
    (e' : L' ≅ L'') :
    tensorProductCongrLeft (K := K) (e ≪≫ e') =
      tensorProductCongrLeft e ≪≫ tensorProductCongrLeft e' := by
  refine iso_ext_val ?_
  have h := congrArg (fun e ↦ e.hom.val)
    (TauCeti.SheafOfModules.tensorProductCongrLeft_trans X.sheaf (N := K.obj)
      ((SheafOfModules.isInvertible X).ι.mapIso e) ((SheafOfModules.isInvertible X).ι.mapIso e'))
  simp only [Iso.trans_hom, _root_.SheafOfModules.comp_val] at h
  simp only [Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom]
  -- Composition in `X.Modules` is composition of sheaves of modules.
  erw [_root_.SheafOfModules.comp_val]
  rw [tensorProductCongrLeft_hom_hom, tensorProductCongrLeft_hom_hom,
    tensorProductCongrLeft_hom_hom]
  exact h

/-- Transport through the second tensor factor sends the identity to the identity. -/
@[simp]
lemma tensorProductCongrRight_refl (L K : InvertibleSheaf X) :
    tensorProductCongrRight (L := L) (Iso.refl K) = Iso.refl _ := by
  refine iso_ext_val ?_
  have h := congrArg (fun e ↦ e.hom.val)
    (TauCeti.SheafOfModules.tensorProductCongrRight_refl X.sheaf L.obj K.obj)
  simp only [Iso.refl_hom, _root_.SheafOfModules.id_val] at h
  rw [tensorProductCongrRight_hom_hom]
  exact h

/-- Transport through the second tensor factor respects composition. -/
@[simp]
lemma tensorProductCongrRight_trans {L K K' K'' : InvertibleSheaf X} (e : K ≅ K')
    (e' : K' ≅ K'') :
    tensorProductCongrRight (L := L) (e ≪≫ e') =
      tensorProductCongrRight e ≪≫ tensorProductCongrRight e' := by
  refine iso_ext_val ?_
  have h := congrArg (fun e ↦ e.hom.val)
    (TauCeti.SheafOfModules.tensorProductCongrRight_trans X.sheaf (M := L.obj)
      ((SheafOfModules.isInvertible X).ι.mapIso e) ((SheafOfModules.isInvertible X).ι.mapIso e'))
  simp only [Iso.trans_hom, _root_.SheafOfModules.comp_val] at h
  simp only [Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom]
  -- Composition in `X.Modules` is composition of sheaves of modules.
  erw [_root_.SheafOfModules.comp_val]
  rw [tensorProductCongrRight_hom_hom, tensorProductCongrRight_hom_hom,
    tensorProductCongrRight_hom_hom]
  exact h

/-- Transports through the two tensor factors commute. -/
lemma tensorProductCongrLeft_trans_tensorProductCongrRight {L L' K K' : InvertibleSheaf X}
    (e : L ≅ L') (f : K ≅ K') :
    tensorProductCongrLeft e ≪≫ tensorProductCongrRight f =
      tensorProductCongrRight f ≪≫ tensorProductCongrLeft e := by
  refine iso_ext_val ?_
  have h := congrArg (fun e ↦ e.hom.val)
    (TauCeti.SheafOfModules.tensorProductCongrLeft_trans_tensorProductCongrRight X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e) ((SheafOfModules.isInvertible X).ι.mapIso f))
  simp only [Iso.trans_hom, _root_.SheafOfModules.comp_val] at h
  simp only [Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom]
  -- Composition in `X.Modules` is composition of sheaves of modules.
  erw [_root_.SheafOfModules.comp_val, _root_.SheafOfModules.comp_val]
  rw [tensorProductCongrLeft_hom_hom, tensorProductCongrRight_hom_hom,
    tensorProductCongrLeft_hom_hom, tensorProductCongrRight_hom_hom]
  exact h

/-- The sheaf isomorphism underlying symmetry of the tensor product of line bundles. -/
def tensorProductCommIso (L K : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct K L).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductComm X.sheaf L.obj K.obj)

/-- The tensor product of line bundles is symmetric. -/
def tensorProductComm (L K : InvertibleSheaf X) : tensorProduct L K ≅ tensorProduct K L :=
  ObjectProperty.isoMk _ (tensorProductCommIso L K)

@[simp]
lemma tensorProductComm_hom_hom (L K : InvertibleSheaf X) :
    (tensorProductComm L K).hom.hom =
      (tensorProductCommIso L K).hom :=
  (rfl)

@[simp]
lemma tensorProductComm_inv_hom (L K : InvertibleSheaf X) :
    (tensorProductComm L K).inv.hom =
      (tensorProductCommIso L K).inv :=
  (rfl)

/-- The sheaf isomorphism underlying associativity of the tensor product of line bundles. -/
def tensorProductAssocIso (L K M : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct (tensorProduct L K) M).obj
      (tensorProduct L (tensorProduct K M)).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductAssoc X.sheaf L.obj K.obj M.obj)

/-- The tensor product of line bundles is associative. -/
def tensorProductAssoc (L K M : InvertibleSheaf X) :
    tensorProduct (tensorProduct L K) M ≅ tensorProduct L (tensorProduct K M) :=
  ObjectProperty.isoMk _ (tensorProductAssocIso L K M)

@[simp]
lemma tensorProductAssoc_hom_hom (L K M : InvertibleSheaf X) :
    (tensorProductAssoc L K M).hom.hom =
      (tensorProductAssocIso L K M).hom :=
  (rfl)

@[simp]
lemma tensorProductAssoc_inv_hom (L K M : InvertibleSheaf X) :
    (tensorProductAssoc L K M).inv.hom =
      (tensorProductAssocIso L K M).inv :=
  (rfl)

/-- The sheaf isomorphism underlying the left unit for the tensor product of line bundles. -/
def tensorTrivialLeftIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct (trivial X) L).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoLeft X.sheaf L.obj)

/-- The trivial line bundle is a left unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialLeftIso (L : InvertibleSheaf X) : tensorProduct (trivial X) L ≅ L :=
  ObjectProperty.isoMk _ (tensorTrivialLeftIsoSheaf L)

@[simp]
lemma tensorTrivialLeftIso_hom_hom (L : InvertibleSheaf X) :
    (tensorTrivialLeftIso L).hom.hom =
      (tensorTrivialLeftIsoSheaf L).hom :=
  (rfl)

@[simp]
lemma tensorTrivialLeftIso_inv_hom (L : InvertibleSheaf X) :
    (tensorTrivialLeftIso L).inv.hom =
      (tensorTrivialLeftIsoSheaf L).inv :=
  (rfl)

/-- The sheaf isomorphism underlying the right unit for the tensor product of line bundles. -/
def tensorTrivialRightIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L (trivial X)).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoRight X.sheaf L.obj)

/-- The trivial line bundle is a right unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialRightIso (L : InvertibleSheaf X) : tensorProduct L (trivial X) ≅ L :=
  ObjectProperty.isoMk _ (tensorTrivialRightIsoSheaf L)

@[simp]
lemma tensorTrivialRightIso_hom_hom (L : InvertibleSheaf X) :
    (tensorTrivialRightIso L).hom.hom =
      (tensorTrivialRightIsoSheaf L).hom :=
  (rfl)

@[simp]
lemma tensorTrivialRightIso_inv_hom (L : InvertibleSheaf X) :
    (tensorTrivialRightIso L).inv.hom =
      (tensorTrivialRightIsoSheaf L).inv :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
