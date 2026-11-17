/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Closure
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Associator
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
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
  underlying sheaves;
* `InvertibleSheaf.tensorProductCongrLeft` and `InvertibleSheaf.tensorProductCongrRight` transport
  isomorphisms through either tensor factor, so `InvertibleSheaf.isIsomorphic_tensorProduct`
  shows that tensor product respects isomorphism;
* `InvertibleSheaf.tensorProductComm` exchanges the two tensor factors;
* `InvertibleSheaf.tensorProductAssoc` is the associativity isomorphism;
* `InvertibleSheaf.tensorTrivialLeftIso` and `InvertibleSheaf.tensorTrivialRightIso` are the
  unit isomorphisms in the full category of invertible sheaves;
* `SheafOfModules.isInvertible_tensor`: the monoidal tensor product of two invertible sheaves is
  invertible.

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
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCongrLeftIso e))

@[simp]
lemma tensorProductCongrLeft_hom_val {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    (tensorProductCongrLeft (K := K) e).hom.hom.val =
      (tensorProductCongrLeftIso e).hom.val := by
  simp only [tensorProductCongrLeft, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorProductCongrLeft_inv_val {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    (tensorProductCongrLeft (K := K) e).inv.hom.val =
      (tensorProductCongrLeftIso e).inv.val := by
  simp only [tensorProductCongrLeft, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- `tensorProductCongrLeft` commutes with taking inverses of isomorphisms. -/
@[simp] lemma tensorProductCongrLeft_symm {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    tensorProductCongrLeft (K := K) e.symm = (tensorProductCongrLeft (K := K) e).symm := by
  refine Iso.ext (ObjectProperty.hom_ext _ (_root_.SheafOfModules.hom_ext ?_))
  rw [tensorProductCongrLeft_hom_val, Iso.symm_hom, tensorProductCongrLeft_inv_val]
  exact congrArg (·.hom.val) (SheafOfModules.tensorProductCongrLeft_symm (N := K.obj) X.sheaf
    ((SheafOfModules.isInvertible X).ι.mapIso e))

/-- The sheaf isomorphism underlying transport through the second tensor factor. -/
def tensorProductCongrRightIso {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct L K').obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductCongrRight (M := L.obj) X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e))

/-- An isomorphism of the second factor transports through the tensor product. -/
def tensorProductCongrRight {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    tensorProduct L K ≅ tensorProduct L K' :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCongrRightIso e))

@[simp]
lemma tensorProductCongrRight_hom_val {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).hom.hom.val =
      (tensorProductCongrRightIso e).hom.val := by
  simp only [tensorProductCongrRight, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorProductCongrRight_inv_val {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).inv.hom.val =
      (tensorProductCongrRightIso e).inv.val := by
  simp only [tensorProductCongrRight, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- `tensorProductCongrRight` commutes with taking inverses of isomorphisms. -/
@[simp] lemma tensorProductCongrRight_symm {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    tensorProductCongrRight (L := L) e.symm = (tensorProductCongrRight (L := L) e).symm := by
  refine Iso.ext (ObjectProperty.hom_ext _ (_root_.SheafOfModules.hom_ext ?_))
  rw [tensorProductCongrRight_hom_val, Iso.symm_hom, tensorProductCongrRight_inv_val]
  exact congrArg (·.hom.val) (SheafOfModules.tensorProductCongrRight_symm (M := L.obj) X.sheaf
    ((SheafOfModules.isInvertible X).ι.mapIso e))

/-- Tensor product preserves isomorphism of line bundles in both variables. -/
lemma isIsomorphic_tensorProduct {L L' K K' : InvertibleSheaf X}
    (hL : IsIsomorphic L L') (hK : IsIsomorphic K K') :
    IsIsomorphic (tensorProduct L K) (tensorProduct L' K') := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := hK
  exact ⟨tensorProductCongrLeft e ≪≫ tensorProductCongrRight f⟩

/-- The sheaf isomorphism underlying symmetry of the tensor product of line bundles. -/
def tensorProductCommIso (L K : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct K L).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductComm X.sheaf L.obj K.obj)

/-- The tensor product of line bundles is symmetric. -/
def tensorProductComm (L K : InvertibleSheaf X) : tensorProduct L K ≅ tensorProduct K L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCommIso L K))

@[simp]
lemma tensorProductComm_hom_val (L K : InvertibleSheaf X) :
    (tensorProductComm L K).hom.hom.val =
      (tensorProductCommIso L K).hom.val := by
  simp only [tensorProductComm, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorProductComm_inv_val (L K : InvertibleSheaf X) :
    (tensorProductComm L K).inv.hom.val =
      (tensorProductCommIso L K).inv.val := by
  simp only [tensorProductComm, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The sheaf isomorphism underlying associativity of the tensor product of line bundles. -/
def tensorProductAssocIso (L K M : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct (tensorProduct L K) M).obj
      (tensorProduct L (tensorProduct K M)).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj] using
    (SheafOfModules.tensorProductAssoc X.sheaf L.obj K.obj M.obj)

/-- The tensor product of line bundles is associative. -/
def tensorProductAssoc (L K M : InvertibleSheaf X) :
    tensorProduct (tensorProduct L K) M ≅ tensorProduct L (tensorProduct K M) :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductAssocIso L K M))

@[simp]
lemma tensorProductAssoc_hom_val (L K M : InvertibleSheaf X) :
    (tensorProductAssoc L K M).hom.hom.val =
      (tensorProductAssocIso L K M).hom.val := by
  simp only [tensorProductAssoc, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorProductAssoc_inv_val (L K M : InvertibleSheaf X) :
    (tensorProductAssoc L K M).inv.hom.val =
      (tensorProductAssocIso L K M).inv.val := by
  simp only [tensorProductAssoc, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The sheaf isomorphism underlying the left unit for the tensor product of line bundles. -/
def tensorTrivialLeftIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct (trivial X) L).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoLeft X.sheaf L.obj)

/-- The trivial line bundle is a left unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialLeftIso (L : InvertibleSheaf X) : tensorProduct (trivial X) L ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorTrivialLeftIsoSheaf L))

@[simp]
lemma tensorTrivialLeftIso_hom_val (L : InvertibleSheaf X) :
    (tensorTrivialLeftIso L).hom.hom.val =
      (tensorTrivialLeftIsoSheaf L).hom.val := by
  simp only [tensorTrivialLeftIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorTrivialLeftIso_inv_val (L : InvertibleSheaf X) :
    (tensorTrivialLeftIso L).inv.hom.val =
      (tensorTrivialLeftIsoSheaf L).inv.val := by
  simp only [tensorTrivialLeftIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The sheaf isomorphism underlying the right unit for the tensor product of line bundles. -/
def tensorTrivialRightIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L (trivial X)).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoRight X.sheaf L.obj)

/-- The trivial line bundle is a right unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialRightIso (L : InvertibleSheaf X) : tensorProduct L (trivial X) ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorTrivialRightIsoSheaf L))

@[simp]
lemma tensorTrivialRightIso_hom_val (L : InvertibleSheaf X) :
    (tensorTrivialRightIso L).hom.hom.val =
      (tensorTrivialRightIsoSheaf L).hom.val := by
  simp only [tensorTrivialRightIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorTrivialRightIso_inv_val (L : InvertibleSheaf X) :
    (tensorTrivialRightIso L).inv.hom.val =
      (tensorTrivialRightIsoSheaf L).inv.val := by
  simp only [tensorTrivialRightIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The forward map of `tensorProductObjIso` factors through `SheafOfModules.tensorProductIso` and
`SheafOfModules.tensorUnderlyingIso`. -/
lemma tensorProductObjIso_hom (L K : InvertibleSheaf X) :
    (tensorProductObjIso L K).hom =
      (eqToIso (tensorProduct_obj L K)).hom ≫
        (SheafOfModules.tensorProductIso X.sheaf L.obj K.obj).hom ≫
          (L.obj.tensorUnderlyingIso K.obj).inv :=
  (rfl)

/-- `tensorProductObjIso` is natural in the first tensor factor. -/
@[reassoc] lemma tensorProductCongrLeft_hom_tensorProductObjIso_hom {L L' K : InvertibleSheaf X}
    (e : L ≅ L') :
    (tensorProductCongrLeft (K := K) e).hom.hom ≫ (tensorProductObjIso L' K).hom =
      (tensorProductObjIso L K).hom ≫ (e.hom.hom ▷ K.obj) := by
  let L₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := L.obj
  let L'₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := L'.obj
  let K₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := K.obj
  let e₀ : L₀ ≅ L'₀ := (SheafOfModules.isInvertible X).ι.mapIso e
  have hcongr : (tensorProductCongrLeft (K := K) e).hom.hom =
      (SheafOfModules.tensorProductCongrLeft (N := K₀) X.sheaf e₀).hom :=
    _root_.SheafOfModules.hom_ext (tensorProductCongrLeft_hom_val e)
  have h2 := _root_.SheafOfModules.tensorUnderlyingIso_naturality (R := X.sheaf) e₀.hom (𝟙 K₀)
  rw [tensorHom_id, _root_.SheafOfModules.id_val, tensorHom_id] at h2
  have h3 : (PresheafOfModules.sheafification (𝟙 (SheafOfModules.ringCatSheaf X.sheaf).obj)).map
        (e₀.hom.val ▷ K₀.val) ≫ (L'₀.tensorUnderlyingIso K₀).inv =
      (L₀.tensorUnderlyingIso K₀).inv ≫ (e₀.hom ▷ K₀) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]; exact h2.symm
  have h1 := SheafOfModules.tensorProductCongrLeft_hom_tensorProductIso_hom (N := K₀) X.sheaf e₀
  have hmain : (SheafOfModules.tensorProductCongrLeft (N := K₀) X.sheaf e₀).hom ≫
      (SheafOfModules.tensorProductIso X.sheaf L'₀ K₀).hom ≫ (L'₀.tensorUnderlyingIso K₀).inv =
    ((SheafOfModules.tensorProductIso X.sheaf L₀ K₀).hom ≫ (L₀.tensorUnderlyingIso K₀).inv) ≫
      (e₀.hom ▷ K₀) := by rw [reassoc_of% h1, h3, Category.assoc]
  have hobj (A B : InvertibleSheaf X) :
      ((tensorProductObjIso A B).hom :
        SheafOfModules.tensorProduct X.sheaf A.obj B.obj ⟶ A.obj ⊗ B.obj) =
      (SheafOfModules.tensorProductIso X.sheaf A.obj B.obj).hom ≫
        (A.obj.tensorUnderlyingIso B.obj).inv := Category.id_comp _
  exact (congrArg₂ (· ≫ ·) hcongr (hobj L' K)).trans <|
    hmain.trans (congrArg (· ≫ _) (hobj L K)).symm

/-- `tensorProductObjIso` is natural in the second tensor factor. -/
@[reassoc] lemma tensorProductCongrRight_hom_tensorProductObjIso_hom {L K K' : InvertibleSheaf X}
    (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).hom.hom ≫ (tensorProductObjIso L K').hom =
      (tensorProductObjIso L K).hom ≫ (L.obj ◁ e.hom.hom) := by
  let L₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := L.obj
  let K₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := K.obj
  let K'₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := K'.obj
  let e₀ : K₀ ≅ K'₀ := (SheafOfModules.isInvertible X).ι.mapIso e
  have hcongr : (tensorProductCongrRight (L := L) e).hom.hom =
      (SheafOfModules.tensorProductCongrRight (M := L₀) X.sheaf e₀).hom :=
    _root_.SheafOfModules.hom_ext (tensorProductCongrRight_hom_val e)
  have h2 := _root_.SheafOfModules.tensorUnderlyingIso_naturality (R := X.sheaf) (𝟙 L₀) e₀.hom
  rw [id_tensorHom, _root_.SheafOfModules.id_val, id_tensorHom] at h2
  have h3 : (PresheafOfModules.sheafification (𝟙 (SheafOfModules.ringCatSheaf X.sheaf).obj)).map
        (L₀.val ◁ e₀.hom.val) ≫ (L₀.tensorUnderlyingIso K'₀).inv =
      (L₀.tensorUnderlyingIso K₀).inv ≫ (L₀ ◁ e₀.hom) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]; exact h2.symm
  have h1 := SheafOfModules.tensorProductCongrRight_hom_tensorProductIso_hom (M := L₀) X.sheaf e₀
  have hmain : (SheafOfModules.tensorProductCongrRight (M := L₀) X.sheaf e₀).hom ≫
      (SheafOfModules.tensorProductIso X.sheaf L₀ K'₀).hom ≫ (L₀.tensorUnderlyingIso K'₀).inv =
    ((SheafOfModules.tensorProductIso X.sheaf L₀ K₀).hom ≫ (L₀.tensorUnderlyingIso K₀).inv) ≫
      (L₀ ◁ e₀.hom) := by rw [reassoc_of% h1, h3, Category.assoc]
  have hobj (A B : InvertibleSheaf X) :
      ((tensorProductObjIso A B).hom :
        SheafOfModules.tensorProduct X.sheaf A.obj B.obj ⟶ A.obj ⊗ B.obj) =
      (SheafOfModules.tensorProductIso X.sheaf A.obj B.obj).hom ≫
        (A.obj.tensorUnderlyingIso B.obj).inv := Category.id_comp _
  exact (congrArg₂ (· ≫ ·) hcongr (hobj L K')).trans <|
    hmain.trans (congrArg (· ≫ _) (hobj L K)).symm

end InvertibleSheaf

namespace SheafOfModules

variable {X : Scheme.{u}}

/-- The monoidal tensor product of two invertible `𝒪_X`-modules is invertible. -/
instance isInvertible_tensor {M N : X.Modules}
    [hM : isInvertible X M] [hN : isInvertible X N] :
    isInvertible X (M ⊗ N) :=
  (isInvertible X).prop_of_iso
    (InvertibleSheaf.tensorProductObjIso ⟨M, hM⟩ ⟨N, hN⟩)
    (InvertibleSheaf.tensorProduct ⟨M, hM⟩ ⟨N, hN⟩).2

end SheafOfModules

end

end AlgebraicGeometry

end TauCeti
