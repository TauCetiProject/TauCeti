/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.CategoryTheory.Products.Preadditive

/-!
# Split `K₀` of a product category

This file identifies the split Grothendieck group of a product of additive categories with the
product of their split Grothendieck groups. The equivalence is characterised on object classes
and is natural in additive functors in both variables.

## Main definitions

* `TauCeti.SplitK0.prodEquiv`: the canonical equivalence
  `SplitK0 (C × D) ≃+ SplitK0 C × SplitK0 D`.

## Main results

* `TauCeti.SplitK0.prodEquiv_apply`: the forward map is induced by the two projections.
* `TauCeti.SplitK0.prodEquiv_symm_apply`: the inverse is the sum of the two zero-section maps.
* `TauCeti.SplitK0.prodEquiv_of`: the equivalence sends `[(X, Y)]` to `([X], [Y])`.
* `TauCeti.SplitK0.prodEquiv_naturality`: the equivalence is natural in additive functors.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w₁ w₂ v v' v₁ v₂ u u' u₁ u₂

namespace SplitK0

section Product

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]

private noncomputable def toProd : SplitK0 (C × D) →+ SplitK0 C × SplitK0 D :=
  AddMonoidHom.prod (map (CategoryTheory.Prod.fst C D))
    (map (CategoryTheory.Prod.snd C D))

private noncomputable def fromProd : SplitK0 C × SplitK0 D →+ SplitK0 (C × D) :=
  (map (CategoryTheory.Prod.sectL C (0 : D))).coprod
    (map (CategoryTheory.Prod.sectR (0 : C) D))

private lemma of_eq_of_components (X : C × D) :
    (of X : SplitK0 (C × D)) = of (X.1, 0) + of (0, X.2) := by
  let _ : PreservesBinaryBiproducts (CategoryTheory.Prod.fst C D) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let _ : PreservesBinaryBiproducts (CategoryTheory.Prod.snd C D) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  rw [← of_biprod]
  apply of_congr
  exact ((prod.etaIso ((X.1, 0) ⊞ (0, X.2))).symm ≪≫
    Iso.prod ((CategoryTheory.Prod.fst C D).mapBiprod _ _)
      ((CategoryTheory.Prod.snd C D).mapBiprod _ _) ≪≫
    Iso.prod (isoBiprodZero (isZero_zero C)).symm
      (isoZeroBiprod (isZero_zero D)).symm ≪≫
      prod.etaIso X).symm

omit [HasZeroObject C] [HasZeroObject D] in
@[simp] private lemma toProd_of (X : C × D) : toProd (of X) = (of X.1, of X.2) := by
  simp [toProd]

omit [HasZeroObject C] in
@[simp] private lemma map_fst_sectL (x : SplitK0 C) :
    map (CategoryTheory.Prod.fst C D) (map (CategoryTheory.Prod.sectL C (0 : D)) x) = x := by
  have h : (map (CategoryTheory.Prod.fst C D)).comp
      (map (CategoryTheory.Prod.sectL C (0 : D))) = AddMonoidHom.id _ := by
    apply hom_ext
    simp
  exact DFunLike.congr_fun h x

omit [HasZeroObject D] in
@[simp] private lemma map_fst_sectR (y : SplitK0 D) :
    map (CategoryTheory.Prod.fst C D) (map (CategoryTheory.Prod.sectR (0 : C) D) y) = 0 := by
  have h : (map (CategoryTheory.Prod.fst C D)).comp
      (map (CategoryTheory.Prod.sectR (0 : C) D)) = 0 := by
    apply hom_ext
    simp
  exact DFunLike.congr_fun h y

omit [HasZeroObject C] in
@[simp] private lemma map_snd_sectL (x : SplitK0 C) :
    map (CategoryTheory.Prod.snd C D) (map (CategoryTheory.Prod.sectL C (0 : D)) x) = 0 := by
  have h : (map (CategoryTheory.Prod.snd C D)).comp
      (map (CategoryTheory.Prod.sectL C (0 : D))) = 0 := by
    apply hom_ext
    simp
  exact DFunLike.congr_fun h x

omit [HasZeroObject D] in
@[simp] private lemma map_snd_sectR (y : SplitK0 D) :
    map (CategoryTheory.Prod.snd C D) (map (CategoryTheory.Prod.sectR (0 : C) D) y) = y := by
  have h : (map (CategoryTheory.Prod.snd C D)).comp
      (map (CategoryTheory.Prod.sectR (0 : C) D)) = AddMonoidHom.id _ := by
    apply hom_ext
    simp
  exact DFunLike.congr_fun h y

private lemma fromProd_toProd :
    (fromProd (C := C) (D := D)).comp toProd = AddMonoidHom.id _ := by
  apply hom_ext
  intro X
  simpa [toProd, fromProd] using (of_eq_of_components X).symm

private lemma toProd_fromProd :
    (toProd (C := C) (D := D)).comp fromProd = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  rintro ⟨x, y⟩
  ext <;> simp [toProd, fromProd]

/-- Split `K₀` takes a product of additive categories to the product of their split
Grothendieck groups. -/
noncomputable def prodEquiv : SplitK0 (C × D) ≃+ SplitK0 C × SplitK0 D where
  toFun := toProd
  invFun := fromProd
  map_add' := map_add _
  left_inv x := DFunLike.congr_fun fromProd_toProd x
  right_inv x := DFunLike.congr_fun toProd_fromProd x

/-- The forward product equivalence is induced by the two projection functors. -/
@[simp]
lemma prodEquiv_apply (x : SplitK0 (C × D)) :
    prodEquiv x =
      (map (CategoryTheory.Prod.fst C D) x, map (CategoryTheory.Prod.snd C D) x) := by
  rfl

/-- The inverse product equivalence is the sum of the maps induced by inserting a zero object in
each coordinate. -/
lemma prodEquiv_symm_apply (x : SplitK0 C × SplitK0 D) :
    (prodEquiv (C := C) (D := D)).symm x =
      map (CategoryTheory.Prod.sectL C (0 : D)) x.1 +
        map (CategoryTheory.Prod.sectR (0 : C) D) x.2 := by
  rfl

/-- The product equivalence sends an object class to the pair of its component classes. -/
lemma prodEquiv_of (X : C × D) : prodEquiv (of X) = (of X.1, of X.2) := by
  simp [prodEquiv_apply]

/-- The inverse product equivalence sends a pair of object classes to the class of the paired
object. -/
@[simp]
lemma prodEquiv_symm_of (X : C) (Y : D) :
    (prodEquiv (C := C) (D := D)).symm (of X, of Y) = of (X, Y) := by
  apply (prodEquiv (C := C) (D := D)).injective
  simp

end Product

section Naturality

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [HasZeroObject C₁]
  [HasBinaryBiproducts C₁] [EssentiallySmall.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [HasZeroObject C₂]
  [HasBinaryBiproducts C₂] [EssentiallySmall.{w₂} C₂]
  {D₁ : Type u} [Category.{v} D₁] [Preadditive D₁] [HasZeroObject D₁]
  [HasBinaryBiproducts D₁] [EssentiallySmall.{w} D₁]
  {D₂ : Type u'} [Category.{v'} D₂] [Preadditive D₂] [HasZeroObject D₂]
  [HasBinaryBiproducts D₂] [EssentiallySmall.{w'} D₂]

/-- The split-`K₀` product equivalence is natural in additive functors in both variables. -/
theorem prodEquiv_naturality (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) [F.Additive] [G.Additive] :
    (prodEquiv (C := C₂) (D := D₂) : SplitK0 (C₂ × D₂) →+ _).comp (map (F.prod G)) =
      ((map F).prodMap (map G)).comp
        (prodEquiv (C := C₁) (D := D₁) : SplitK0 (C₁ × D₁) →+ _) := by
  apply hom_ext
  intro X
  simp

end Naturality

end SplitK0

end TauCeti
