/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Coproducts over the fibres of a graded object as biproducts

Let `X : GradedObject I C` and `p : I → J` be such that `X.mapObj p` exists, that is the coproduct
of the `X i` over every fibre of `p` exists (`CategoryTheory.GradedObject.HasMap`). Given an
equivalence `e` of a fibre `p ⁻¹' {n}` with a type `A` such that the objects `X (e.symm a)` also
have a biproduct, for instance a finite type when `C` has finite biproducts, `X.mapObj p n` is this
biproduct (`CategoryTheory.GradedObject.mapObjIsoBiproductOfEquiv`), with the expected inclusions.
It is the comparison of the coproduct reindexed along `e` (`Cofan.isColimitEquivOfEquiv`) with the
biproduct. The comparison is natural: a map of graded objects induces on these biproducts the map
`biproduct.map` of its components
(`CategoryTheory.GradedObject.mapMap_mapObjIsoBiproductOfEquiv_hom`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.GradedObject

variable {I J A C : Type*} [Category* C] [HasZeroMorphisms C] (X : GradedObject I C) (p : I → J)
  [X.HasMap p] {n : J} (e : p ⁻¹' {n} ≃ A) [HasBiproduct fun a ↦ X (e.symm a).val]

/-- The coproduct `X.mapObj p n`, reindexed along `e`, is a colimit cofan over `A`. -/
private def isColimitCofanMapObjReindex :
    IsColimit (Cofan.mk (X.mapObj p n) fun a ↦ (X.cofanMapObj p n).inj (e.symm a)) :=
  Cofan.isColimitEquivOfEquiv e.symm (X.cofanMapObj p n) (X.isColimitCofanMapObj p n)

/-- The coproduct `X.mapObj p n` of the `X i` with `p i = n` is the biproduct of these objects,
indexed through an equivalence `e` of the fibre `p ⁻¹' {n}` with a type `A`. This needs the
coproducts over all the fibres of `p` (`X.HasMap p`) and the biproduct over the fibre of `n`. -/
def mapObjIsoBiproductOfEquiv : X.mapObj p n ≅ ⨁ fun a ↦ X (e.symm a).val :=
  IsColimit.coconePointUniqueUpToIso (isColimitCofanMapObjReindex X p e)
    (biproduct.isColimit fun a ↦ X (e.symm a).val)

/-- `mapObjIsoBiproductOfEquiv` sends the summand `X (e.symm a)` to the summand of index `a`. -/
@[reassoc (attr := simp)]
lemma ιMapObj_mapObjIsoBiproductOfEquiv_hom (a : A) :
    X.ιMapObj p (e.symm a).val n (Set.mem_singleton_iff.1 (e.symm a).property) ≫
        (X.mapObjIsoBiproductOfEquiv p e).hom = biproduct.ι (fun a ↦ X (e.symm a).val) a :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitCofanMapObjReindex X p e)
    (biproduct.isColimit fun a ↦ X (e.symm a).val) ⟨a⟩

/-- The inverse of `mapObjIsoBiproductOfEquiv` sends the summand of index `a` to the summand
`X (e.symm a)` of `X.mapObj p n`. -/
@[reassoc (attr := simp)]
lemma ι_mapObjIsoBiproductOfEquiv_inv (a : A) :
    biproduct.ι (fun a ↦ X (e.symm a).val) a ≫ (X.mapObjIsoBiproductOfEquiv p e).inv =
      X.ιMapObj p (e.symm a).val n (Set.mem_singleton_iff.1 (e.symm a).property) :=
  IsColimit.comp_coconePointUniqueUpToIso_inv (isColimitCofanMapObjReindex X p e)
    (biproduct.isColimit fun a ↦ X (e.symm a).val) ⟨a⟩

variable {X} {Y : GradedObject I C} [Y.HasMap p] [HasBiproduct fun a ↦ Y (e.symm a).val]

/-- **Naturality of `mapObjIsoBiproductOfEquiv`**: under these identifications, the map induced by
a morphism `φ` of graded objects is the map of biproducts given by the components of `φ`. -/
@[reassoc]
lemma mapMap_mapObjIsoBiproductOfEquiv_hom (φ : X ⟶ Y) :
    mapMap φ p n ≫ (Y.mapObjIsoBiproductOfEquiv p e).hom =
      (X.mapObjIsoBiproductOfEquiv p e).hom ≫ biproduct.map fun a ↦ φ (e.symm a).val := by
  rw [← Iso.inv_comp_eq]
  refine biproduct.hom_ext' _ _ fun a ↦ ?_
  simp

end CategoryTheory.GradedObject
