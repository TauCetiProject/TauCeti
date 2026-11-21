/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Bifunctor
public import TauCeti.Algebra.Order.Antidiag.Prod
public import TauCeti.CategoryTheory.GradedObject.Map

/-!
# Graded bifunctor objects indexed by antidiagonals as biproducts

For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the fibre of
the addition map over `n` is `Finset.antidiagonal n` (`TauCeti.fiberEquivAntidiagonal`). When
`CategoryTheory.GradedObject.mapBifunctorMapObj` exists, that is when the coproducts over all the
fibres of the addition map exist (`HasMap`), and the summands in degree `n` also have a biproduct
(both hold when `C₃` has finite biproducts, since antidiagonals are finite), its degree `n` part is
this biproduct indexed by `Finset.antidiagonal n`
(`CategoryTheory.GradedObject.mapBifunctorMapObjIsoBiproduct`). This is the special case of
`CategoryTheory.GradedObject.mapObjIsoBiproductOfEquiv`. The comparison is natural
(`CategoryTheory.GradedObject.mapBifunctorMapMap_mapBifunctorMapObjIsoBiproduct_hom`). The tensor
product of graded objects is a special case
(`CategoryTheory.GradedObject.Monoidal.tensorObjIsoBiproduct`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.GradedObject

section Antidiagonal

variable {I : Type*} [Add I] [Finset.HasAntidiagonal I]
  {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [HasZeroMorphisms C₃]
  (X : GradedObject I C₁) (Y : GradedObject I C₂) (F : C₁ ⥤ C₂ ⥤ C₃)
  [HasMap (((mapBifunctor F I I).obj X).obj Y) (fun x ↦ x.1 + x.2)] (n : I)
  [HasBiproduct fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)]

-- The summands of the reindexed biproduct are by definition the `(F.obj (X i)).obj (Y j)`, since
-- `TauCeti.fiberEquivAntidiagonal` does not change the underlying pairs.
private instance : HasBiproduct fun a : Finset.antidiagonal n ↦
    (((mapBifunctor F I I).obj X).obj Y) ((TauCeti.fiberEquivAntidiagonal n).symm a).val :=
  ‹HasBiproduct fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)›

/-- For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the
coproduct of the `(F.obj (X i)).obj (Y j)` with `i + j = n` is the biproduct of these objects
indexed by `Finset.antidiagonal n`: this is `CategoryTheory.GradedObject.mapObjIsoBiproductOfEquiv`
for the equivalence `TauCeti.fiberEquivAntidiagonal` of the fibre of the addition map with
`Finset.antidiagonal n`. It needs the coproducts over all the fibres of the addition map (the
`HasMap` hypothesis) and the biproduct of the summands in degree `n`. -/
def mapBifunctorMapObjIsoBiproduct :
    mapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y n ≅
      ⨁ fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2) :=
  -- `mapBifunctorMapObj` is by definition `mapObj` of the graded object of the summands
  mapObjIsoBiproductOfEquiv (((mapBifunctor F I I).obj X).obj Y) _
    (TauCeti.fiberEquivAntidiagonal n)

/-- `mapBifunctorMapObjIsoBiproduct` sends the summand `(F.obj (X i)).obj (Y j)` to the
corresponding summand of the biproduct. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_hom (i j : I) (h : i + j = n) :
    ιMapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y i j n h ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).hom =
      biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2))
        ⟨(i, j), Finset.mem_antidiagonal.2 h⟩ :=
  -- `ιMapBifunctorMapObj` is by definition `ιMapObj`, and the pair `(i, j)` is by definition the
  -- image of `⟨(i, j), _⟩` under `(TauCeti.fiberEquivAntidiagonal n).symm`
  ιMapObj_mapObjIsoBiproductOfEquiv_hom (((mapBifunctor F I I).obj X).obj Y) _
    (TauCeti.fiberEquivAntidiagonal n) ⟨(i, j), Finset.mem_antidiagonal.2 h⟩

/-- The inverse of `mapBifunctorMapObjIsoBiproduct` sends each summand of the biproduct to the
corresponding summand of `mapBifunctorMapObj`. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_inv (x : Finset.antidiagonal n) :
    biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)) x ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).inv =
      ιMapBifunctorMapObj F _ X Y x.val.1 x.val.2 n (Finset.mem_antidiagonal.1 x.property) :=
  -- as for `ι_mapBifunctorMapObjIsoBiproduct_hom`
  ι_mapObjIsoBiproductOfEquiv_inv (((mapBifunctor F I I).obj X).obj Y) _
    (TauCeti.fiberEquivAntidiagonal n) x

variable {X Y} {X' : GradedObject I C₁} {Y' : GradedObject I C₂}
  [HasMap (((mapBifunctor F I I).obj X').obj Y') (fun x ↦ x.1 + x.2)]
  [HasBiproduct fun x : Finset.antidiagonal n ↦ (F.obj (X' x.val.1)).obj (Y' x.val.2)]

/-- **Naturality of `mapBifunctorMapObjIsoBiproduct`**: under these identifications, the map
induced by morphisms `f` and `g` of graded objects is the map of biproducts given on the summand
of `(i, j)` by `F` applied to `f i` and `g j`. -/
@[reassoc]
lemma mapBifunctorMapMap_mapBifunctorMapObjIsoBiproduct_hom (f : X ⟶ X') (g : Y ⟶ Y') :
    mapBifunctorMapMap F (fun x ↦ x.1 + x.2) f g n ≫
        (mapBifunctorMapObjIsoBiproduct X' Y' F n).hom =
      (mapBifunctorMapObjIsoBiproduct X Y F n).hom ≫ biproduct.map fun x ↦
        (F.map (f x.val.1)).app (Y x.val.2) ≫ (F.obj (X' x.val.1)).map (g x.val.2) :=
  -- `mapBifunctorMapMap` is by definition `mapMap` of the graded map of summands, and
  -- `TauCeti.fiberEquivAntidiagonal` does not change the underlying pairs
  mapMap_mapObjIsoBiproductOfEquiv_hom _ (TauCeti.fiberEquivAntidiagonal n)
    (((mapBifunctor F I I).map f).app Y ≫ ((mapBifunctor F I I).obj X').map g)

end Antidiagonal

end CategoryTheory.GradedObject
