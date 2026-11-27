/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The hull of subquotients of finite direct sums of an object

For an object `X` of a category with finite biproducts, `TauCeti.subquotientHull X` is the
property of being a subquotient of a finite direct sum of copies of `X`: an object `Y` belongs to
it when there are a finite type `ι`, a monomorphism `Z ⟶ ⨁ (fun _ : ι ↦ X)` and an epimorphism
`Z ⟶ Y`.

In an abelian category this is the smallest property of objects containing `X` and closed under
subobjects, quotients and finite products (`TauCeti.subquotientHull_le`). In the reconstruction
of a category with a fibre functor from finite-dimensional algebras, the full subcategory
`⟨X⟩` it defines is the finite piece attached to `X`: the fibre functor restricted to `⟨X⟩` has
a finite-dimensional endomorphism algebra. The hulls are ordered by membership
(`TauCeti.subquotientHull_le_iff`), so nested hulls give the transition maps between these
algebras.

Functors preserving finite biproducts, monomorphisms and epimorphisms send hulls into the
hulls of their images, and equivalences preserve and reflect hull membership. These transport
results need only preadditive categories with finite biproducts, without abelianness.

## Main definitions and results

* `TauCeti.subquotientHull X`: subquotients of finite direct sums of copies of `X`.
* `TauCeti.subquotientHull_self`, `TauCeti.subquotientHull_biproduct`: `X` and finite
  biproducts of members are members.
* The hull is closed under subobjects, quotients and finite products, and contains zero.
* `TauCeti.subquotientHull_le`: the hull is the smallest such property containing `X`.
* `TauCeti.subquotientHull_le_iff`: `⟨Y⟩ ≤ ⟨X⟩` if and only if `Y ∈ ⟨X⟩`.
* `CategoryTheory.Functor.map_subquotientHull`: preservation of hull membership by functors
  preserving finite biproducts, monomorphisms and epimorphisms.
* `CategoryTheory.Equivalence.subquotientHull_obj_iff`: preservation and reflection of hull
  membership under equivalences.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, §2, the categories `⟨X⟩` before Lemma 2.13.
-/

public section

namespace TauCeti

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

section Definition

variable [Preadditive C] [HasFiniteBiproducts C]

/-- The objects that are subquotients of a finite direct sum of copies of `X`: `Y` satisfies
`subquotientHull X` when some subobject `Z` of `⨁ (fun _ : ι ↦ X)`, for a finite type `ι`, has
`Y` as a quotient. -/
def subquotientHull (X : C) : ObjectProperty C := fun Y ↦
  ∃ (ι : Type) (_ : Finite ι) (Z : C) (i : Z ⟶ ⨁ fun _ : ι ↦ X) (p : Z ⟶ Y), Mono i ∧ Epi p

variable {X Y : C}

/-- Unfolding `subquotientHull`: `Y` is a quotient of a subobject of a finite power of `X`. -/
theorem subquotientHull_iff : subquotientHull X Y ↔
    ∃ (ι : Type) (_ : Finite ι) (Z : C) (i : Z ⟶ ⨁ fun _ : ι ↦ X) (p : Z ⟶ Y),
      Mono i ∧ Epi p :=
  Iff.rfl

/-- A quotient of a subobject of a finite direct sum of copies of `X` lies in the hull of `X`. -/
theorem subquotientHull.mk {ι : Type} [Finite ι] {Z : C} (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i]
    (p : Z ⟶ Y) [Epi p] : subquotientHull X Y :=
  ⟨ι, inferInstance, Z, i, p, inferInstance, inferInstance⟩

/-- A subobject of a finite direct sum of copies of `X` lies in the hull of `X`. -/
theorem subquotientHull.of_mono {ι : Type} [Finite ι] (i : Y ⟶ ⨁ fun _ : ι ↦ X) [Mono i] :
    subquotientHull X Y :=
  subquotientHull.mk i (𝟙 Y)

/-- A finite direct sum of copies of `X` lies in the hull of `X`. -/
theorem subquotientHull_biproduct_const (ι : Type) [Finite ι] :
    subquotientHull X (⨁ fun _ : ι ↦ X) :=
  subquotientHull.of_mono (𝟙 _)

/-- `X` lies in its own hull. -/
theorem subquotientHull_self : subquotientHull X X :=
  subquotientHull.of_mono (biproduct.ι (fun _ : Unit ↦ X) ())

/-- The hull of `X` is closed under quotients. -/
instance : (subquotientHull X).IsClosedUnderQuotients where
  prop_of_epi f _ := by
    rintro ⟨ι, _, Z, i, p, _, _⟩
    exact subquotientHull.mk i (p ≫ f)

/-- A finite biproduct of members of the hull of `X` lies in the hull of `X`. -/
theorem subquotientHull_biproduct {J : Type} [Finite J] (f : J → C)
    (h : ∀ j, subquotientHull X (f j)) : subquotientHull X (⨁ f) := by
  choose ι hι Z i p _ _ using h
  exact subquotientHull.mk
    (biproduct.map i ≫ (biproductBiproductIso ι fun _ _ ↦ X).hom) (biproduct.map p)

/-- The hull of `X` is closed under finite products. -/
instance : (subquotientHull X).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ :=
    { limitsOfShape_le := by
        rintro W ⟨p⟩
        exact (subquotientHull X).prop_of_iso
          (IsLimit.conePointUniqueUpToIso (biproduct.isLimit _)
            ((IsLimit.postcomposeHomEquiv (Discrete.natIsoFunctor (F := p.diag)) _).invFun
              p.isLimit))
          (subquotientHull_biproduct _ fun j ↦ p.prop_diag_obj ⟨j⟩) }

/-- A zero object lies in the hull of every object. -/
theorem subquotientHull_of_isZero (hY : IsZero Y) : subquotientHull X Y :=
  have : Mono (hY.to_ (⨁ fun _ : Empty ↦ X)) := hY.mono _
  subquotientHull.of_mono (hY.to_ (⨁ fun _ : Empty ↦ X))

open ZeroObject in
instance [HasZeroObject C] : (subquotientHull X).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, subquotientHull_of_isZero (isZero_zero C)⟩

/-- The hull of `X` is contained in every property of objects containing `X` and closed under
subobjects, quotients and finite products. In an abelian category the hull is itself such a
property, so it is the smallest one. -/
theorem subquotientHull_le (P : ObjectProperty C) [P.IsClosedUnderSubobjects]
    [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts] (hX : P X) :
    subquotientHull X ≤ P := by
  rintro Y ⟨ι, _, Z, i, p, _, _⟩
  have hsum : P (⨁ fun _ : ι ↦ X) :=
    P.prop_of_iso (biproduct.isoProduct _).symm (P.prop_product fun _ ↦ hX)
  exact P.prop_of_epi p (P.prop_of_mono i hsum)

end Definition

section Abelian

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] {X Y : C}

/-- In an abelian category the hull of `X` is closed under subobjects: a subobject of a quotient
of `Z` is a quotient of a subobject of `Z`, namely of a pullback. -/
instance : (subquotientHull X).IsClosedUnderSubobjects where
  prop_of_mono {W Y} f _ := by
    rintro ⟨ι, _, Z, i, p, _, _⟩
    exact subquotientHull.mk (pullback.fst p f ≫ i) (pullback.snd p f)

/-- If `Y` lies in the hull of `X`, then so does every member of the hull of `Y`. -/
theorem subquotientHull_le_of_mem (h : subquotientHull X Y) :
    subquotientHull Y ≤ subquotientHull X :=
  subquotientHull_le _ h

/-- The hull of `Y` is contained in the hull of `X` exactly when `Y` lies in the hull of `X`. -/
theorem subquotientHull_le_iff : subquotientHull Y ≤ subquotientHull X ↔ subquotientHull X Y :=
  ⟨fun h ↦ h _ subquotientHull_self, subquotientHull_le_of_mem⟩

end Abelian

end TauCeti

namespace CategoryTheory

open Limits TauCeti

universe v' u'

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]

/-- A functor preserving finite biproducts, monomorphisms and epimorphisms maps a finite-sum
and subquotient hull into the hull of the image. -/
theorem Functor.map_subquotientHull (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteBiproducts F] [F.PreservesMonomorphisms] [F.PreservesEpimorphisms]
    {X Y : C} (h : subquotientHull X Y) : subquotientHull (F.obj X) (F.obj Y) := by
  obtain ⟨ι, _, Z, i, p, _, _⟩ := h
  exact subquotientHull.mk (F.map i ≫ (F.mapBiproduct (fun _ : ι ↦ X)).hom) (F.map p)

/-- An equivalence identifies membership in finite-sum and subquotient hulls. -/
@[simp]
theorem Equivalence.subquotientHull_obj_iff (E : C ≌ D) (X Y : C) :
    subquotientHull (E.functor.obj X) (E.functor.obj Y) ↔ subquotientHull X Y := by
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  refine ⟨fun h ↦ ?_, E.functor.map_subquotientHull⟩
  obtain ⟨ι, _, Z, i, p, _, _⟩ := E.inverse.map_subquotientHull h
  exact subquotientHull.mk
    (i ≫ (biproduct.mapIso (fun _ : ι ↦ (E.unitIso.app X).symm)).hom)
    (p ≫ (E.unitIso.app Y).inv)

end

end CategoryTheory
