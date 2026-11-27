/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import TauCeti.CategoryTheory.Abelian.SubquotientHull

/-!
# Sums of units

An object `X` of a monoidal category with finite biproducts is a *sum of units*,
`TauCeti.IsSumOfUnits X`, when it is isomorphic to a finite direct sum of copies of the tensor
unit `𝟙_ C`.

For the representations of an affine group scheme these are the representations on which the
group acts trivially, and the connectedness criterion for neutral Tannakian categories is phrased
in terms of them and of finite-sum and subquotient hulls closed under tensor products. Every sum of
units lies in the hull `TauCeti.subquotientHull (𝟙_ C)` of the unit; the converse holds for
finite comodules, where both are characterized by matrix coefficients.

## Main declarations

* `TauCeti.IsSumOfUnits`: being isomorphic to a finite direct sum of copies of `𝟙_ C`.
* `TauCeti.IsSumOfUnits.of_iso`: the property is invariant under isomorphism.
* `TauCeti.isSumOfUnits_tensorUnit`: the unit is a sum of units.
* `TauCeti.IsSumOfUnits.subquotientHull_tensorUnit`: a sum of units lies in the hull of the unit.
* `CategoryTheory.Functor.map_isSumOfUnits`: strong monoidal functors preserving finite products
  send sums of units to sums of units.
* `CategoryTheory.Equivalence.isSumOfUnits_obj_iff`: monoidal equivalences preserve and reflect
  sums of units.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Corollary 2.22.
-/

public section

namespace TauCeti

open CategoryTheory Limits MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y : C}

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- An object is a **sum of units** when it is isomorphic to a finite direct sum of copies of the
tensor unit. -/
def IsSumOfUnits (X : C) : Prop :=
  ∃ (ι : Type) (_ : Finite ι), Nonempty (X ≅ ⨁ fun _ : ι ↦ 𝟙_ C)

/-- Unfolding `IsSumOfUnits`. -/
theorem isSumOfUnits_iff :
    IsSumOfUnits X ↔ ∃ (ι : Type) (_ : Finite ι), Nonempty (X ≅ ⨁ fun _ : ι ↦ 𝟙_ C) :=
  Iff.rfl

/-- An object isomorphic to a finite direct sum of copies of the unit is a sum of units. -/
theorem IsSumOfUnits.mk {ι : Type} [Finite ι] (e : X ≅ ⨁ fun _ : ι ↦ 𝟙_ C) : IsSumOfUnits X :=
  ⟨ι, inferInstance, ⟨e⟩⟩

/-- Being a sum of units is invariant under isomorphism. -/
theorem IsSumOfUnits.of_iso (h : IsSumOfUnits X) (e : X ≅ Y) : IsSumOfUnits Y := by
  obtain ⟨ι, _, ⟨f⟩⟩ := h
  exact .mk (e.symm ≪≫ f)

/-- A finite direct sum of copies of the unit is a sum of units. -/
@[simp]
theorem isSumOfUnits_biproduct_const (ι : Type) [Finite ι] :
    IsSumOfUnits (⨁ fun _ : ι ↦ 𝟙_ C) :=
  .mk (Iso.refl _)

variable (C) in
/-- The tensor unit is a sum of units. -/
@[simp]
theorem isSumOfUnits_tensorUnit : IsSumOfUnits (𝟙_ C) :=
  .mk (biproductUniqueIso (fun _ : Unit ↦ 𝟙_ C)).symm

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] [HasFiniteBiproducts C]

/-- A sum of units lies in the finite-sum and subquotient hull of the unit. -/
theorem IsSumOfUnits.subquotientHull_tensorUnit (h : IsSumOfUnits X) :
    subquotientHull (𝟙_ C) X := by
  obtain ⟨ι, _, ⟨e⟩⟩ := h
  exact subquotientHull.of_mono e.hom

end Preadditive

end TauCeti

namespace CategoryTheory

open Limits MonoidalCategory TauCeti

universe v' u'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [HasZeroMorphisms D] [HasFiniteBiproducts D]

/-- A strong monoidal functor preserving finite products sends sums of units to sums of
units. -/
theorem Functor.map_isSumOfUnits (F : C ⥤ D) [F.Monoidal] [PreservesFiniteProducts F]
    {X : C} (h : IsSumOfUnits X) : IsSumOfUnits (F.obj X) := by
  obtain ⟨ι, _, ⟨e⟩⟩ := h
  exact .mk (F.mapIso (e ≪≫ biproduct.isoProduct _) ≪≫ PreservesProduct.iso F _ ≪≫
    Pi.mapIso (fun _ : ι ↦ (Functor.Monoidal.εIso F).symm) ≪≫
    (biproduct.isoProduct _).symm)

/-- A monoidal equivalence preserves and reflects finite sums of tensor units. -/
@[simp]
theorem Equivalence.isSumOfUnits_obj_iff (E : C ≌ D) [E.functor.Monoidal] (X : C) :
    IsSumOfUnits (E.functor.obj X) ↔ IsSumOfUnits X := by
  let := E.inverseMonoidal
  exact ⟨fun h ↦ (E.inverse.map_isSumOfUnits h).of_iso (E.unitIso.app X).symm,
    E.functor.map_isSumOfUnits⟩

end CategoryTheory
