/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Localization.Triangulated

/-!
# The bounded below derived category of an exact category

Let `E` be an exact structure on an additive category `C`. The homotopy acyclic objects
(`TauCeti.ExactStructure.homotopyAcyclic`, the objects isomorphic to the class of an `E`-acyclic
complex) form a triangulated subcategory of the homotopy category, and so of Mathlib's homotopy
category `K⁺(C)` of bounded below complexes, `HomotopyCategory.Plus C`. The **bounded below
derived category** `D⁺(E)` is the Verdier quotient of `K⁺(C)` by it, with its localized
triangulated structure (Bühler, Section 10).

As for the bounded derived category `TauCeti.ExactStructure.BoundedDerivedCategory`, the subcategory
is the closure under isomorphisms of the classes of acyclic complexes, since a complex homotopy
equivalent to an acyclic one need not be acyclic when `C` is not idempotent complete.

## Main definitions

* `TauCeti.ExactStructure.acyclicPlus`: the acyclic objects of `K⁺(C)`.
* `TauCeti.ExactStructure.PlusDerivedCategory`: the bounded below derived category `D⁺(E)`, with
  the quotient functor `TauCeti.ExactStructure.PlusDerivedCategory.Q`.

## Main results

* `TauCeti.ExactStructure.acyclicPlus_trW_iff`: the morphisms inverted in `D⁺(E)` are those whose
  image in the homotopy category is in `E.homotopyAcyclic.trW`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 10.
* Amnon Neeman, *The derived category of an exact category*, J. Algebra **135** (1990),
  388--394.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- The acyclic objects of `K⁺(C)`, as a triangulated subcategory. -/
def acyclicPlus : ObjectProperty (HomotopyCategory.Plus C) :=
  E.homotopyAcyclic.inverseImage (HomotopyCategory.Plus.ι C)

/-- An object of `K⁺(C)` is acyclic exactly when its image in the homotopy category is. -/
@[simp]
theorem acyclicPlus_iff (X : HomotopyCategory.Plus C) :
    E.acyclicPlus X ↔ E.homotopyAcyclic ((HomotopyCategory.Plus.ι C).obj X) :=
  Iff.rfl

instance : E.acyclicPlus.IsTriangulated := by
  dsimp only [acyclicPlus]
  infer_instance

/-- A morphism of `K⁺(C)` is in `E.acyclicPlus.trW` exactly when its image in the homotopy category
is in `E.homotopyAcyclic.trW`. -/
theorem acyclicPlus_trW_iff {X Y : HomotopyCategory.Plus C} (f : X ⟶ Y) :
    E.acyclicPlus.trW f ↔ E.homotopyAcyclic.trW f.hom :=
  ObjectProperty.inverseImage_trW_iff _ _ f

/-- The **bounded below derived category** `D⁺(E)` of an exact category: the Verdier quotient of
the homotopy category `K⁺(C)` of bounded below complexes by the acyclic complexes. -/
abbrev PlusDerivedCategory :=
  E.acyclicPlus.trW.Localization

namespace PlusDerivedCategory

/-- The Verdier quotient functor `K⁺(C) ⥤ D⁺(E)`. -/
noncomputable def Q : HomotopyCategory.Plus C ⥤ E.PlusDerivedCategory :=
  E.acyclicPlus.trW.Q

instance : (Q E).IsLocalization E.acyclicPlus.trW := by
  dsimp only [Q]
  infer_instance

noncomputable instance : Preadditive E.PlusDerivedCategory :=
  Localization.preadditive (Q E) E.acyclicPlus.trW

instance : (Q E).Additive :=
  Localization.functor_additive (Q E) E.acyclicPlus.trW

noncomputable instance : HasZeroObject E.PlusDerivedCategory :=
  (Q E).hasZeroObject_of_additive

noncomputable instance : HasShift E.PlusDerivedCategory ℤ :=
  HasShift.localized (Q E) E.acyclicPlus.trW ℤ

noncomputable instance : (Q E).CommShift ℤ :=
  Functor.CommShift.localized (Q E) E.acyclicPlus.trW ℤ

instance (n : ℤ) : (shiftFunctor E.PlusDerivedCategory n).Additive := by
  rw [Localization.functor_additive_iff (Q E) E.acyclicPlus.trW]
  exact Functor.additive_of_iso ((Q E).commShiftIso n)

noncomputable instance : Pretriangulated E.PlusDerivedCategory :=
  Triangulated.Localization.pretriangulated (Q E) E.acyclicPlus.trW

instance : (Q E).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor (Q E) E.acyclicPlus.trW

instance : IsTriangulated E.PlusDerivedCategory :=
  Triangulated.Localization.isTriangulated (Q E) E.acyclicPlus.trW

end PlusDerivedCategory

end TauCeti.ExactStructure
