/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Localization.Triangulated

/-!
# The bounded below derived category of an exact category

Let `E` be an exact structure on an additive category `C`. An object of the homotopy category is
**homotopy acyclic** when it is isomorphic to the homotopy class of an `E`-acyclic complex. By
Neeman's lemma (`TauCeti.ExactStructure.acyclic_mappingCone`) these objects form a triangulated
subcategory of the homotopy category, and so of Mathlib's homotopy category `K⁺(C)` of bounded
below complexes, `HomotopyCategory.Plus C`. The **bounded below derived category** `D⁺(E)` is the
Verdier quotient of `K⁺(C)` by it, with its localized triangulated structure (Bühler, Section 10).

As for the bounded derived category `TauCeti.ExactStructure.BoundedDerivedCategory`, the subcategory
is the closure under isomorphisms of the classes of acyclic complexes, since a complex homotopy
equivalent to an acyclic one need not be acyclic when `C` is not idempotent complete.

## Main definitions

* `TauCeti.ExactStructure.homotopyAcyclic`: the objects of the homotopy category isomorphic to the
  class of an acyclic complex.
* `TauCeti.ExactStructure.acyclicPlus`: the same objects in `K⁺(C)`.
* `TauCeti.ExactStructure.PlusDerivedCategory`: the bounded below derived category `D⁺(E)`, with
  the quotient functor `TauCeti.ExactStructure.PlusDerivedCategory.Q`.

## Main results

* `TauCeti.ExactStructure.homotopyAcyclic_trW_quotient_map`: a map of complexes with acyclic
  mapping cone becomes invertible in the localization.

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

/-- The objects of the homotopy category isomorphic to the class of an acyclic complex. -/
def homotopyAcyclic : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun X ↦
  ∃ K : CochainComplex C ℤ, E.acyclic K ∧ Nonempty (X ≅ (HomotopyCategory.quotient C (.up ℤ)).obj K)

/-- An object of the homotopy category is homotopy acyclic exactly when it is isomorphic to the
class of an acyclic complex. -/
theorem homotopyAcyclic_iff (X : HomotopyCategory C (.up ℤ)) :
    E.homotopyAcyclic X ↔
      ∃ K : CochainComplex C ℤ, E.acyclic K ∧
        Nonempty (X ≅ (HomotopyCategory.quotient C (.up ℤ)).obj K) :=
  Iff.rfl

/-- The class of an acyclic complex is homotopy acyclic. -/
theorem homotopyAcyclic_quotient_obj {K : CochainComplex C ℤ} (ha : E.acyclic K) :
    E.homotopyAcyclic ((HomotopyCategory.quotient C (.up ℤ)).obj K) :=
  ⟨K, ha, ⟨Iso.refl _⟩⟩

instance : E.homotopyAcyclic.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨K, ha, ⟨e'⟩⟩ ↦ ⟨K, ha, ⟨e.symm ≪≫ e'⟩⟩

instance : E.homotopyAcyclic.ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient C (.up ℤ)).obj 0,
    Functor.map_isZero _ (isZero_zero _), E.homotopyAcyclic_quotient_obj
      (E.acyclic.prop_of_isZero (isZero_zero _))⟩

instance : E.homotopyAcyclic.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ⟨K, ha, ⟨e⟩⟩ ↦ ⟨K⟦n⟧, E.acyclic.le_shift n K ha,
    ⟨(shiftFunctor _ n).mapIso e ≪≫
      ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app K⟩⟩⟩

instance : E.homotopyAcyclic.IsTriangulatedClosed₃ where
  ext₃' T hT := fun ⟨K₁, ha₁, ⟨e₁⟩⟩ ⟨K₂, ha₂, ⟨e₂⟩⟩ ↦ by
    obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
    refine ObjectProperty.le_isoClosure _ _ ⟨CochainComplex.mappingCone f,
      E.acyclic_mappingCone f ha₁ ha₂,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f) e₁ e₂ ?_)⟩⟩
    -- The goal is stated through the triangle of the mapping cone; its first morphism is the
    -- class of `f`.
    change T.mor₁ ≫ e₂.hom = e₁.hom ≫ (HomotopyCategory.quotient C (.up ℤ)).map f
    rw [hf]
    simp

instance : E.homotopyAcyclic.IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- **A map of complexes with acyclic mapping cone is inverted in the derived category**: its class
in the homotopy category lies in `E.homotopyAcyclic.trW`. -/
theorem homotopyAcyclic_trW_quotient_map {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hf : E.acyclic (CochainComplex.mappingCone f)) :
    E.homotopyAcyclic.trW ((HomotopyCategory.quotient C (.up ℤ)).map f) :=
  (E.homotopyAcyclic.trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).2
      (E.homotopyAcyclic_quotient_obj hf)

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
