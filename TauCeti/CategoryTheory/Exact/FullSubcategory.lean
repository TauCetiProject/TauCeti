/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Injective

/-!
# Relative projectives and injectives in full subcategories

An extension-closed full subcategory inherits an exact structure from its ambient category.
Ambient relative projectives and injectives remain projective and injective for that structure:
the inclusion preserves conflations and fullness transports lifts and extensions back inside.
The converse requires presentations inside the subcategory; it need not hold in general.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C}

/-- An ambient relatively projective object lying in an extension-closed full subcategory is
relatively projective for the induced exact structure. -/
theorem isProjective_fullSubcategory_of_isProjective {P : ObjectProperty C} [P.ContainsZero]
    [P.IsClosedUnderBinaryProducts] (hP : E.IsExtensionClosed P) (X : P.FullSubcategory)
    (hX : E.isProjective X.obj) : (E.fullSubcategory P hP).isProjective X := by
  rw [isProjective_iff]
  rw [isProjective_iff] at hX
  intro Y Z p hp f
  obtain ⟨g, hg⟩ := hX ((E.isConflationExact_ι hP).map_isDeflation hp) (P.ι.map f)
  exact ⟨ObjectProperty.homMk g, P.ι.map_injective (by simpa using hg)⟩

/-- An ambient relatively injective object lying in an extension-closed full subcategory is
relatively injective for the induced exact structure. -/
theorem isInjective_fullSubcategory_of_isInjective {P : ObjectProperty C} [P.ContainsZero]
    [P.IsClosedUnderBinaryProducts] (hP : E.IsExtensionClosed P) (X : P.FullSubcategory)
    (hX : E.isInjective X.obj) : (E.fullSubcategory P hP).isInjective X := by
  rw [isInjective_iff]
  rw [isInjective_iff] at hX
  intro Y Z i hi f
  obtain ⟨g, hg⟩ := hX ((E.isConflationExact_ι hP).map_isInflation hi) (P.ι.map f)
  exact ⟨ObjectProperty.homMk g, P.ι.map_injective (by simpa using hg)⟩

end TauCeti.ExactStructure
