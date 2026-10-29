/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Stability under retracts: zero objects, inverse images, idempotent completeness

Zero objects are stable under retracts, and so is the inverse image of any property stable under
retracts; together these make the kernel `Functor.kernel` of every functor stable under retracts.

If idempotents split in a category `C` and an object property `P` is stable under retracts, then
idempotents split in the full subcategory of `P`: an idempotent of a `P`-object splits in `C`
through a retract of that object, which again satisfies `P`. This is how a full subcategory of an
abelian category, such as the finitely generated projective modules, inherits the splitting of
idempotents that makes indecomposability equivalent to the absence of nontrivial idempotent
endomorphisms.

## Main results

* `CategoryTheory.ObjectProperty.isStableUnderRetracts_isZero`: a retract of a zero object is a
  zero object.
* `CategoryTheory.ObjectProperty.isStableUnderRetracts_inverseImage`: the inverse image of a
  property stable under retracts is stable under retracts.
* `CategoryTheory.ObjectProperty.isIdempotentComplete_fullSubcategory`: the full subcategory of a
  property stable under retracts in an idempotent-complete category is idempotent complete.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

/-- **A retract of a zero object is a zero object**: maps into or out of the retract factor
through the zero object. -/
instance isStableUnderRetracts_isZero {C : Type*} [Category* C] :
    IsStableUnderRetracts (IsZero (C := C)) where
  of_retract {X Y} h hY := ⟨fun Z ↦ ⟨⟨h.i ≫ hY.to_ Z⟩, fun f ↦ by
      rw [← Category.id_comp f, ← h.retract, Category.assoc, hY.eq_of_src (h.r ≫ f)]; rfl⟩,
    fun Z ↦ ⟨⟨hY.from_ Z ≫ h.r⟩, fun f ↦ by
      rw [← Category.comp_id f, ← h.retract, ← Category.assoc, hY.eq_of_tgt (f ≫ h.i)]; rfl⟩⟩

/-- The inverse image of a property stable under retracts is stable under retracts, since
functors preserve retracts. -/
instance isStableUnderRetracts_inverseImage {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) [P.IsStableUnderRetracts] (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract h hY := P.prop_of_retract (h.map F) hY

/-- **A full subcategory stable under retracts of an idempotent-complete category is idempotent
complete**: an idempotent splits in the ambient category through a retract of its object, which
lies in the subcategory again. -/
instance isIdempotentComplete_fullSubcategory {C : Type*} [Category* C] [IsIdempotentComplete C]
    (P : ObjectProperty C) [P.IsStableUnderRetracts] : IsIdempotentComplete P.FullSubcategory where
  idempotents_split X p hp := by
    obtain ⟨Y, i, e, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split X.obj p.hom
      (by rw [← FullSubcategory.comp_hom, hp])
    exact ⟨⟨Y, P.prop_of_retract ⟨i, e, h₁⟩ X.property⟩, homMk i, homMk e,
      hom_ext _ h₁, hom_ext _ h₂⟩

end CategoryTheory.ObjectProperty
