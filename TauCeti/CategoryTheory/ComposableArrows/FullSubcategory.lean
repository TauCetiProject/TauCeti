/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Groupoid

/-!
# Strings in full subcategories

The strings in a full subcategory are exactly the ambient strings all of whose vertices
satisfy its object property. For a groupoid and an isomorphism-invariant property, testing
one vertex suffices. These range descriptions identify the nerve of a saturated restriction
without replacing any of its arrows by germs.
-/

public section

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C) (n : ℕ)

/-- A string comes from the full subcategory precisely when every vertex satisfies its
object property. No closure condition on the property is required. -/
theorem range_mapComposableArrows_ι :
    Set.range (P.ι.mapComposableArrows n).obj = {F | ∀ i, P (F.obj i)} := by
  ext F
  constructor
  · rintro ⟨G, rfl⟩ i
    exact (G.obj i).property
  · intro hF
    exact ⟨P.lift F hF, rfl⟩

/-- In a groupoid, a string lies in a saturated full subcategory precisely when its first
vertex does. In particular the restriction retains every isotropy arrow at that vertex. -/
theorem range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms [IsGroupoid C]
    [P.IsClosedUnderIsomorphisms] :
    Set.range (P.ι.mapComposableArrows n).obj = {F | P (F.obj 0)} := by
  rw [range_mapComposableArrows_ι]
  ext F
  exact ⟨fun h ↦ h 0, fun h i ↦ P.prop_of_iso (asIso (F.map (homOfLE (Fin.zero_le i)))) h⟩

end CategoryTheory.ObjectProperty
