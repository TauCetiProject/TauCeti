/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# Von Neumann regular categories

Every morphism in a von Neumann regular category has an inner inverse.
This property is preserved by opposition and reflected by fully faithful functors.

See D. Simson, *On pure global dimension of locally finitely presented
Grothendieck categories*, §1, p. 93, for the inner-inverse condition in the
preadditive setting.
-/

public section

open CategoryTheory

universe v u v' u'

namespace TauCeti

/-- A category is von Neumann regular when each morphism `f` has an inner inverse
`g`, so that `f ≫ g ≫ f = f`. -/
class IsVonNeumannRegularCategory (C : Type u) [Category.{v} C] : Prop where
  exists_comp_comp_eq_self ⦃X Y : C⦄ (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f

namespace IsVonNeumannRegularCategory

variable {C : Type u} [Category.{v} C]

/-- The opposite of a von Neumann regular category is von Neumann regular. -/
instance op [IsVonNeumannRegularCategory C] : IsVonNeumannRegularCategory Cᵒᵖ where
  exists_comp_comp_eq_self {_ _} f := by
    obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f.unop
    exact ⟨g.op, by simpa [Category.assoc] using congrArg Quiver.Hom.op hg⟩

/-- A fully faithful functor reflects von Neumann regularity. -/
theorem _root_.CategoryTheory.Functor.isVonNeumannRegularCategory_of_fullyFaithful
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful] [IsVonNeumannRegularCategory D] : IsVonNeumannRegularCategory C where
  exists_comp_comp_eq_self {_ _} f := by
    obtain ⟨g, hg⟩ := exists_comp_comp_eq_self (F.map f)
    exact ⟨F.preimage g, F.map_injective (by
      simpa only [Functor.map_comp, Functor.map_preimage] using hg)⟩

/-- Von Neumann regularity is invariant under passage to the opposite category. -/
@[simp] theorem op_iff : IsVonNeumannRegularCategory Cᵒᵖ ↔ IsVonNeumannRegularCategory C :=
  ⟨fun _ ↦ (opOpEquivalence C).inverse.isVonNeumannRegularCategory_of_fullyFaithful,
    fun _ ↦ inferInstance⟩

end IsVonNeumannRegularCategory

end TauCeti
