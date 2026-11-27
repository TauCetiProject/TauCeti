/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# Von Neumann regular categories

A category is von Neumann regular if every morphism `f : X ⟶ Y` has an inner inverse
`g : Y ⟶ X` with `f ≫ g ≫ f = f`. The condition is invariant under passing to the opposite
category.

See Simson, *On pure global dimension of locally finitely presented Grothendieck categories*,
§1, before Proposition 1.2, for the preadditive case.
-/

public section

namespace TauCeti

open CategoryTheory

/-- A category is von Neumann regular if every morphism has an inner inverse. -/
@[mk_iff]
class IsVonNeumannRegularCategory (C : Type*) [Category* C] : Prop where
  exists_comp_comp_eq_self ⦃X Y : C⦄ (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f

namespace IsVonNeumannRegularCategory

variable {C : Type*} [Category* C]

/-- Von Neumann regularity is invariant under passing to the opposite category. -/
@[simp]
theorem op_iff : IsVonNeumannRegularCategory Cᵒᵖ ↔ IsVonNeumannRegularCategory C := by
  constructor
  · intro h
    constructor
    intro X Y f
    obtain ⟨g, hg⟩ := h.exists_comp_comp_eq_self f.op
    refine ⟨g.unop, ?_⟩
    simpa only [unop_comp, Quiver.Hom.unop_op, Category.assoc]
      using congrArg Quiver.Hom.unop hg
  · intro h
    constructor
    intro X Y f
    obtain ⟨g, hg⟩ := h.exists_comp_comp_eq_self f.unop
    exact ⟨g.op, Quiver.Hom.unop_inj (by simpa only [unop_comp, Quiver.Hom.unop_op,
      Category.assoc] using hg)⟩

/-- The opposite of a von Neumann regular category is von Neumann regular. -/
instance [IsVonNeumannRegularCategory C] : IsVonNeumannRegularCategory Cᵒᵖ :=
  op_iff.mpr inferInstance

end IsVonNeumannRegularCategory

end TauCeti
