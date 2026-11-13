/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.FactorThru

/-!
# Factorizations through subobjects

This file records elementary forms of the universal property of a subobject. Factoring is
unchanged by precomposition with a split epimorphism (for instance an isomorphism, or one induced
by an equality of objects), it is transported along an isomorphism of ambient objects, and a
factorization through a subobject is unique because its representing arrow is a monomorphism.

## Main declarations

* `CategoryTheory.Subobject.factors_comp_iff_of_isSplitEpi`: precomposition by a split
  epimorphism does not change whether a morphism factors through a subobject.
* `CategoryTheory.Subobject.factors_mapIsoToOrderIso_iff`: factoring through a subobject
  transported along an isomorphism of ambient objects.
* `CategoryTheory.Subobject.factors_iff_existsUnique`: factoring through a subobject is equivalent
  to the existence of a unique lift.
-/

public section

open CategoryTheory

namespace CategoryTheory.Subobject

universe v u

variable {C : Type u} [Category.{v} C] {X Y Z : C}

/-- Factoring through a subobject is unchanged after precomposing with a split epimorphism, such
as an isomorphism or the morphism `eqToHom h` induced by an equality of objects. -/
@[simp]
theorem factors_comp_iff_of_isSplitEpi (P : Subobject Z) (g : X ⟶ Y) [IsSplitEpi g]
    (f : Y ⟶ Z) : P.Factors (g ≫ f) ↔ P.Factors f :=
  ⟨fun h ↦ by simpa using factors_of_factors_right (section_ g) h, factors_of_factors_right g⟩

/-- A morphism factors through the image of a subobject under an isomorphism `e` of ambient
objects exactly when its composite with `e.inv` factors through the original subobject. -/
theorem factors_mapIsoToOrderIso_iff (e : Y ≅ Z)
    (P : Subobject Y) (f : X ⟶ Z) :
    (Subobject.mapIsoToOrderIso e P).Factors f ↔ P.Factors (f ≫ e.inv) := by
  induction P using Subobject.ind with
  | _ g =>
    rw [mapIsoToOrderIso_apply, map_mk]
    simp [MonoOver.Factors, Iso.eq_comp_inv]

/-- A morphism factors through a subobject exactly when it has a unique lift through the
subobject's representing arrow. -/
theorem factors_iff_existsUnique (P : Subobject Y) (f : X ⟶ Y) :
    P.Factors f ↔ ∃! g : X ⟶ (P : C), g ≫ P.arrow = f :=
  ⟨fun hf ↦ ⟨P.factorThru f hf, P.factorThru_arrow f hf, fun g hg ↦
      (cancel_mono P.arrow).mp (by rw [hg, P.factorThru_arrow])⟩,
    fun ⟨g, hg, _⟩ ↦ hg ▸ factors_comp_arrow g⟩

end CategoryTheory.Subobject
