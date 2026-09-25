/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
-- Non-public: the component equations for the unitors and associators of functors are used only
-- to simplify the mate computation of the declaration below.
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Mating a two-square through the identity functors

The unit and the counit of an identity adjunction are the identity maps, so mating a
two-square whose vertical functors are the identity functors reproduces that two-square: the
mate is computed on the source objects by left whiskering with the unit of one adjunction and
right whiskering with the counit of the other, and both are identities.

Recording this once keeps mate computations that route a square through the identity functors
free of the underlying unit, counit, and whisker calculations. It is the two-square
counterpart of Mathlib's `CategoryTheory.conjugateEquiv_id`. The internal-Hom comparison of a
lax monoidal functor is one such computation: at the tensor unit the left unitor identifies the
unit with left tensoring by the unit, and the remaining mate is taken between the two
tensor--Hom adjunctions.

## Main declaration

* `CategoryTheory.mateEquiv_adjunction_id`.
-/

public section

namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The mate of a two-square between the identity functors of the source and target category is
the two-square itself. -/
theorem mateEquiv_adjunction_id {G H : C ⥤ D} (α : TwoSquare G (𝟭 C) (𝟭 D) H) :
    mateEquiv (Adjunction.id : (𝟭 C) ⊣ (𝟭 C))
      (Adjunction.id : (𝟭 D) ⊣ (𝟭 D)) α = α := by
  ext X
  rw [mateEquiv_apply]
  simp only [comp_obj, id_obj, NatTrans.comp_app,
    Functor.id_obj, Functor.id_map, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    rightUnitor_inv_app, associator_hom_app, associator_inv_app, leftUnitor_hom_app,
    Adjunction.id_unit, Adjunction.id_counit, Category.comp_id, Category.id_comp,
    Functor.comp_map, Functor.map_id, NatTrans.id_app]

end CategoryTheory
