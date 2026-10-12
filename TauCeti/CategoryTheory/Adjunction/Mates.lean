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
# Mates and conjugates

`CategoryTheory.mateEquiv_adjunction_id` is the case of the mate bijection
`CategoryTheory.mateEquiv` in which both adjunctions are identity adjunctions: a two-square
between the identity functors of the source and target category is its own mate.  Use it to
normalize a mate that has been routed through the identity functors, so a computation about
such a square can be read back on the square itself.  It is the two-square counterpart of
Mathlib's `CategoryTheory.conjugateEquiv_id`.

The internal-Hom comparison of a monoidal functor is one such computation: at the tensor unit
the left unitor identifies the unit with left tensoring by the unit, and the mate that remains
is taken between the two tensor--Hom adjunctions.

`CategoryTheory.Adjunction.homEquiv_conjugateEquiv` transposes a morphism across two adjunctions
whose left adjoints are compared by a natural transformation `α`: transposing along the first
adjunction and then applying the conjugate of `α` is transposing `α` followed by the morphism along
the second.
It computes transposes along an adjunction whose left adjoint is only known up to a comparison
with another left adjoint, such as a composite of pullback functors.

## Main declarations

* `CategoryTheory.mateEquiv_adjunction_id`;
* `CategoryTheory.Adjunction.homEquiv_conjugateEquiv`.
-/

public section

namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The mate of a two-square between the identity functors of the source and target category is
the two-square itself. -/
-- `high` priority: Mathlib's generated equational lemma `mateEquiv_apply` is itself a simp lemma
-- that unfolds the mate, so at the default priority this rule would never fire, and `simpNF`
-- rejects a simp lemma whose left-hand side another simp lemma already simplifies.
@[simp high]
theorem mateEquiv_adjunction_id {G H : C ⥤ D} (α : TwoSquare G (𝟭 C) (𝟭 D) H) :
    mateEquiv (Adjunction.id : (𝟭 C) ⊣ (𝟭 C))
      (Adjunction.id : (𝟭 D) ⊣ (𝟭 D)) α = α := by
  -- The mate is a whiskered composite of the units and counits of the two adjunctions with the
  -- component of the square; the unit and the counit of an identity adjunction are the identity
  -- maps, so every whiskered unit and counit is the identity and only the square survives.
  ext X
  rw [mateEquiv_apply]
  simp only [comp_obj, id_obj, NatTrans.comp_app,
    Functor.id_obj, Functor.id_map, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    rightUnitor_inv_app, associator_hom_app, associator_inv_app, leftUnitor_hom_app,
    Adjunction.id_unit, Adjunction.id_counit, Category.comp_id, Category.id_comp,
    Functor.comp_map, Functor.map_id, NatTrans.id_app]

section Conjugate

namespace Adjunction

variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Transposing `a : L₁ c ⟶ d` along `adj₁` and then applying the conjugate of `α : L₂ ⟶ L₁` is
the transpose of `α.app c ≫ a` along `adj₂`. -/
theorem homEquiv_conjugateEquiv (α : L₂ ⟶ L₁) {c : C} {d : D} (a : L₁.obj c ⟶ d) :
    adj₁.homEquiv c d a ≫ (conjugateEquiv adj₁ adj₂ α).app d =
      adj₂.homEquiv c d (α.app c ≫ a) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv, Category.assoc, Category.assoc, NatTrans.naturality]

end Adjunction

end Conjugate

end CategoryTheory
