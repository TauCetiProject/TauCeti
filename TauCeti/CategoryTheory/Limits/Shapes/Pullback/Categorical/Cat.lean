/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Categorical pullbacks as objects of `Cat`

For functors `P : A ⥤ B` and `Q : C ⥤ B`, a `2`-morphism of `Cat` between two functors with
values in the categorical pullback `P ⊡ Q` is determined by its components in the two factors
`A` and `C`. Mathlib's `CategoricalPullback.natTrans_ext` states this after whiskering with the
two projections; the extensionality lemma here is stated componentwise, so that `ext` reduces
such a `2`-morphism directly to the `fst` and `snd` components of its values.

## Main declarations

* `CategoryTheory.Limits.CategoricalPullback.cat_hom₂_ext`: extensionality for `2`-morphisms of
  `Cat` with values in `P ⊡ Q`.
-/

public section

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] {P : A ⥤ B} {Q : C ⥤ B}

/-- Extensionality for `2`-morphisms of `Cat` with values in the categorical pullback `P ⊡ Q`:
they are determined by their components in the two factors. -/
@[ext]
lemma cat_hom₂_ext {X : Cat.{max v₁ v₃, max u₁ u₃ v₂}} {T U : X ⟶ ⟨P ⊡ Q, inferInstance⟩}
    {α β : T ⟶ U}
    (h₁ : ∀ x, (α.toNatTrans.app x).fst = (β.toNatTrans.app x).fst)
    (h₂ : ∀ x, (α.toNatTrans.app x).snd = (β.toNatTrans.app x).snd) : α = β :=
  Cat.Hom₂.ext (NatTrans.ext (funext fun x ↦ hom_ext (h₁ x) (h₂ x)))

end CategoryTheory.Limits.CategoricalPullback
