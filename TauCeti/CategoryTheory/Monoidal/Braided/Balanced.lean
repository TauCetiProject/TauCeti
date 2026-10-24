/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Balanced categories

A *balanced category* is a braided monoidal category equipped with a *twist*: a natural
automorphism `θ` of the identity functor whose component at a tensor product is the tensor
product of the components followed by the double braiding,
`θ_{X ⊗ Y} = (θ_X ⊗ θ_Y) ≫ β_{X,Y} ≫ β_{Y,X}`.

Balanced categories sit between braided categories and ribbon categories. A braided rigid
category with a pivotal structure is balanced, and a ribbon category is a balanced rigid
category whose twist is compatible with duals.

## Main declarations

* `TauCeti.BalancedCategory`: a twist on a braided monoidal category;
* `TauCeti.BalancedCategory.twist_hom_app_unit`, `TauCeti.BalancedCategory.twist_inv_app_unit`:
  the twist and its inverse are trivial on the unit object;
* `TauCeti.BalancedCategory.twist_inv_tensor`: the balancing axiom for the inverse twist.

The class is named `BalancedCategory` rather than `Balanced` because Mathlib's
`CategoryTheory.Balanced` is the unrelated notion of a category in which every morphism that is
both a monomorphism and an epimorphism is an isomorphism.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

/-- A *balanced* structure on a braided monoidal category: a twist `θ : 𝟭 C ≅ 𝟭 C`, a natural
automorphism of the identity functor, satisfying the balancing axiom
`θ_{X ⊗ Y} = (θ_X ⊗ θ_Y) ≫ β_{X,Y} ≫ β_{Y,X}`. -/
@[ext]
class BalancedCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] where
  /-- The twist, with components `θ_X : X ≅ X`. -/
  twist : 𝟭 C ≅ 𝟭 C
  /-- The balancing axiom: the twist of a tensor product is the tensor product of the twists,
  followed by the double braiding. -/
  twist_tensor (X Y : C) : twist.hom.app (X ⊗ Y) =
    (twist.hom.app X ⊗ₘ twist.hom.app Y) ≫ (β_ X Y).hom ≫ (β_ Y X).hom

namespace BalancedCategory

attribute [reassoc] twist_tensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [BalancedCategory C]

/-- The twist of the unit object is the identity. -/
@[simp]
theorem twist_hom_app_unit : (twist (C := C)).hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  -- Naturality at the left unitor of `𝟙_ C ⊗ 𝟙_ C`, together with the balancing axiom, shows
  -- that the twist of the unit is idempotent.
  rw [← cancel_epi ((twist (C := C)).hom.app (𝟙_ C))]
  simpa [twist_tensor, tensorHom_def, ← unitors_equal, ← unitors_inv_equal] using
    ((twist (C := C)).hom.naturality (λ_ (𝟙_ C)).hom).symm

/-- The inverse twist of the unit object is the identity. -/
@[simp]
theorem twist_inv_app_unit : (twist (C := C)).inv.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  rw [← cancel_epi ((twist (C := C)).hom.app (𝟙_ C)), Iso.hom_inv_id_app, twist_hom_app_unit]
  simp

/-- The balancing axiom for the inverse twist: the inverse twist of a tensor product is the
inverse double braiding followed by the tensor product of the inverse twists. -/
@[reassoc]
theorem twist_inv_tensor (X Y : C) : (twist (C := C)).inv.app (X ⊗ Y) =
    (β_ Y X).inv ≫ (β_ X Y).inv ≫ (twist.inv.app X ⊗ₘ twist.inv.app Y) := by
  rw [← cancel_epi ((twist (C := C)).hom.app (X ⊗ Y)), Iso.hom_inv_id_app, twist_tensor]
  simp

end BalancedCategory

end TauCeti
