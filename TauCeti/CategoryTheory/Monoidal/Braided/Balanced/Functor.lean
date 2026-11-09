/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Balanced.Basic

/-!
# Balanced functors

A balanced functor is a strong braided monoidal functor preserving the chosen twists.
Preservation is stable under identity, composition, and natural isomorphism. In particular,
no additional equation on a monoidal natural isomorphism is needed to compare balanced
functors: ordinary naturality already intertwines the twists.

The convention for twists is that of `TauCeti.BalancedCategory`. These functors allow the
correspondence between pivotal and balanced structures to be used on morphisms as well.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory TauCeti

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [BalancedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [BalancedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  [BalancedCategory E]

/-- A strong braided monoidal functor is balanced when it preserves the chosen twists. -/
class IsBalanced (F : C ⥤ D) [F.Braided] : Prop where
  /-- The image of the source twist is the target twist. -/
  map_twist_hom_app (X : C) :
    F.map (BalancedCategory.twist.hom.app X) = BalancedCategory.twist.hom.app (F.obj X)

attribute [simp] IsBalanced.map_twist_hom_app

variable (F : C ⥤ D) [F.Braided]

/-- A balanced functor also preserves inverse twists. -/
@[simp]
theorem map_twist_inv_app [F.IsBalanced] (X : C) :
    F.map (BalancedCategory.twist.inv.app X) = BalancedCategory.twist.inv.app (F.obj X) := by
  apply (cancel_mono (BalancedCategory.twist.hom.app (F.obj X))).mp
  rw [← IsBalanced.map_twist_hom_app (F := F), ← F.map_comp]
  simp

/-- The identity braided functor preserves the twist. -/
instance isBalanced_id : (𝟭 C).IsBalanced where
  map_twist_hom_app _ := rfl

/-- A composite of balanced functors is balanced. -/
instance isBalanced_comp (G : D ⥤ E) [G.Braided] [F.IsBalanced] [G.IsBalanced] :
    (F ⋙ G).IsBalanced where
  map_twist_hom_app X := by simp

variable {F} {G : C ⥤ D} [G.Braided]

/-- Twist preservation transports along any natural isomorphism of braided functors.
The isomorphism need not itself be monoidal for this assertion. -/
theorem IsBalanced.of_iso (e : F ≅ G) [F.IsBalanced] : G.IsBalanced where
  map_twist_hom_app X := by
    apply (cancel_epi (e.hom.app X)).mp
    rw [← e.hom.naturality, IsBalanced.map_twist_hom_app]
    exact (BalancedCategory.twist.hom.naturality (e.hom.app X)).symm

/-- Naturally isomorphic braided functors preserve twists simultaneously. -/
theorem isBalanced_iff_of_iso (e : F ≅ G) : F.IsBalanced ↔ G.IsBalanced :=
  ⟨fun _ => IsBalanced.of_iso e, fun _ => IsBalanced.of_iso e.symm⟩

end CategoryTheory.Functor
