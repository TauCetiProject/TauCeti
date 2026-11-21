/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Lifting properties in Under categories

Given `S : C`, a commutative square in `Under S` admits a lift as soon as its underlying
commutative square in `C` admits a lift: compatibility of the left morphism with the structural map
from `S` forces any lift in `C` to commute with the structural maps. Consequently, a morphism `i`
in `Under S` has the left lifting property with respect to `p` whenever `i.right` has the left
lifting property with respect to `p.right` (`CategoryTheory.HasLiftingProperty.under`).

This is the dual of Joël Riou's `Mathlib.CategoryTheory.LiftingProperties.Over`.
-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

namespace CommSq.HasLift

/-- A commutative square in `Under S` has a lift whenever its underlying square in `C` has a
lift. -/
lemma under {X₁ X₂ X₃ X₄ : Under S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} {sq : CommSq t l r b}
    [CommSq.HasLift (f := t.right) (i := l.right) (p := r.right) (g := b.right)
      (sq.map (Under.forget _))] :
    sq.HasLift := by
  let sq' := sq.map (Under.forget _)
  dsimp at sq'
  exact ⟨⟨{
    l := Under.homMk sq'.lift
      (by rw [← Under.w l, Category.assoc, sq'.fac_left, Under.w t])
  }⟩⟩

end CommSq.HasLift

namespace HasLiftingProperty

/-- Morphisms in `Under S` inherit lifting properties from their underlying morphisms in `C`. -/
lemma under {A B X Y : Under S}
    (i : A ⟶ B) (p : X ⟶ Y) [HasLiftingProperty i.right p.right] :
    HasLiftingProperty i p := ⟨fun _ ↦ .under⟩

end HasLiftingProperty

end CategoryTheory
