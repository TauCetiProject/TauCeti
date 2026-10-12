/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup

/-!
# Evaluation of signed words in free and presented groups

A signed word is a list of pairs `(x, b)`, with `true` denoting a generator and `false` its
inverse. This file gives product formulas for evaluating such words under a homomorphism from a
free group and under the quotient map to a presented group.

## Main results

* `MonoidHom.apply_freeGroup_mk`: a homomorphism evaluates a signed word letter by letter.
* `PresentedGroup.mk_mk`: the class of a word is the product of its signed generators.
* `PresentedGroup.lift_inv_of_mk`: inverting every generator flips every sign in a word.
-/

public section

namespace MonoidHom

/-- A homomorphism out of a free group evaluates on the word `L` as the product of the images of
its signed letters. This is `FreeGroup.lift_mk` for a homomorphism not presented as a lift. -/
theorem apply_freeGroup_mk {α G : Type*} [Group G] (F : FreeGroup α →* G)
    (L : List (α × Bool)) :
    F (FreeGroup.mk L) =
      (L.map fun p => cond p.2 (F (FreeGroup.of p.1)) (F (FreeGroup.of p.1))⁻¹).prod := by
  rw [FreeGroup.lift_unique F (f := fun x => F (FreeGroup.of x)) fun _ => rfl, FreeGroup.lift_mk]

end MonoidHom

namespace PresentedGroup

/-- The image of a word in a presented group is the product of the images of its signed
letters. -/
theorem mk_mk {α : Type*} (S : Set (FreeGroup α)) (L : List (α × Bool)) :
    mk S (FreeGroup.mk L) =
      (L.map fun p => cond p.2 (of p.1) (of p.1)⁻¹).prod :=
  (mk S).apply_freeGroup_mk L

/-- Inverting every generator of a presented group sends the class of a word to the class of the
word with every sign flipped. -/
theorem lift_inv_of_mk {α : Type*} (S : Set (FreeGroup α)) (L : List (α × Bool)) :
    FreeGroup.lift (fun x => (of x : PresentedGroup S)⁻¹) (FreeGroup.mk L) =
      mk S (FreeGroup.mk (L.map fun p => (p.1, !p.2))) := by
  rw [FreeGroup.lift_mk, mk_mk, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨x, b⟩ := p
  cases b <;> simp

end PresentedGroup
