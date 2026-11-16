/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# The degree of a formal sum

The degree (or augmentation) of a formal sum `∑ nᵢ [xᵢ]` in the free abelian group on a type `X`
is the integer `∑ nᵢ`. It is the morphism `FreeAbelianGroup X →+ ℤ` sending every generator to
`1`, and it is invariant under relabelling the generators by `FreeAbelianGroup.map`.

## Main declarations

* `FreeAbelianGroup.degree X`: the degree morphism `FreeAbelianGroup X →+ ℤ`.
* `FreeAbelianGroup.degree_map`: relabelling generators preserves the degree.
* `FreeAbelianGroup.lift_const_apply`: lifting a constant function `fun _ ↦ a` sends a formal sum
  to its degree times `a`.
-/

public section

namespace FreeAbelianGroup

variable {X Y A : Type*} [AddCommGroup A]

variable (X) in
/-- The degree of a formal sum: the morphism `FreeAbelianGroup X →+ ℤ` sending `∑ nᵢ [xᵢ]` to
`∑ nᵢ`. -/
def degree : FreeAbelianGroup X →+ ℤ :=
  lift fun _ ↦ 1

@[simp]
lemma degree_of (x : X) : degree X (of x) = 1 :=
  lift_apply_of _ _

/-- Relabelling the generators of a formal sum does not change its degree. -/
lemma degree_comp_map (f : X → Y) : (degree Y).comp (map f) = degree X :=
  lift_ext _ _ fun x ↦ by simp

/-- Relabelling the generators of a formal sum does not change its degree. -/
@[simp]
lemma degree_map (f : X → Y) (x : FreeAbelianGroup X) : degree Y (map f x) = degree X x :=
  DFunLike.congr_fun (degree_comp_map f) x

/-- Lifting a constant function `fun _ ↦ a` multiplies the degree by `a`. -/
lemma lift_const (a : A) : lift (fun _ : X ↦ a) = (zmultiplesHom A a).comp (degree X) :=
  lift_ext _ _ fun x ↦ by simp

/-- Lifting a constant function `fun _ ↦ a` sends a formal sum to its degree times `a`. -/
lemma lift_const_apply (a : A) (x : FreeAbelianGroup X) :
    lift (fun _ : X ↦ a) x = degree X x • a :=
  DFunLike.congr_fun (lift_const a) x

end FreeAbelianGroup
