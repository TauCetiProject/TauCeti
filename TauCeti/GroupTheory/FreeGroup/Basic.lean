/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Evaluation of signed words in free groups

A signed word is a list of pairs `(x, b)`, with `true` denoting a generator and `false` its
inverse. This file gives product formulas for evaluating such words under a homomorphism out of a
free group.

## Main results

* `MonoidHom.apply_freeGroup_mk`: a homomorphism evaluates a signed word letter by letter.
* `FreeGroup.lift_inv_mk`: inverting the image of every generator flips every sign in a word.
* `FreeGroup.lift_map`: lifting after mapping the generators is lifting the composite.
* `FreeGroup.lift_sumElim_image_map_inl`: substituting words for the generators of the second
  summand of `α ⊕ β` recovers every set of words in `α`.
-/

public section

namespace MonoidHom

/-- A homomorphism out of a free group into a division monoid evaluates on the word `L` as the
product of the images of its signed letters. For a group target and a homomorphism given as a
lift, this is `FreeGroup.lift_mk`. -/
theorem apply_freeGroup_mk {α M : Type*} [DivisionMonoid M] (F : FreeGroup α →* M)
    (L : List (α × Bool)) :
    F (FreeGroup.mk L) =
      (L.map fun p => cond p.2 (F (FreeGroup.of p.1)) (F (FreeGroup.of p.1))⁻¹).prod := by
  rw [← FreeGroup.lift_of_apply (FreeGroup.mk L), FreeGroup.lift_mk, map_list_prod, List.map_map]
  exact congrArg List.prod <| List.map_congr_left fun ⟨_, b⟩ _ => by cases b <;> simp

end MonoidHom

namespace FreeGroup

/-- Lifting the pointwise inverse of `f` evaluates on the word `L` as lifting `f` evaluates on the
word with every sign flipped. -/
theorem lift_inv_mk {α G : Type*} [Group G] (f : α → G) (L : List (α × Bool)) :
    lift (fun x => (f x)⁻¹) (mk L) = lift f (mk (L.map fun p => (p.1, !p.2))) := by
  rw [lift_mk, lift_mk, List.map_map]
  exact congrArg List.prod <| List.map_congr_left fun ⟨_, b⟩ _ => by cases b <;> simp

attribute [simp] lift_of_eq_id

/-- Lifting `f` after mapping the generators along `g` is lifting `f ∘ g`. -/
@[simp]
theorem lift_comp_map {α β G : Type*} [Group G] (f : β → G) (g : α → β) :
    (lift f).comp (map g) = lift (f ∘ g) := by
  ext
  simp

/-- Lifting `f` after mapping the generators along `g` evaluates as lifting `f ∘ g`. -/
@[simp]
theorem lift_map {α β G : Type*} [Group G] (f : β → G) (g : α → β) (x : FreeGroup α) :
    lift f (map g x) = lift (f ∘ g) x :=
  DFunLike.congr_fun (lift_comp_map f g) x

/-- Substituting a word `w b` in `α` for each generator `b` of the second summand of `α ⊕ β`
is a left inverse of the inclusion of `FreeGroup α`, so it recovers every set of words in `α`. -/
theorem lift_sumElim_image_map_inl {α β : Type*} (w : β → FreeGroup α) (R : Set (FreeGroup α)) :
    lift (Sum.elim of w) '' (map Sum.inl '' R) = R := by
  simp [Set.image_image]

end FreeGroup
