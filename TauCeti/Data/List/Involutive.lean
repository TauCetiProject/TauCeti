/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lists of involutions

This file provides an elementary invariance result for predicates transported along lists of
involutions.

## Main results

* `TauCeti.predicate_foldl_iff_of_involutive`: a predicate preserved by involutive steps is
  invariant along a list of steps.
* `TauCeti.foldl_reverse_foldl_of_involutive`: reverse a word of involutions to undo its action.
-/

public section

namespace TauCeti

/-- Applying a list of involutions in reverse order undoes its left-fold action. No relations
between distinct directions, decidable equality, or finiteness of the index type are needed. -/
theorem foldl_reverse_foldl_of_involutive {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) (a : I) :
    l.reverse.foldl f (l.foldl f a) = a := by
  induction l generalizing a with
  | nil => rfl
  | cons j l ih =>
    simpa only [List.foldl_cons, List.reverse_cons, List.foldl_append, List.foldl_nil,
      ih] using hf j a

/-- A predicate preserved by a family of involutions is invariant under every list of those
involutions. -/
theorem predicate_foldl_iff_of_involutive {I J : Type*} (p : I → Prop)
    (reflect : J → I → I) (hinvolutive : ∀ j, Function.Involutive (reflect j))
    (hreflect : ∀ a j, p a → p (reflect j a)) (l : List J) (a : I) :
    p (l.foldl (fun b j ↦ reflect j b) a) ↔ p a := by
  induction l generalizing a with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    exact ⟨fun h ↦ hinvolutive j a ▸ hreflect _ j h, hreflect a j⟩

end TauCeti
