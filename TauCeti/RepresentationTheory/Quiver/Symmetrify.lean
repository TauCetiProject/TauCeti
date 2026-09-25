/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Fintype.Sum

/-!
# Symmetrified quivers

This file supplies general infrastructure for Mathlib's `Quiver.Symmetrify` construction.

## Main results

* `TauCeti.symmetrify_of_obj`: the doubling inclusion is the identity on vertices.
* `TauCeti.card_symmetrify_hom`: hence their number is `#(a ⟶ b) + #(b ⟶ a)`.

## References

This file supplies a prerequisite for Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

/-- Typeclass search does not unfold the `Symmetrify` type synonym to reuse `Finite Q`. -/
instance instFiniteSymmetrify (Q : Type u) [Finite Q] : Finite (Symmetrify Q) :=
  inferInstanceAs (Finite Q)

/-- Typeclass search does not unfold the `Symmetrify` type synonym to reuse `DecidableEq Q`. -/
instance instDecidableEqSymmetrify (Q : Type u) [DecidableEq Q] : DecidableEq (Symmetrify Q) :=
  inferInstanceAs (DecidableEq Q)

/-- Typeclass search does not unfold the `Symmetrify` type synonym to reuse `Fintype Q`. -/
instance instFintypeSymmetrify (Q : Type u) [Fintype Q] : Fintype (Symmetrify Q) :=
  inferInstanceAs (Fintype Q)

/-- The arrows of the doubled quiver between two vertices are the arrows of `Q` in either
direction, so there are finitely many whenever `Q` has finitely many between each pair. -/
instance instFintypeSymmetrifyHom (Q : Type u) [Quiver.{v} Q] [∀ i j : Q, Fintype (i ⟶ j)]
    (x y : Symmetrify Q) : Fintype (x ⟶ y) :=
  inferInstanceAs (Fintype (((show Q from x) ⟶ (show Q from y)) ⊕
    ((show Q from y) ⟶ (show Q from x))))

/-- The inclusion `Quiver.Symmetrify.of` of a quiver in its doubled quiver is the identity on
vertices.  Deliberately not a `simp` lemma: the two vertex types are definitionally equal, so
rewriting `Quiver.Symmetrify.of` away erases the only record of which of the two quiver structures
a vertex was meant to carry. -/
theorem symmetrify_of_obj {Q : Type u} [Quiver.{v} Q] (x : Q) :
    (Symmetrify.of (V := Q)).obj x = x := rfl

/-- The inclusion `Quiver.Symmetrify.of` of a quiver in its doubled quiver is the identity on
vertices, hence bijective on them. -/
theorem symmetrify_of_obj_bijective {Q : Type u} [Quiver.{v} Q] :
    Function.Bijective (Symmetrify.of (V := Q)).obj :=
  Function.bijective_id

/-- The doubled quiver has `#(a ⟶ b) + #(b ⟶ a)` arrows from `a` to `b`. -/
theorem card_symmetrify_hom {Q : Type u} [Quiver.{v} Q] [∀ i j : Q, Fintype (i ⟶ j)] (a b : Q) :
    Fintype.card (Symmetrify.of.obj a ⟶ Symmetrify.of.obj b) =
      Fintype.card (a ⟶ b) + Fintype.card (b ⟶ a) := by
  change Fintype.card ((a ⟶ b) ⊕ (b ⟶ a)) = _
  exact Fintype.card_sum

end TauCeti
