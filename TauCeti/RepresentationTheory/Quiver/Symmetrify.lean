/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Fintype.Sum
public import TauCeti.Combinatorics.Quiver.PathWeight

/-!
# Symmetrified quivers

Mathlib's `Quiver.Symmetrify` doubles a quiver by adjoining a formal reverse to every arrow,
with the same vertices as the original quiver. This file transfers finiteness and decidable
equality to the doubled vertex type, supplies finite arrow types from those of the original
quiver, counts them, and records that the inclusion is bijective on vertices. These facts let
path-algebra constructions on the doubled quiver reuse the original finite vertex and arrow data.

The reverse-arrow weight counts formal reverse arrows in paths, without finiteness assumptions.
Its weight-zero paths are exactly the images of paths in the original quiver, and any intermediate
weight is attained by a prefix.

## Main results

* `TauCeti.card_symmetrify_hom`: the doubled quiver has as many arrows from `i` to `j` as `Q`
  has from `i` to `j` and from `j` to `i` together.
* `TauCeti.symmetrify_of_obj`: the doubling inclusion is the identity on vertices.
* `TauCeti.symmetrify_of_obj_bijective`: the doubling inclusion is bijective on vertices.
* `TauCeti.reverseArrowWeight`: original arrows have weight zero, formal reverses one.
* `Quiver.Path.addWeight_reverseArrowWeight_eq_zero_iff`: weight zero characterizes original paths.
* `Quiver.Path.exists_eq_comp_of_le_reverseArrowWeight`: split a path at any reverse-arrow count.
-/

public section

universe u v

namespace TauCeti

open _root_.Quiver

section ReverseArrowWeight

variable {Q : Type u} [Quiver.{v} Q]

/-- Give original arrows weight zero and formal reverse arrows weight one. -/
def reverseArrowWeight {i j : Symmetrify Q} (a : i ⟶ j) : ℕ :=
  Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) a

/-- The first summand of the doubled arrow type consists of weight-zero arrows. -/
@[simp]
theorem reverseArrowWeight_inl {i j : Symmetrify Q} (a : @Quiver.Hom Q _ i j) :
    reverseArrowWeight (i := i) (j := j) (Sum.inl a) = 0 :=
  (rfl)

/-- The second summand of the doubled arrow type consists of weight-one arrows. -/
@[simp]
theorem reverseArrowWeight_inr {i j : Symmetrify Q} (a : @Quiver.Hom Q _ j i) :
    reverseArrowWeight (i := i) (j := j) (Sum.inr a) = 1 :=
  (rfl)

/-- An arrow included from the original quiver has weight zero. -/
@[simp↓]
theorem reverseArrowWeight_of_map {i j : Q} (a : i ⟶ j) :
    reverseArrowWeight (Symmetrify.of.map a) = 0 :=
  (rfl)

/-- The formal reverse of an included arrow has weight one. -/
@[simp↓]
theorem reverseArrowWeight_reverse_of_map {i j : Q} (a : i ⟶ j) :
    reverseArrowWeight (Quiver.reverse (Symmetrify.of.map a)) = 1 :=
  (rfl)

/-- Every arrow of the doubled quiver has reverse-arrow weight at most one. -/
theorem reverseArrowWeight_le_one {i j : Symmetrify Q} (a : i ⟶ j) :
    reverseArrowWeight a ≤ 1 := by
  cases a <;> simp

end ReverseArrowWeight

end TauCeti

namespace Quiver.Path

open Symmetrify TauCeti

variable {Q : Type u} [Quiver.{v} Q]

/-- A path in the double has weight zero exactly when it is the image of an original path. -/
theorem addWeight_reverseArrowWeight_eq_zero_iff {i j : Symmetrify Q} (p : Path i j) :
    p.addWeight reverseArrowWeight = 0 ↔
      ∃ q : @Path Q ‹Quiver Q› i j, (@of Q _).mapPath q = p := by
  constructor
  · induction p with
    | nil => exact fun _ ↦ ⟨Path.nil, rfl⟩
    | cons p a ih =>
      rcases a with a | a
      · intro hp
        have hw : p.addWeight reverseArrowWeight = 0 := by
          simpa only [Path.addWeight_cons, reverseArrowWeight_inl, add_zero] using hp
        obtain ⟨q, rfl⟩ := ih hw
        exact ⟨q.cons a, rfl⟩
      · simp
  · rintro ⟨q, rfl⟩
    refine ((@of Q _).addWeight_mapPath (@reverseArrowWeight Q _) q).trans ?_
    exact (Path.addWeight_const (0 : ℕ) q).trans (nsmul_zero _)

/-- A path with at least `n` formal reverse arrows has a prefix with exactly `n` of them. -/
theorem exists_eq_comp_of_le_reverseArrowWeight {i j : Symmetrify Q} (p : Path i j) {n : ℕ}
    (hn : n ≤ p.addWeight reverseArrowWeight) :
    ∃ (l : Symmetrify Q) (p₁ : Path i l) (p₂ : Path l j),
      p = p₁.comp p₂ ∧ p₁.addWeight reverseArrowWeight = n :=
  p.exists_eq_comp_of_le_addWeight reverseArrowWeight reverseArrowWeight_le_one hn

end Quiver.Path

namespace TauCeti

open _root_.Quiver

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
  -- `show Q from _` retypes the vertices as vertices of `Q`, so that the instance search finds
  -- the hom-set instances of `Q`.
  inferInstanceAs (Fintype (((show Q from x) ⟶ (show Q from y)) ⊕
    ((show Q from y) ⟶ (show Q from x))))

/-- The arrows of the doubled quiver from `i` to `j` are the arrows of `Q` from `i` to `j` together
with the formal reverses of the arrows of `Q` from `j` to `i`. -/
theorem card_symmetrify_hom (Q : Type u) [Quiver.{v} Q] [∀ i j : Q, Fintype (i ⟶ j)] (i j : Q) :
    Fintype.card (Symmetrify.of.obj i ⟶ Symmetrify.of.obj j) =
      Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) :=
  -- Mathlib defines the arrows of `Symmetrify Q` as this sum, and `instFintypeSymmetrifyHom`
  -- is the sum instance.
  Fintype.card_sum (α := i ⟶ j) (β := j ⟶ i)

/-- The inclusion `Quiver.Symmetrify.of` of a quiver in its doubled quiver is the identity on
vertices. Mathlib's simp lemma `Quiver.Symmetrify.of_obj` states this with right-hand side `id x`;
this `id`-free form rewrites a vertex of the doubled quiver directly to the underlying vertex of `Q`
in `rw` and `simp only`. -/
theorem symmetrify_of_obj {Q : Type u} [Quiver.{v} Q] (x : Q) :
    (Symmetrify.of (V := Q)).obj x = x := rfl

/-- The inclusion `Quiver.Symmetrify.of` of a quiver in its doubled quiver is the identity on
vertices, hence bijective on them. -/
theorem symmetrify_of_obj_bijective {Q : Type u} [Quiver.{v} Q] :
    Function.Bijective (Symmetrify.of (V := Q)).obj :=
  Function.bijective_id

end TauCeti
