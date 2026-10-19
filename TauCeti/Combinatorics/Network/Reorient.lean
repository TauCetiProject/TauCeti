/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Order.Interval.Set.Defs
public import TauCeti.Combinatorics.Network.Excess
public import TauCeti.Combinatorics.Quiver.Reorient

/-!
# Reorienting directed networks

A Boolean label on the arrows of an explicit arrow family selects arrows to reverse. This file
exposes `TauCeti.Reorient` through the explicit-family interface used by directed networks and
transports assignments and finite bounds across the reorientation. Values on reversed arrows are
negated, so an interval `[l(e), u(e)]` becomes `[-u(e), -l(e)]`.

The transport preserves feasibility and vertex excess. In particular, reversing a loop changes
its value's sign but still contributes zero excess, while parallel and antiparallel arrows remain
distinguished by their identities.

## Main definitions

* `TauCeti.ReorientHom Q σ`: the explicit arrow family obtained by reversing the arrows selected
  by `σ`.
* `TauCeti.reorientAssignment σ`: assignment transport, negating values on reversed arrows.
* `TauCeti.reorientLower σ` and `TauCeti.reorientUpper σ`: transported finite bounds.
* `TauCeti.Network.reorient`: the corresponding reorientation of a bounded network.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-- The explicit arrow family obtained by reversing precisely the arrows selected by `σ`.

This is the arrow family of the existing quiver reorientation `TauCeti.Reorient`, exposed without
installing a global `Quiver` instance on the vertex type. -/
abbrev ReorientHom (Q : V → V → Type v) (σ : Assignment Q Bool) (x y : V) : Type v :=
  @Quiver.Hom (@Reorient V ⟨Q⟩ σ) (@reorientQuiver V ⟨Q⟩ σ) x y

namespace ReorientHom

/-- An unselected arrow retains its direction in the reoriented family. -/
def keep (σ : Assignment Q Bool) {x y : V} (e : Q x y) (h : ¬ σ e) :
    ReorientHom Q σ x y :=
  Sum.inl ⟨e, h⟩

/-- A selected arrow appears with reversed direction in the reoriented family. -/
def flip (σ : Assignment Q Bool) {x y : V} (e : Q y x) (h : σ e) :
    ReorientHom Q σ x y :=
  Sum.inr ⟨e, h⟩

/-- Eliminate an arrow of an explicitly reoriented family by considering whether it was retained
or reversed. -/
@[elab_as_elim]
theorem inductionOn (σ : Assignment Q Bool) {x y : V} {motive : ReorientHom Q σ x y → Prop}
    (e : ReorientHom Q σ x y)
    (keep : ∀ (a : Q x y) (h : ¬ σ a), motive (keep σ a h))
    (flip : ∀ (a : Q y x) (h : σ a), motive (flip σ a h)) : motive e := by
  obtain ⟨a, ha⟩ | ⟨a, ha⟩ := e
  exacts [keep a ha, flip a ha]

end ReorientHom

/-- Reorientation preserves finiteness of every explicit arrow type. -/
instance instFintypeNetworkReorientHom (σ : Assignment Q Bool) [∀ x y, Fintype (Q x y)]
    (x y : V) : Fintype (ReorientHom Q σ x y) :=
  inferInstanceAs (Fintype ({e : Q x y // ¬ σ e} ⊕ {e : Q y x // σ e}))

section AddCommGroup

variable [AddCommGroup K]

/-- Transport an assignment across a reorientation, retaining values on unselected arrows and
negating values on selected, reversed arrows. -/
def reorientAssignment (σ : Assignment Q Bool) (f : Assignment Q K) :
    Assignment (ReorientHom Q σ) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ f e.1) (fun e ↦ -f e.1) e

@[simp]
theorem reorientAssignment_keep (σ : Assignment Q Bool) (f : Assignment Q K) {x y : V}
    (e : Q x y) (h : ¬ σ e) :
    reorientAssignment σ f (ReorientHom.keep σ e h) = f e :=
  (rfl)

@[simp]
theorem reorientAssignment_flip (σ : Assignment Q Bool) (f : Assignment Q K) {x y : V}
    (e : Q y x) (h : σ e) :
    reorientAssignment σ f (ReorientHom.flip σ e h) = -f e :=
  (rfl)

/-- Recover an assignment on the original arrow family from one on a reorientation. Values on
reversed arrows are negated again. -/
def unreorientAssignment (σ : Assignment Q Bool) (g : Assignment (ReorientHom Q σ) K) :
    Assignment Q K :=
  fun _ _ e ↦ if h : σ e then -g (ReorientHom.flip σ e h)
    else g (ReorientHom.keep σ e h)

@[simp]
theorem unreorientAssignment_apply_of_pos (σ : Assignment Q Bool)
    (g : Assignment (ReorientHom Q σ) K) {x y : V} (e : Q x y) (h : σ e) :
    unreorientAssignment σ g e = -g (ReorientHom.flip σ e h) := by
  simp [unreorientAssignment, h]

@[simp]
theorem unreorientAssignment_apply_of_neg (σ : Assignment Q Bool)
    (g : Assignment (ReorientHom Q σ) K) {x y : V} (e : Q x y) (h : ¬ σ e) :
    unreorientAssignment σ g e = g (ReorientHom.keep σ e h) := by
  simp [unreorientAssignment, h]

@[simp]
theorem unreorientAssignment_reorientAssignment (σ : Assignment Q Bool) (f : Assignment Q K) :
    unreorientAssignment σ (reorientAssignment σ f) = f := by
  funext x y e
  by_cases h : σ e <;> simp [unreorientAssignment, h]

@[simp]
theorem reorientAssignment_unreorientAssignment (σ : Assignment Q Bool)
    (g : Assignment (ReorientHom Q σ) K) :
    reorientAssignment σ (unreorientAssignment σ g) = g := by
  funext x y e
  induction e using ReorientHom.inductionOn σ with
  | keep e h => simp [unreorientAssignment, h]
  | flip e h => simp [unreorientAssignment, h]

/-- Reorientation gives an additive equivalence of the two assignment groups. -/
def reorientAssignmentEquiv (σ : Assignment Q Bool) :
    Assignment Q K ≃+ Assignment (ReorientHom Q σ) K where
  toFun := reorientAssignment σ
  invFun := unreorientAssignment σ
  left_inv := unreorientAssignment_reorientAssignment σ
  right_inv := reorientAssignment_unreorientAssignment σ
  map_add' f g := by
    funext x y e
    induction e using ReorientHom.inductionOn σ <;> simp [add_comm]

@[simp]
theorem reorientAssignmentEquiv_apply (σ : Assignment Q Bool) (f : Assignment Q K) :
    reorientAssignmentEquiv σ f = reorientAssignment σ f :=
  (rfl)

@[simp]
theorem reorientAssignmentEquiv_symm_apply (σ : Assignment Q Bool)
    (g : Assignment (ReorientHom Q σ) K) :
    (reorientAssignmentEquiv σ).symm g = unreorientAssignment σ g :=
  (rfl)

section Excess

variable [∀ x y, Fintype (Q x y)]

/-- The sum of a transported assignment over a reoriented hom set is the retained-arrow sum
minus the reversed-arrow sum. -/
theorem sum_reorientAssignment (σ : Assignment Q Bool) (f : Assignment Q K) (x y : V) :
    (∑ e : ReorientHom Q σ x y, reorientAssignment σ f e) =
      (∑ e : {e : Q x y // ¬ σ e}, f e.1) - ∑ e : {e : Q y x // σ e}, f e.1 := by
  -- Big-operator rewriting does not unfold the locally installed quiver instance, so expose the
  -- sum-of-subtypes representation supplied definitionally by `TauCeti.Reorient`.
  change (∑ e : ({e : Q x y // ¬ σ e} ⊕ {e : Q y x // σ e}),
    Sum.elim (fun e ↦ f e.1) (fun e ↦ -f e.1) e) = _
  simp [Fintype.sum_sum_type, sub_eq_add_neg]

variable [Fintype V]

/-- Reorienting arrows and negating their values preserves excess at every vertex. -/
@[simp]
theorem excessAt_reorientAssignment (σ : Assignment Q Bool) (f : Assignment Q K) (x : V) :
    excessAt (reorientAssignment σ f) x = excessAt f x := by
  have hsplit (a b : V) :
      (∑ e : {e : Q a b // ¬ σ e}, f e.1) + (∑ e : {e : Q a b // σ e}, f e.1) =
        ∑ e : Q a b, f e := by
    rw [add_comm]
    exact Fintype.sum_subtype_add_sum_subtype (fun e : Q a b ↦ σ e) (fun e ↦ f e)
  have hin :
      (∑ w, ∑ e : {e : Q w x // ¬ σ e}, f e.1) +
          (∑ w, ∑ e : {e : Q w x // σ e}, f e.1) = ∑ w, ∑ e : Q w x, f e := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun w _ ↦ hsplit w x
  have hout :
      (∑ w, ∑ e : {e : Q x w // ¬ σ e}, f e.1) +
          (∑ w, ∑ e : {e : Q x w // σ e}, f e.1) = ∑ w, ∑ e : Q x w, f e := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun w _ ↦ hsplit x w
  simp only [excessAt_def, sum_reorientAssignment, sum_sub_distrib]
  rw [← hin, ← hout]
  abel

end Excess

/-- The lower bound after reorientation: retained arrows keep their lower bound, while reversed
arrows receive the negation of their former upper bound. -/
def reorientLower (σ : Assignment Q Bool) (lo hi : Assignment Q K) :
    Assignment (ReorientHom Q σ) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ lo e.1) (fun e ↦ -hi e.1) e

/-- The upper bound after reorientation: retained arrows keep their upper bound, while reversed
arrows receive the negation of their former lower bound. -/
def reorientUpper (σ : Assignment Q Bool) (lo hi : Assignment Q K) :
    Assignment (ReorientHom Q σ) K :=
  fun _ _ e ↦ Sum.elim (fun e ↦ hi e.1) (fun e ↦ -lo e.1) e

@[simp]
theorem reorientLower_keep (σ : Assignment Q Bool) (lo hi : Assignment Q K) {x y : V}
    (e : Q x y) (h : ¬ σ e) :
    reorientLower σ lo hi (ReorientHom.keep σ e h) = lo e :=
  (rfl)

@[simp]
theorem reorientLower_flip (σ : Assignment Q Bool) (lo hi : Assignment Q K) {x y : V}
    (e : Q y x) (h : σ e) :
    reorientLower σ lo hi (ReorientHom.flip σ e h) = -hi e :=
  (rfl)

@[simp]
theorem reorientUpper_keep (σ : Assignment Q Bool) (lo hi : Assignment Q K) {x y : V}
    (e : Q x y) (h : ¬ σ e) :
    reorientUpper σ lo hi (ReorientHom.keep σ e h) = hi e :=
  (rfl)

@[simp]
theorem reorientUpper_flip (σ : Assignment Q Bool) (lo hi : Assignment Q K) {x y : V}
    (e : Q y x) (h : σ e) :
    reorientUpper σ lo hi (ReorientHom.flip σ e h) = -lo e :=
  (rfl)

section Order

variable [PartialOrder K] [ordered : IsOrderedAddMonoid K]

/-- Reorientation preserves feasibility: negating the value of a reversed arrow carries its
original interval exactly to the reversed interval. -/
@[simp]
theorem reorientAssignment_mem_Icc_iff (σ : Assignment Q Bool) (lo hi f : Assignment Q K) :
    reorientAssignment σ f ∈ Set.Icc (reorientLower σ lo hi) (reorientUpper σ lo hi) ↔
      f ∈ Set.Icc lo hi := by
  constructor
  · intro hf
    constructor <;> intro x y e
    · by_cases h : σ e
      · simpa using neg_le_neg (hf.2 y x (ReorientHom.flip σ e h))
      · exact hf.1 x y (ReorientHom.keep σ e h)
    · by_cases h : σ e
      · simpa using neg_le_neg (hf.1 y x (ReorientHom.flip σ e h))
      · exact hf.2 x y (ReorientHom.keep σ e h)
  · intro hf
    constructor <;> intro x y e
    · induction e using ReorientHom.inductionOn σ with
      | keep e h => exact hf.1 _ _ e
      | flip e h => exact neg_le_neg (hf.2 _ _ e)
    · induction e using ReorientHom.inductionOn σ with
      | keep e h => exact hf.2 _ _ e
      | flip e h => exact neg_le_neg (hf.1 _ _ e)

namespace Network

/-- Reorient a bounded network, negating arrow values and swapping the negated bounds on every
reversed arrow. This is reducible so its dependent arrow family computes for assignments. -/
@[expose, reducible] def reorient (N : Network K V)
    (σ : TauCeti.Assignment N.Hom Bool) : Network K V where
  Hom := ReorientHom N.Hom σ
  lower := reorientLower σ N.lower N.upper
  upper := reorientUpper σ N.lower N.upper
  lower_le_upper := by
    intro x y e
    induction e using ReorientHom.inductionOn σ with
    | keep e h => exact N.lower_le_upper e
    | flip e h => exact neg_le_neg (N.lower_le_upper e)

include ordered in
@[simp]
theorem reorient_Hom (N : Network K V) (σ : TauCeti.Assignment N.Hom Bool) :
    (N.reorient σ).Hom = ReorientHom N.Hom σ :=
  (rfl)

include ordered in
@[simp]
theorem reorient_lower_keep (N : Network K V) (σ : TauCeti.Assignment N.Hom Bool) {x y : V}
    (e : N.Hom x y) (h : ¬ σ e) :
    (N.reorient σ).lower (ReorientHom.keep σ e h) = N.lower e :=
  (rfl)

include ordered in
@[simp]
theorem reorient_lower_flip (N : Network K V) (σ : TauCeti.Assignment N.Hom Bool) {x y : V}
    (e : N.Hom y x) (h : σ e) :
    (N.reorient σ).lower (ReorientHom.flip σ e h) = -N.upper e :=
  (rfl)

include ordered in
@[simp]
theorem reorient_upper_keep (N : Network K V) (σ : TauCeti.Assignment N.Hom Bool) {x y : V}
    (e : N.Hom x y) (h : ¬ σ e) :
    (N.reorient σ).upper (ReorientHom.keep σ e h) = N.upper e :=
  (rfl)

include ordered in
@[simp]
theorem reorient_upper_flip (N : Network K V) (σ : TauCeti.Assignment N.Hom Bool) {x y : V}
    (e : N.Hom y x) (h : σ e) :
    (N.reorient σ).upper (ReorientHom.flip σ e h) = -N.lower e :=
  (rfl)

end Network

end Order

end AddCommGroup

end TauCeti
