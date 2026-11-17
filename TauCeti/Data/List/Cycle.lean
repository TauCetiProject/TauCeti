/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.List.Cycle
import Mathlib.Data.Bool.Count

/-!
# Orientation reversal on signed cycles

A signed cyclic word `Cycle (α × Bool)` records a cyclic sequence of elements of `α` equipped with
orientation bits (`true` for forward, `false` for backward), as arises on segmented boundary
components of oriented 2-dimensional foams and surfaces. Reversing the orientation of the ambient
cycle reverses the cyclic order while simultaneously negating every orientation bit.

## Main definitions and results

* `Cycle.reverseSigned`: reverse cyclic order and negate every `Bool` sign bit on
  `Cycle (α × Bool)`.
* `Cycle.reverseSigned_reverseSigned`: `Cycle.reverseSigned` is an involution.
* `Cycle.count_reverseSigned_snd`: `Cycle.reverseSigned` swaps the multiset counts of `true` and
  `false` sign bits.
* `Cycle.ne_reverseSigned_of_count_ne` and `Cycle.ne_reverseSigned_of_odd_length`: a signed cycle
  with unequal `true` and `false` sign counts—in particular, any signed cycle of odd length—is
  distinct from its orientation reversal.
-/

public section

namespace Cycle

/-- Reverse the orientation of a signed cyclic word by reversing cyclic order and negating every
sign bit. -/
def reverseSigned {α : Type*} (w : Cycle (α × Bool)) : Cycle (α × Bool) :=
  w.reverse.map (Prod.map id Bool.not)

theorem reverseSigned_def {α : Type*} (w : Cycle (α × Bool)) :
    w.reverseSigned = w.reverse.map (Prod.map id Bool.not) := (rfl)

@[simp] theorem reverseSigned_nil {α : Type*} :
    (Cycle.nil : Cycle (α × Bool)).reverseSigned = Cycle.nil := by
  simp [reverseSigned]

@[simp] theorem reverseSigned_coe {α : Type*} (l : List (α × Bool)) :
    (l : Cycle (α × Bool)).reverseSigned = l.reverse.map (Prod.map id Bool.not) := by
  simp [reverseSigned]

@[simp] theorem mem_reverseSigned {α : Type*} {x : α × Bool} {w : Cycle (α × Bool)} :
    x ∈ w.reverseSigned ↔ (x.1, !x.2) ∈ w := by
  rcases x with ⟨x1, x2⟩
  rw [reverseSigned, Cycle.mem_map]
  simp only [Cycle.mem_reverse_iff, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
  refine ⟨fun ⟨_, b, hab, rfl, hb⟩ ↦ ?_, fun h ↦ ⟨x1, !x2, h, rfl, Bool.not_not x2⟩⟩
  rwa [← hb, Bool.not_not]

@[simp] theorem reverseSigned_reverseSigned {α : Type*} (w : Cycle (α × Bool)) :
    w.reverseSigned.reverseSigned = w := by
  induction w with
  | nil => simp
  | cons a l _ =>
    have hmap : ∀ u : List (α × Bool),
        (u.map (Prod.map id Bool.not)).map (Prod.map id Bool.not) = u := by
      intro u
      rw [List.map_map]
      convert List.map_id u
      ext ⟨_, b⟩ <;> simp
    rw [reverseSigned_coe, reverseSigned_coe, ← List.map_reverse, List.reverse_reverse, hmap]

@[simp] theorem length_reverseSigned {α : Type*} (w : Cycle (α × Bool)) :
    w.reverseSigned.length = w.length := by
  induction w with
  | nil => simp
  | cons a l _ => simp

/-- Orientation reversal exchanges the multiset counts of `true` and `false` sign bits. -/
@[simp] theorem count_reverseSigned_snd {α : Type*} (w : Cycle (α × Bool)) (b : Bool) :
    Multiset.count b (w.reverseSigned.toMultiset.map Prod.snd) =
      Multiset.count (!b) (w.toMultiset.map Prod.snd) := by
  induction w with
  | nil => simp
  | cons a l _ =>
    set u : List (α × Bool) := a :: l
    have hcomp : (Prod.snd ∘ Prod.map (id : α → α) Bool.not) = Bool.not ∘ Prod.snd := rfl
    rw [reverseSigned_coe, Cycle.coe_toMultiset, Cycle.coe_toMultiset,
      Multiset.map_coe, Multiset.map_coe, List.map_map, hcomp, List.map_reverse,
      Multiset.coe_reverse, ← List.map_map, ← Multiset.map_coe]
    simpa using Multiset.count_map_eq_count' Bool.not (u.map Prod.snd : Multiset Bool)
      (Function.Involutive.injective Bool.not_not) (!b)

/-- A signed cycle whose `true` and `false` sign counts differ cannot equal its orientation
reversal. -/
theorem ne_reverseSigned_of_count_ne {α : Type*} {w : Cycle (α × Bool)}
    (h : Multiset.count true (w.toMultiset.map Prod.snd) ≠
      Multiset.count false (w.toMultiset.map Prod.snd)) :
    w ≠ w.reverseSigned := by
  intro hw
  apply h
  have hc :=
    congrArg (fun c : Cycle (α × Bool) ↦ Multiset.count true (c.toMultiset.map Prod.snd)) hw
  simpa [count_reverseSigned_snd] using hc

/-- Every signed cycle of odd length is distinct from its orientation reversal. -/
theorem ne_reverseSigned_of_odd_length {α : Type*} {w : Cycle (α × Bool)}
    (hw : Odd w.length) : w ≠ w.reverseSigned := by
  apply ne_reverseSigned_of_count_ne
  intro heq
  have hwlen : Multiset.count true (w.toMultiset.map Prod.snd) +
      Multiset.count false (w.toMultiset.map Prod.snd) = w.length := by
    rw [← Cycle.card_toMultiset, ← Multiset.card_map Prod.snd]
    exact Quot.inductionOn (w.toMultiset.map Prod.snd) fun l ↦ by
      rw [Multiset.quot_mk_to_coe'', Multiset.coe_count, Multiset.coe_count, Multiset.coe_card]
      exact List.count_true_add_count_false l
  obtain ⟨k, hk⟩ := hw
  omega

end Cycle
