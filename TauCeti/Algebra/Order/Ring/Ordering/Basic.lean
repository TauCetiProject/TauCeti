/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Ring.Ordering.Basic

import Mathlib.Tactic.Ring

/-! # Basic constructions for ring preorderings

We describe adjoining one element to a preordering and its least-extension property.
Nonempty directed suprema preserve preorderings. Over a field, a preordering that
contains one sign of every element is an ordering.

The one-element construction is part of the classical preordering extension
argument; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 3](https://www.math.uni-konstanz.de/algebra/WS0910/Notes03.pdf),
Lemma 2.1. The proper extension to an ordering is proved in
`TauCeti.Algebra.Order.Ring.Ordering.Extension`.
-/

public section

namespace Subsemiring.IsPreordering

section CommRing

variable {R : Type*} [CommRing R] {P : Subsemiring R}

/-- Adjoin an element to a preordering using expressions `u + a * v`.
The resulting subsemiring need not remain a proper preordering. -/
def adjoin (hP : P.IsPreordering) (a : R) : Subsemiring R where
  carrier := {x | ∃ u ∈ P, ∃ v ∈ P, x = u + a * v}
  zero_mem' := ⟨0, P.zero_mem, 0, P.zero_mem, by simp⟩
  one_mem' := ⟨1, P.one_mem, 0, P.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
    exact ⟨u + w, P.add_mem hu hw, v + z, P.add_mem hv hz, by ring⟩
  mul_mem' := by
    rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
    exact ⟨u * w + a ^ 2 * (v * z),
      P.add_mem (P.mul_mem hu hw) (P.mul_mem (hP.pow_two_mem a) (P.mul_mem hv hz)),
      u * z + v * w, P.add_mem (P.mul_mem hu hz) (P.mul_mem hv hw), by ring⟩

/-- Membership in the extension is a linear expression with coefficients in the cone. -/
@[simp] theorem mem_adjoin (hP : P.IsPreordering) (a x : R) :
    x ∈ hP.adjoin a ↔ ∃ u ∈ P, ∃ v ∈ P, x = u + a * v := Iff.rfl

/-- The one-element extension contains the original preordering. -/
@[simp] theorem le_adjoin (hP : P.IsPreordering) (a : R) : P ≤ hP.adjoin a :=
  fun x hx => ⟨x, hx, 0, P.zero_mem, by simp⟩

/-- The adjoined element belongs to the extension. -/
-- Apply this before `mem_adjoin` expands membership into an existential formula.
@[simp↓] theorem self_mem_adjoin (hP : P.IsPreordering) (a : R) : a ∈ hP.adjoin a :=
  ⟨0, P.zero_mem, 1, P.one_mem, by simp⟩

/-- The extension is the least subsemiring containing the cone and the adjoined element. -/
@[simp] theorem adjoin_le_iff (hP : P.IsPreordering) (a : R) {Q : Subsemiring R} :
    hP.adjoin a ≤ Q ↔ P ≤ Q ∧ a ∈ Q := by
  refine ⟨fun h ↦ ⟨(hP.le_adjoin a).trans h, h (hP.self_mem_adjoin a)⟩, ?_⟩
  rintro ⟨hPQ, ha⟩ x ⟨u, hu, v, hv, rfl⟩
  exact Q.add_mem (hPQ hu) (Q.mul_mem ha (hPQ hv))

/-- A nonempty directed supremum of preorderings is a preordering. -/
theorem iSup {ι : Type*} [Nonempty ι] {S : ι → Subsemiring R}
    (hS : ∀ i, (S i).IsPreordering) (hd : Directed (· ≤ ·) S) :
    (⨆ i, S i).IsPreordering where
  mem_of_isSquare := by
    intro x hx
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact le_iSup S i ((hS i).mem_of_isSquare hx)
  neg_one_notMem := by
    intro hx
    obtain ⟨i, hi⟩ := (Subsemiring.mem_iSup_of_directed hd).mp hx
    exact (hS i).neg_one_notMem hi

end CommRing

/-- A field preordering that contains one sign of every element is an ordering. -/
theorem isOrdering_of_isSpanning {K : Type*} [Field K] {P : Subsemiring K}
    (hP : P.IsPreordering) (hs : P.IsSpanning) : P.IsOrdering := by
  have hbot : P.supportIdeal hs = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    rw [Subsemiring.mem_supportIdeal, Subsemiring.mem_support] at hx
    exact Ideal.mem_bot.mpr (hP.isPointed.eq_zero_of_mem_of_neg_mem hx.1 hx.2)
  apply Subsemiring.IsOrdering.of_isPrime_supportIdeal hs
  rw [hbot]
  infer_instance

end Subsemiring.IsPreordering
