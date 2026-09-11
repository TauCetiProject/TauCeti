/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Nat.Even
import Lean.Elab.Tactic.Omega

/-!
# Grouping consecutive list elements into pairs

This file provides the elementary list operation that groups consecutive elements into disjoint
ordered pairs, dropping a possible final unpaired element.

## Main results

* `List.pairAdjacent` groups consecutive elements into pairs.
* `List.prod_map_pairAdjacent` recovers a mapped product from the pairs of an even-length list.
* `List.length_pairAdjacent` computes the number of pairs.
-/

public section

namespace List

universe u v

/-- Group consecutive elements into disjoint ordered pairs, dropping a final unpaired element. -/
def pairAdjacent {α : Type u} : List α → List (α × α)
  | a :: b :: l => (a, b) :: pairAdjacent l
  | _ => []

/-- Multiplying the mapped entries of each consecutive pair recovers the mapped product of an
even-length list. -/
theorem prod_map_pairAdjacent {α : Type u} {β : Type v} [Monoid β] (f : α → β) :
    ∀ (l : List α), Even l.length →
      ((pairAdjacent l).map fun p => f p.1 * f p.2).prod = (l.map f).prod
  | [], _ => by simp [pairAdjacent]
  | [_], hl => by simp at hl
  | a :: b :: l, hl => by
      have htail : Even l.length := by
        obtain ⟨k, hk⟩ := hl
        use k - 1
        simp only [List.length_cons] at hk
        omega
      simp only [pairAdjacent, List.map_cons, List.prod_cons,
        prod_map_pairAdjacent f l htail, mul_assoc]

/-- The number of consecutive pairs in a list is half its length, rounded down. -/
@[simp]
theorem length_pairAdjacent {α : Type u} : ∀ (l : List α),
    (pairAdjacent l).length = l.length / 2
  | [] => by simp [pairAdjacent]
  | [_] => by simp [pairAdjacent]
  | _ :: _ :: l => by
      rw [pairAdjacent, List.length_cons, List.length_cons, List.length_cons,
        length_pairAdjacent]
      omega

end List
