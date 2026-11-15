/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Grouping consecutive list elements into pairs

This file provides the elementary list operation that groups consecutive elements into disjoint
ordered pairs, dropping a possible final unpaired element.

## Main results

* `List.pairAdjacent` groups consecutive elements into pairs.
* `List.prod_map_pairAdjacent` recovers a mapped product from the pairs of an even-length list;
  `List.sum_map_pairAdjacent` is its additive version.
* `List.length_pairAdjacent` computes the number of pairs.
-/

public section

namespace List

variable {α β : Type*}

/-- Group consecutive elements into disjoint ordered pairs, dropping a final unpaired element. -/
def pairAdjacent : List α → List (α × α)
  | a :: b :: l => (a, b) :: pairAdjacent l
  | _ => []

/-- Multiplying the mapped entries of each consecutive pair recovers the mapped product of an
even-length list. The codomain need only be a semigroup with a `1`; no unit law is required. -/
@[to_additive /-- Adding the mapped entries of each consecutive pair recovers the mapped sum of an
even-length list. The codomain need only be an additive semigroup with a `0`; no unit law is
required. -/]
theorem prod_map_pairAdjacent [Semigroup β] [One β] (f : α → β) :
    ∀ (l : List α), Even l.length →
      ((pairAdjacent l).map fun p => f p.1 * f p.2).prod = (l.map f).prod
  | [], _ => by simp [pairAdjacent]
  | [_], hl => by simp at hl
  | a :: b :: l, hl => by
      simp [pairAdjacent, prod_map_pairAdjacent f l (by grind), mul_assoc]

/-- The number of consecutive pairs in a list is half its length, rounded down. -/
@[simp]
theorem length_pairAdjacent : ∀ (l : List α), (pairAdjacent l).length = l.length / 2
  | [] | [_] => by simp [pairAdjacent]
  | _ :: _ :: l => by simp [pairAdjacent, length_pairAdjacent l]; omega

end List
