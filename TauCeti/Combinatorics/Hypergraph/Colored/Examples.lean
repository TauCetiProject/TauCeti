/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Colored.Counting

/-!
# Small induced colored-copy counts

Use `true` for an edge and `false` for a nonedge. A three-vertex edge has six labeled
copies in itself, while a nonedge triple has no copies in the complete three-graph. The empty
vertex pattern has one copy even in an empty host, and oversized patterns have none.
-/

namespace TauCeti

open Colored3Graph

-- Reordering the vertices of a triple does not change its color.
example (H : Colored3Graph Bool (Fin 3)) :
    H.color (Set.powersetCard.ofCard (s := {0, 1, 2}) (by decide)) =
      H.color (Set.powersetCard.ofCard (s := {2, 1, 0}) (by decide)) := by
  congr 1
  decide

-- Labeled copies are not divided by the six automorphisms of a triple.
example : (const true : Colored3Graph Bool (Fin 3)).inducedCopyCount
    (FiniteColored3Pattern.const 3 true) = 6 := by
  simp [Nat.descFactorial]

-- Matching the nonedge color also gives six injections.
example : (const false : Colored3Graph Bool (Fin 3)).inducedCopyCount
    (FiniteColored3Pattern.const 3 false) = 6 := by
  simp [Nat.descFactorial]

-- Induced counting forbids a nonedge pattern in a complete host.
example : (const true : Colored3Graph Bool (Fin 3)).inducedCopyCount
    (FiniteColored3Pattern.const 3 false) = 0 := by
  apply inducedCopyCount_const_eq_zero
  exact ⟨Set.powersetCard.ofCard (s := Finset.univ) (by simp), by simp⟩

-- No triples means no color constraints, even for an arbitrary palette and host coloring.
example {κ : Type*} (H : Colored3Graph κ (Fin 3)) (F : FiniteColored3Pattern κ)
    (h : F.k = 2) : H.inducedCopyCount F = 6 := by
  rw [H.inducedCopyCount_of_lt_three F (by omega), h]
  decide

example : (const true : Colored3Graph Bool (Fin 0)).inducedCopyCount
    (FiniteColored3Pattern.const 0 false) = 1 := by
  rw [inducedCopyCount_of_lt_three _ _ (by simp)]
  simp

example : (const true : Colored3Graph Bool (Fin 2)).inducedCopyCount
    (FiniteColored3Pattern.const 3 true) = 0 := by
  apply inducedCopyCount_eq_zero_of_card_lt
  simp

end TauCeti
