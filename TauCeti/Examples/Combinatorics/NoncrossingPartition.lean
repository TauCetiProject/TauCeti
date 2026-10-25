/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.NoncrossingPartition.Basic
import TauCeti.Combinatorics.NoncrossingPartition.Catalan
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Regression examples: noncrossing partitions

These examples exercise `Finpartition.IsNoncrossing` and the lattice of noncrossing partitions on
the four positions `0 < 1 < 2 < 3` of `Fin 4`, with concrete partitions given by the fibres of a
function:

* the crossing partition `{{0, 2}, {1, 3}}` is not noncrossing, while `{{0, 2}, {1}, {3}}` and
  `{{0}, {2}, {1, 3}}` are;
* those two noncrossing partitions have the crossing partition `{{0, 2}, {1, 3}}` as a common
  coarsening, but their join among noncrossing partitions is the partition with one part.

Final examples check that `NC(0)`, on the positions of `Fin 0`, has a single element, and that
`NC(3)` has `catalan 3 = 5` elements.
-/

open Finset Finpartition TauCeti

-- The partition `{{0, 2}, {1, 3}}`, the fibres of `![0, 1, 0, 1]`, crosses.
example :
    ¬ (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 0, 1]) fun _ _ => Nat.decEq _ _).IsNoncrossing := by
  decide

-- The partitions `{{0, 2}, {1}, {3}}` and `{{0}, {2}, {1, 3}}` do not cross, and the crossing
-- partition `{{0, 2}, {1, 3}}` is a common coarsening of both other than the partition with one
-- part.
example :
    (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 0, 3]) fun _ _ => Nat.decEq _ _).IsNoncrossing ∧
    (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 2, 1]) fun _ _ => Nat.decEq _ _).IsNoncrossing ∧
    (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 0, 3]) fun _ _ => Nat.decEq _ _) ≤
      (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 0, 1]) fun _ _ => Nat.decEq _ _) ∧
    (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 2, 1]) fun _ _ => Nat.decEq _ _) ≤
      (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 0, 1]) fun _ _ => Nat.decEq _ _) ∧
    ¬ ⊤ ≤ (@ofSetoid _ _ _ (Setoid.ker ![0, 1, 0, 1]) fun _ _ => Nat.decEq _ _) := by
  decide

-- The join among noncrossing partitions of one with `0` and `2` in a part and one with `1` and `3`
-- in a part is the partition with one part.
example (P Q : NoncrossingPartition (univ : Finset (Fin 4))) (hP : 2 ∈ P.1.part 0)
    (hQ : 3 ∈ Q.1.part 1) : P ⊔ Q = ⊤ := by
  suffices h : ∀ R : NoncrossingPartition (univ : Finset (Fin 4)), P ≤ R → Q ≤ R → ⊤ ≤ R from
    top_le_iff.1 (h _ le_sup_left le_sup_right)
  intro R hPR hQR
  have h02 : 2 ∈ R.1.part 0 := part_mono (Subtype.coe_le_coe.2 hPR) 0 hP
  have h13 : 3 ∈ R.1.part 1 := part_mono (Subtype.coe_le_coe.2 hQR) 1 hQ
  have h01 := isNoncrossing_iff_part.1 R.2 0 (mem_univ _) 1 (mem_univ _) 2 h02 3 h13
    (by decide) (by decide) (by decide)
  refine Subtype.coe_le_coe.1 <| le_def.2 fun B hB =>
    ⟨R.1.part 0, R.1.part_mem.2 (mem_univ _), ?_⟩
  rw [NoncrossingPartition.coe_top] at hB
  rw [Finset.mem_singleton.1 (parts_top_subset _ hB)]
  intro x _
  fin_cases x
  · exact R.1.mem_part_self.2 (mem_univ _)
  · exact h01 ▸ R.1.mem_part_self.2 (mem_univ _)
  · exact h02
  · exact h01 ▸ h13

-- `NC(0)` consists of the empty partition alone.
example : Unique (NoncrossingPartition (univ : Finset (Fin 0))) := inferInstance

-- `NC(3)` has `catalan 3 = 5` elements.
example : Fintype.card (NoncrossingPartition (univ : Finset (Fin 3))) = 5 := by
  rw [NoncrossingPartition.card_fin_eq_catalan, catalan_three]
