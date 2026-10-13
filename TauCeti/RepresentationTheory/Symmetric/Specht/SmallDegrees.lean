/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.HookLength
public import TauCeti.Combinatorics.Enumerative.Partition.Small

/-!
# Specht dimensions on four and five letters

The hook-length formula gives degrees `1, 3, 2, 3, 1` for the five shapes of size four and
`1, 4, 5, 6, 5, 4, 1` for the seven shapes of size five, in decreasing lexicographic order.
The formulas below apply to every partition of the respective size. By
`TauCeti.finrank_spechtModule`, these degrees also count the standard Young tableaux and hence
the vectors of `TauCeti.spechtModuleStandardBasis` for each shape.

## References

* B. E. Sagan, *The Symmetric Group*, second edition, §3.10 (the hook-length formula).
-/

public section

namespace Nat.Partition

open TauCeti

/-- The degrees of the Specht modules of `S₄`, indexed by their decreasing row lengths. -/
theorem finrank_spechtModule_four (μ : Nat.Partition 4) :
    Module.finrank ℚ (spechtModule μ) =
      match μ.parts.sort (· ≥ ·) with
      | [4] => 1
      | [3, 1] => 3
      | [2, 2] => 2
      | [2, 1, 1] => 3
      | [1, 1, 1, 1] => 1
      | _ => 0 := by
  rw [finrank_spechtModule_eq_factorial_div_prod_hookLength]
  rcases μ.sort_parts_four with h | h | h | h | h
  all_goals
    simp only [YoungDiagram.hookLength_def, YoungDiagram.armLength_def,
      YoungDiagram.legLength_def]
    rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := diagramOf μ)]
    simp only [rowLens_diagramOf, h, YoungDiagram.rowLen_eq_card,
      YoungDiagram.colLen_eq_card, YoungDiagram.row, YoungDiagram.col, YoungDiagram.ofRowLens]
    norm_num [YoungDiagram.cellsOfRowLens, Finset.range_add_one, Finset.filter_insert,
      Finset.filter_singleton, Nat.factorial]

/-- The degrees of the Specht modules of `S₅`, indexed by their decreasing row lengths. -/
theorem finrank_spechtModule_five (μ : Nat.Partition 5) :
    Module.finrank ℚ (spechtModule μ) =
      match μ.parts.sort (· ≥ ·) with
      | [5] => 1
      | [4, 1] => 4
      | [3, 2] => 5
      | [3, 1, 1] => 6
      | [2, 2, 1] => 5
      | [2, 1, 1, 1] => 4
      | [1, 1, 1, 1, 1] => 1
      | _ => 0 := by
  rw [finrank_spechtModule_eq_factorial_div_prod_hookLength]
  rcases μ.sort_parts_five with h | h | h | h | h | h | h
  all_goals
    simp only [YoungDiagram.hookLength_def, YoungDiagram.armLength_def,
      YoungDiagram.legLength_def]
    rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := diagramOf μ)]
    simp only [rowLens_diagramOf, h, YoungDiagram.rowLen_eq_card,
      YoungDiagram.colLen_eq_card, YoungDiagram.row, YoungDiagram.col, YoungDiagram.ofRowLens]
    norm_num [YoungDiagram.cellsOfRowLens, Finset.range_add_one, Finset.filter_insert,
      Finset.filter_singleton, Nat.factorial]

end Nat.Partition
