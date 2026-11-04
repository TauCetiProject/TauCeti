/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Crossing
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

/-!
# The crossings of the standard `5 × 5` torus link grid

The standard `5 × 5` grid `TauCeti.GridDiagram.torusLink 1 2` has exactly three crossings, in the
squares `(1, 3)`, `(2, 1)` and `(3, 2)`, all of them negative. This checks the crossing predicate
and the sign convention of `TauCeti.KnotTheory.Grid.Diagram.Crossing` on a concrete grid.

## Main results

* `TauCeti.GridDiagram.crossings_torusLink_one_two`: the three crossings of `torusLink 1 2`.
* `TauCeti.GridDiagram.card_crossings_torusLink_one_two`: `torusLink 1 2` has three crossings.
* `TauCeti.GridDiagram.crossingSign_torusLink_one_two`: all three crossings are negative.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208 (2015), Section 3.1, for the planar link diagram of a grid diagram.
-/

public section

namespace TauCeti

namespace GridDiagram

/-- The row of the `X` marking in column `c` of the standard `5 × 5` grid. -/
private theorem torusLink_one_two_X_val (c : Fin 5) : ((torusLink 1 2).X c : ℕ) = (c + 3) % 5 :=
  torusLink_X_val 1 2 c

/-- The column of the `X` marking in row `r` of the standard `5 × 5` grid. -/
private theorem torusLink_one_two_X_transpose_val (r : Fin 5) :
    ((torusLink 1 2).X.transpose r : ℕ) = (r + 2) % 5 := by
  have h := torusLink_one_two_X_val ((torusLink 1 2).X.transpose r)
  rw [GridState.apply_transpose_apply] at h
  omega

/-- The row of the `O` marking in column `c` of the standard `5 × 5` grid. -/
private theorem torusLink_one_two_O_val (c : Fin 5) : ((torusLink 1 2).O c : ℕ) = c :=
  congrArg Fin.val (torusLink_O_apply 1 2 c)

/-- The column of the `O` marking in row `r` of the standard `5 × 5` grid. -/
private theorem torusLink_one_two_O_transpose_val (r : Fin 5) :
    ((torusLink 1 2).O.transpose r : ℕ) = r := by
  have h := torusLink_one_two_O_val ((torusLink 1 2).O.transpose r)
  rw [GridState.apply_transpose_apply] at h
  exact h.symm

/-- The standard `5 × 5` grid `torusLink 1 2` has exactly three crossings, in the squares
`(1, 3)`, `(2, 1)` and `(3, 2)`. -/
theorem crossings_torusLink_one_two :
    (torusLink 1 2).crossings = {(1, 3), (2, 1), (3, 2)} := by
  ext ⟨c, r⟩
  simp only [mem_crossings, isCrossing_iff, Fin.mem_uIoo_iff_val, torusLink_one_two_O_val,
    torusLink_one_two_O_transpose_val, torusLink_one_two_X_val,
    torusLink_one_two_X_transpose_val, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    Fin.ext_iff]
  fin_cases c <;> fin_cases r <;> decide

/-- The standard `5 × 5` grid `torusLink 1 2` has three crossings. -/
theorem card_crossings_torusLink_one_two : (torusLink 1 2).crossings.card = 3 := by
  rw [crossings_torusLink_one_two]
  decide

/-- All three crossings of the standard `5 × 5` grid `torusLink 1 2` are negative. -/
theorem crossingSign_torusLink_one_two {p : Fin 5 × Fin 5} (hp : p ∈ (torusLink 1 2).crossings) :
    (torusLink 1 2).crossingSign p.1 p.2 = -1 := by
  rw [crossings_torusLink_one_two] at hp
  rw [crossingSign_eq_neg_one_iff]
  simp only [Fin.lt_def, torusLink_one_two_O_val, torusLink_one_two_O_transpose_val,
    torusLink_one_two_X_val, torusLink_one_two_X_transpose_val]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> decide

end GridDiagram

end TauCeti
