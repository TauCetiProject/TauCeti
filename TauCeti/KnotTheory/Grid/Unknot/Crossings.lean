/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Crossings
public import TauCeti.KnotTheory.Grid.Unknot.Basic

/-!
# The planar diagram of the unknot grids has no crossings

In the standard unknot grid `TauCeti.GridDiagram.unknot n` the vertical segment of every column
but the last spans no row, and the only row whose horizontal segment spans a column is the bottom
one, which meets the vertical segment of the last column only at its `X`-marking. So the planar
diagram has no crossings (`TauCeti.GridDiagram.crossings_unknot`).
-/

public section

open Set

namespace TauCeti

namespace GridDiagram

/-- The standard unknot grids have no crossings: the vertical segment of every column but the last
spans no row, and the only row whose horizontal segment spans a column is the bottom one, which
meets the vertical segment of the last column only at its `X`-marking. -/
@[simp]
theorem crossings_unknot (n : ℕ) : (unknot n).crossings = ∅ := by
  ext ⟨c, r⟩
  simp only [mem_crossings, isCrossing_iff, Finset.notMem_empty, iff_false, not_and]
  intro hr hc
  -- The `X`-marking of a column `y` sits one row up, except in the last column.
  have hX (y : Fin (n + 2)) :
      ((unknot n).X y : ℕ) = y + 1 ∧ (y : ℕ) < n + 1 ∨
        ((unknot n).X y : ℕ) = 0 ∧ (y : ℕ) = n + 1 := by
    rw [unknot_X_apply_eq_add_one, Fin.val_add_one]
    split_ifs with h
    · exact .inr ⟨rfl, by simp [h]⟩
    · exact .inl ⟨rfl, by have := Fin.val_lt_last h; simpa using this⟩
  have hOt : (unknot n).O.transpose r = r := by
    simpa using (unknot n).O.transpose_apply_apply r
  have hXt := hX ((unknot n).X.transpose r)
  rw [(unknot n).X.apply_transpose_apply] at hXt
  rw [hOt] at hc
  simp only [mem_uIoo, Fin.lt_def] at hr hc
  simp only [unknot_O_apply] at hr
  rcases hX c with hXc | hXc <;> omega

/-- The unknot grids have no crossings. -/
theorem card_crossings_unknot (n : ℕ) : (unknot n).crossings.card = 0 := by
  simp

end GridDiagram

end TauCeti
