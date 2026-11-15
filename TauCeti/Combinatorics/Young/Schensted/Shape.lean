/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Schensted.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# The shape of a list of tableau rows

A list of rows satisfying `List.IsTableauRows` has weakly decreasing positive row lengths, so it
determines a Young diagram `List.tableauShape`. Its row lengths are the lengths of the rows
(`List.rowLens_tableauShape`) and its number of cells is the number of entries
(`List.card_tableauShape`).
-/

public section

namespace List

/-- The Young diagram whose row lengths are the lengths of a semistandard list of tableau rows. -/
def tableauShape {α : Type*} [Preorder α]
    (rows : List (List α)) (hrows : rows.IsTableauRows) : YoungDiagram :=
  YoungDiagram.ofRowLens (rows.map length) hrows.sortedGE_map_length

/-- The row lengths of the shape inferred from tableau rows are the lengths of those rows. -/
@[simp]
theorem rowLens_tableauShape {α : Type*} [Preorder α]
    (rows : List (List α)) (hrows : rows.IsTableauRows) :
    (tableauShape rows hrows).rowLens = rows.map length := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro k hk
  obtain ⟨row, hrow, rfl⟩ := mem_map.mp hk
  exact List.length_pos_iff.mpr fun hnil => hrows.nil_notMem (hnil ▸ hrow)

/-- The number of cells in the shape inferred from tableau rows is the length of their
flattening. -/
@[simp]
theorem card_tableauShape {α : Type*} [Preorder α]
    (rows : List (List α)) (hrows : rows.IsTableauRows) :
    (tableauShape rows hrows).card = rows.flatten.length := by
  rw [← YoungDiagram.sum_rowLens_eq_card, rowLens_tableauShape, length_flatten]

end List
