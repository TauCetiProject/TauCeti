/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Crossings
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

/-!
# Crossings of the torus link grids

Every crossing of the planar diagram of the standard torus link grid
`TauCeti.GridDiagram.torusLink p q` is negative (`TauCeti.GridDiagram.crossingSign_torusLink`).
On the `5 × 5` trefoil grid `torusLink 1 2` there are exactly three crossings
(`TauCeti.GridDiagram.crossings_torusLink_one_two`). These are the signs of the left-handed
trefoil, the mirror of the positive torus knot.
-/

public section

open Set

namespace TauCeti

namespace GridDiagram

/-- **Every crossing of a torus link grid is negative.** In the first `p + 1` columns the vertical
segment runs down from the `X`-marking `q + 1` rows above the diagonal, and every crossing on it
lies in a row whose horizontal segment runs to the left; in the last `q + 1` columns the vertical
segment runs up, and every crossing on it lies in a row whose horizontal segment runs to the
right. -/
theorem crossingSign_torusLink (p q : ℕ) {x : Fin (p + 1 + (q + 1)) × Fin (p + 1 + (q + 1))}
    (hx : x ∈ (torusLink p q).crossings) : (torusLink p q).crossingSign x = -1 := by
  obtain ⟨c, r⟩ := x
  rw [mem_crossings, isCrossing_iff] at hx
  rw [crossingSign_eq_neg_one_iff]
  set d := (torusLink p q).X.transpose r
  have hOt : (torusLink p q).O.transpose r = r := by
    simpa using (torusLink p q).O.transpose_apply_apply r
  -- The rows of the `X`-markings of `c` and of `d`, whose `X`-marking lies in row `r`.
  have hX (y : Fin (p + 1 + (q + 1))) :
      ((torusLink p q).X y : ℕ) = y + (q + 1) ∧ (y : ℕ) ≤ p ∨
        ((torusLink p q).X y : ℕ) = y - (p + 1) ∧ p < (y : ℕ) := by
    rcases le_or_gt (y : ℕ) p with hy | hy
    · exact .inl ⟨torusLink_X_val_of_le p q hy, hy⟩
    · exact .inr ⟨torusLink_X_val_of_lt p q hy, hy⟩
  have hXd := hX d
  rw [(torusLink p q).X.apply_transpose_apply] at hXd
  have hXc := hX c
  rw [hOt] at hx ⊢
  simp only [torusLink_O_apply, mem_uIoo] at hx ⊢
  simp only [Fin.lt_def] at hx ⊢
  have := c.isLt
  have := d.isLt
  omega

/-- The crossings of the `5 × 5` trefoil grid: the squares `(1, 3)`, `(2, 1)` and `(3, 2)`. -/
theorem crossings_torusLink_one_two :
    (torusLink 1 2).crossings = {(1, 3), (2, 1), (3, 2)} := by
  ext ⟨c, r⟩
  simp only [mem_crossings, isCrossing_iff, mem_uIoo, GridState.transpose_apply,
    torusLink_O_toPerm, torusLink_X_toPerm]
  -- The marking permutations are explicit, so `decide` evaluates every square.
  revert c r
  decide

/-- The `5 × 5` trefoil grid has three crossings. -/
theorem card_crossings_torusLink_one_two : (torusLink 1 2).crossings.card = 3 := by
  rw [crossings_torusLink_one_two]
  decide

end GridDiagram

end TauCeti
