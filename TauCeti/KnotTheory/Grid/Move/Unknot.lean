/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Move.Components

/-!
# The unknot as a grid link

The standard unknot grids of all sizes present one grid link, the unknot `GridLink.unknot`. The
standard grid of size `n + 3` is the `X`-stabilization of the standard grid of size `n + 2` that
splits the `X`-marking in its first column (`GridDiagram.isXStabilization_unknot_succ`), so by
induction every standard unknot grid is connected to the `2 × 2` grid by grid moves
(`GridDiagram.toGridLink_unknot`). This makes the unknot a well-defined grid link, independent of
the grid size used to present it.

## Main definitions

* `TauCeti.GridLink.unknot`: the unknot as a grid link.

## Main results

* `TauCeti.GridDiagram.isXStabilization_unknot_succ`: consecutive standard unknot grids are related
  by an `X`-stabilization.
* `TauCeti.GridDiagram.toGridLink_unknot`: every standard unknot grid presents the unknot.
* `TauCeti.GridLink.isKnot_unknot`: the unknot is a knot.

## References

The grid moves follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

/-- The standard unknot grid of size `n + 3` is the `X`-stabilization of the standard unknot grid
of size `n + 2` that splits the `X`-marking in its first column. -/
theorem isXStabilization_unknot_succ (n : ℕ) : IsXStabilization (unknot n) (unknot (n + 1)) := by
  refine (isXStabilization_iff _ _).mpr ⟨1, 1, 0, Or.inr ?_, Or.inl ?_, ?_⟩
  · ext
    simp [Fin.succAbove]
  · ext
    simp only [unknot_X_apply_eq_add_one, Fin.succAbove, Fin.lt_def]
    simp [Fin.val_add_one, Fin.ext_iff, Nat.mod_eq_of_lt]
  · refine GridDiagram.ext (GridState.ext fun c ↦ ?_) (GridState.ext fun c ↦ ?_)
    · rw [unknot_O_apply, stabilizeX_O]
      induction c using Fin.succAboveCases (1 : Fin (n + 3)) with
      | x => simp
      | p c => simp
    · rw [unknot_X_apply_eq_add_one, stabilizeX_X]
      induction c using Fin.succAboveCases (1 : Fin (n + 3)) with
      | x =>
        have h₂ : (1 + 1 : Fin (n + 3)) = 2 := by
          ext
          simp [Fin.val_add, Nat.mod_eq_of_lt]
        simp [h₂]
      | p c =>
        rw [GridState.splitPoint_apply_succAbove]
        split_ifs with hc
        · subst hc
          simp
        · rw [unknot_X_apply_eq_add_one]
          have hc' : (c : ℕ) ≠ 0 := fun h ↦ hc (Fin.ext h)
          -- The last column of the small grid wraps around to the bottom row.
          by_cases hl : c = Fin.last (n + 1)
          · subst hl
            rw [Fin.last_add_one, Fin.ext_iff, Fin.val_add_one]
            simp [Fin.succAbove, Fin.lt_def]
          · have hv : ((c + 1 : Fin (n + 2)) : ℕ) = c + 1 := by simp [Fin.val_add_one, hl]
            have hl' : (c : ℕ) ≠ n + 1 := fun h ↦ hl (Fin.ext h)
            rw [Fin.ext_iff, Fin.val_add_one]
            simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_one, Fin.ext_iff,
              Fin.val_last, hv]
            split_ifs <;> simp_all

end GridDiagram

namespace GridLink

/-- The unknot as a grid link: the grid link of the `2 × 2` grid diagram. Every standard unknot
grid presents it (`GridDiagram.toGridLink_unknot`). -/
def unknot : GridLink :=
  (GridDiagram.unknot 0).toGridLink

end GridLink

namespace GridDiagram

/-- Every standard unknot grid presents the unknot. -/
@[simp]
theorem toGridLink_unknot (n : ℕ) : (unknot n).toGridLink = GridLink.unknot := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    exact (IsStabilization.toGridLink_eq
      ((isStabilization_iff _ _).mpr (Or.inr (isXStabilization_unknot_succ n)))).symm

end GridDiagram

namespace GridLink

/-- The unknot is a knot. -/
@[simp]
theorem isKnot_unknot : unknot.IsKnot := by
  rw [← GridDiagram.toGridLink_unknot 0, isKnot_toGridLink]
  exact GridDiagram.isKnot_unknot 0

end GridLink

end TauCeti
