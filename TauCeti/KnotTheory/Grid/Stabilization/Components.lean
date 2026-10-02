/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.Stabilization.Basic

/-!
# Link components under grid stabilization

A stabilization splits one marking of a grid diagram across an inserted row and column and puts
a marking of the other type at their intersection. Along the link this inserts one short
horizontal and one short vertical segment into the component through the split marking, so the
number of components does not change.

On the component permutation `c ↦ X⁻¹(O(c))` this is visible directly. For the stabilization
`G.stabilizeX p q s` splitting the `X`-marking of column `s`, write `ι = p.succAbove` for the
embedding of the old columns and `σ` for the old component permutation. The new permutation sends
the new column `p` to `ι s`, and sends `ι c` to `ι (σ c)`, except that the column `ι c` with
`σ c = s` now goes to `p`. So the new column is spliced into the cycle through `ι s`, just before
it. An `O`-stabilization is an `X`-stabilization after exchanging the two marking types.

These statements need no adjacency of the new row and column to the split marking, so they hold
for the constructions `GridDiagram.stabilizeX` and `GridDiagram.stabilizeO` themselves, and in
particular for every elementary stabilization of each of the eight corner types.

## Main results

* `TauCeti.GridDiagram.componentPerm_stabilizeX_newColumn` and
  `TauCeti.GridDiagram.componentPerm_stabilizeX_succAbove`: the component permutation of an
  `X`-stabilization.
* `TauCeti.GridDiagram.componentCount_stabilizeX` and
  `TauCeti.GridDiagram.componentCount_stabilizeO`: both stabilization constructions preserve the
  number of components.
* `TauCeti.GridDiagram.IsStabilization.componentCount_eq` and
  `TauCeti.GridDiagram.IsStabilization.isKnot_iff`: every elementary stabilization preserves the
  number of components and whether the diagram represents a knot.

## Implementation notes

The count is compared through `TauCeti.orbitCount`, using
`TauCeti.GridDiagram.componentCount_eq_orbitCount`. Cutting the new column back out of its cycle,
by the transposition of `p` and `ι s`, gives a permutation that fixes `p` and is carried from `σ`
by `ι`. Adjoining a fixed point adds one orbit (`TauCeti.orbitCount_add_one_eq_of_semiconj`) and
splicing it into another orbit removes one (`TauCeti.orbitCount_mul_swap_add_one`).

## References

The stabilization moves follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

open Equiv

variable {n : ℕ} (G : GridDiagram n) (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n)

/-- In an `X`-stabilization, the component through the new column continues to the embedded split
column: the new `O`-marking shares its row with the `X`-marking moved into the split column. -/
@[simp]
theorem componentPerm_stabilizeX_newColumn :
    (G.stabilizeX newColumn newRow splitColumn).componentPerm newColumn =
      newColumn.succAbove splitColumn := by
  rw [componentPerm_apply_eq_iff]
  simp

/-- In an `X`-stabilization, an embedded old column continues to the embedded image of its old
successor along the component, except that the column whose old successor is the split column
now continues to the new column. -/
@[simp]
theorem componentPerm_stabilizeX_succAbove (c : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).componentPerm (newColumn.succAbove c) =
      if G.componentPerm c = splitColumn then newColumn
      else newColumn.succAbove (G.componentPerm c) := by
  rw [componentPerm_apply_eq_iff]
  rw [stabilizeX_X, stabilizeX_O, GridState.insertPoint_apply_succAbove]
  split_ifs with h
  · rw [GridState.splitPoint_apply_newColumn, ← h, X_componentPerm_apply]
  · simp only [GridState.splitPoint_apply_succAbove, h, ↓reduceIte, X_componentPerm_apply]

/-- An `X`-stabilization does not change the number of link components: the new column is spliced
into the component through the split marking. -/
@[simp]
theorem componentCount_stabilizeX :
    (G.stabilizeX newColumn newRow splitColumn).componentCount = G.componentCount := by
  set a := newColumn.succAbove splitColumn with ha
  -- Cutting the new column out of its cycle leaves a permutation fixing it.
  set τ := swap newColumn a * (G.stabilizeX newColumn newRow splitColumn).componentPerm with hτ
  have hτp : τ newColumn = newColumn := by
    rw [hτ, Perm.mul_apply, componentPerm_stabilizeX_newColumn, ← ha, swap_apply_right]
  -- Away from the new column, that permutation is the old component permutation.
  have hsemiconj : Function.Semiconj newColumn.succAbove G.componentPerm τ := by
    intro c
    rw [hτ, Perm.mul_apply, componentPerm_stabilizeX_succAbove]
    split_ifs with h
    · rw [swap_apply_left, ha, h]
    · exact (swap_apply_of_ne_of_ne (newColumn.succAbove_ne _)
        fun h' ↦ h (Fin.succAbove_right_injective h')).symm
  have hadjoin := orbitCount_add_one_eq_of_semiconj Fin.succAbove_right_injective
    newColumn.succAbove_ne (fun _ hy ↦ Fin.exists_succAbove_eq hy) hsemiconj
  have hsplice := orbitCount_mul_swap_add_one (a := a) hτp (newColumn.succAbove_ne splitColumn)
  have hperm :
      (G.stabilizeX newColumn newRow splitColumn).componentPerm = swap newColumn a * τ := by
    rw [hτ, ← mul_assoc, swap_mul_self, one_mul]
  rw [componentCount_eq_orbitCount, componentCount_eq_orbitCount, hperm, orbitCount_mul_comm,
    swap_comm]
  omega

/-- An `O`-stabilization does not change the number of link components. -/
@[simp]
theorem componentCount_stabilizeO :
    (G.stabilizeO newColumn newRow splitColumn).componentCount = G.componentCount := by
  rw [← componentCount_swapMarkings, stabilizeO_swapMarkings, componentCount_stabilizeX,
    componentCount_swapMarkings]

/-- An `X`-stabilization represents a knot exactly when the original diagram does. -/
@[simp]
theorem isKnot_stabilizeX :
    (G.stabilizeX newColumn newRow splitColumn).IsKnot ↔ G.IsKnot := by
  rw [isKnot_def, componentCount_stabilizeX, isKnot_def]

/-- An `O`-stabilization represents a knot exactly when the original diagram does. -/
@[simp]
theorem isKnot_stabilizeO :
    (G.stabilizeO newColumn newRow splitColumn).IsKnot ↔ G.IsKnot := by
  rw [isKnot_def, componentCount_stabilizeO, isKnot_def]

variable {G} {G' : GridDiagram (n + 1)}

/-- Every elementary stabilization preserves the number of represented link components. -/
theorem IsStabilization.componentCount_eq (h : IsStabilization G G') :
    G'.componentCount = G.componentCount := by
  rcases (isStabilization_iff G G').mp h with h | h
  · obtain ⟨_, _, _, _, _, rfl⟩ := (isOStabilization_iff G G').mp h
    exact G.componentCount_stabilizeO _ _ _
  · obtain ⟨_, _, _, _, _, rfl⟩ := (isXStabilization_iff G G').mp h
    exact G.componentCount_stabilizeX _ _ _

/-- Every elementary stabilization preserves whether a grid diagram represents a knot. -/
theorem IsStabilization.isKnot_iff (h : IsStabilization G G') : G'.IsKnot ↔ G.IsKnot := by
  rw [isKnot_def, h.componentCount_eq, isKnot_def]

end GridDiagram

end TauCeti
