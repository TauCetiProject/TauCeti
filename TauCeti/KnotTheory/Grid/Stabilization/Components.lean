/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Splice
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

Consequently the components of `G` and of the stabilization correspond
(`GridDiagram.componentsStabilizeXEquiv`): the component of an old column goes to that of its
embedded column, and the new column lies on the component of the split column.

These statements need no adjacency of the new row and column to the split marking, so they hold
for the constructions `GridDiagram.stabilizeX` and `GridDiagram.stabilizeO` themselves, and in
particular for every elementary stabilization of each of the eight corner types.

## Main definitions

* `TauCeti.GridDiagram.componentsStabilizeXEquiv`: the correspondence between the components of a
  grid diagram and of its `X`-stabilization.

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

Cutting the new column back out of its cycle, by the transposition of `p` with the embedded
predecessor of `s`, gives a permutation that fixes `p` and is carried from `σ` by `ι`
(`TauCeti.GridDiagram.semiconj_componentPerm_stabilizeX_mul_swap`). The component equivalence is
then `Equiv.Perm.orbitQuotientEquivSplice`, and the component count is compared through it.

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
theorem componentPerm_stabilizeX_newColumn :
    (G.stabilizeX newColumn newRow splitColumn).componentPerm newColumn =
      newColumn.succAbove splitColumn := by
  rw [componentPerm_apply_eq_iff]
  simp

/-- In an `X`-stabilization, an embedded old column continues to the embedded image of its old
successor along the component, except that the column whose old successor is the split column
now continues to the new column. -/
theorem componentPerm_stabilizeX_succAbove (c : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).componentPerm (newColumn.succAbove c) =
      if G.componentPerm c = splitColumn then newColumn
      else newColumn.succAbove (G.componentPerm c) := by
  rw [componentPerm_apply_eq_iff]
  rw [stabilizeX_X, stabilizeX_O, GridState.insertPoint_apply_succAbove]
  split_ifs with h
  · rw [GridState.splitPoint_apply_newColumn, ← h, X_componentPerm_apply]
  · simp only [GridState.splitPoint_apply_succAbove, h, ↓reduceIte, X_componentPerm_apply]

/-- In an `X`-stabilization, the new column lies on the component of the embedded split column. -/
theorem sameCycle_componentPerm_stabilizeX_newColumn :
    (G.stabilizeX newColumn newRow splitColumn).componentPerm.SameCycle newColumn
      (newColumn.succAbove splitColumn) :=
  ⟨1, by rw [zpow_one, componentPerm_stabilizeX_newColumn]⟩

/-- Cutting the new column out of the component permutation of an `X`-stabilization, by
transposing it with the embedded old predecessor of the split column, leaves the old component
permutation carried along the embedding of the old columns. -/
theorem semiconj_componentPerm_stabilizeX_mul_swap :
    Function.Semiconj newColumn.succAbove G.componentPerm
      ⇑((G.stabilizeX newColumn newRow splitColumn).componentPerm *
        swap (newColumn.succAbove (G.componentPerm.symm splitColumn)) newColumn) := by
  intro c
  rw [Perm.mul_apply]
  by_cases hc : G.componentPerm c = splitColumn
  · obtain rfl : c = G.componentPerm.symm splitColumn := by rw [← hc, Equiv.symm_apply_apply]
    rw [swap_apply_left, componentPerm_stabilizeX_newColumn, hc]
  · have hne : newColumn.succAbove c ≠ newColumn.succAbove (G.componentPerm.symm splitColumn) :=
      fun h ↦ hc (by rw [Fin.succAbove_right_injective h, Equiv.apply_symm_apply])
    rw [swap_apply_of_ne_of_ne hne (newColumn.succAbove_ne c), componentPerm_stabilizeX_succAbove]
    simp only [hc, ↓reduceIte]

/-- The components of an `X`-stabilization correspond to those of the original diagram: the
component of an old column goes to the component of its embedded column, and the new column lies
on the component of the split column. The new column is spliced into the cycle of the old
component permutation through the split column (`Equiv.Perm.orbitQuotientEquivSplice`). -/
noncomputable def componentsStabilizeXEquiv :
    G.Components ≃ (G.stabilizeX newColumn newRow splitColumn).Components :=
  (Perm.orbitQuotientEquivSplice G.componentPerm _ newColumn.succAbove newColumn
      (G.componentPerm.symm splitColumn) Fin.succAbove_right_injective newColumn.succAbove_ne
      (fun _ hy ↦ Fin.exists_succAbove_eq hy)
      (G.semiconj_componentPerm_stabilizeX_mul_swap newColumn newRow splitColumn)).trans
    (Quotient.congrRight fun _ _ ↦ by rw [mul_assoc, swap_mul_self, mul_one])

/-- The component equivalence of an `X`-stabilization sends the component of an old column to the
component of its embedded column. -/
@[simp]
theorem componentsStabilizeXEquiv_componentOfColumn (c : Fin n) :
    G.componentsStabilizeXEquiv newColumn newRow splitColumn (G.componentOfColumn c) =
      (G.stabilizeX newColumn newRow splitColumn).componentOfColumn (newColumn.succAbove c) := by
  rw [componentOfColumn_def, componentOfColumn_def, componentsStabilizeXEquiv, Equiv.trans_apply,
    Perm.orbitQuotientEquivSplice_mk]
  -- `Quotient.congrRight` acts on representatives by the identity.
  rfl

/-- The inverse component equivalence of an `X`-stabilization sends the component of an embedded
column back to the component of the old column. -/
@[simp]
theorem componentsStabilizeXEquiv_symm_componentOfColumn_succAbove (c : Fin n) :
    (G.componentsStabilizeXEquiv newColumn newRow splitColumn).symm
        ((G.stabilizeX newColumn newRow splitColumn).componentOfColumn (newColumn.succAbove c)) =
      G.componentOfColumn c := by
  rw [Equiv.symm_apply_eq, componentsStabilizeXEquiv_componentOfColumn]

/-- The inverse component equivalence of an `X`-stabilization sends the component of the new
column to the component of the split column. -/
@[simp]
theorem componentsStabilizeXEquiv_symm_componentOfColumn_newColumn :
    (G.componentsStabilizeXEquiv newColumn newRow splitColumn).symm
        ((G.stabilizeX newColumn newRow splitColumn).componentOfColumn newColumn) =
      G.componentOfColumn splitColumn := by
  rw [Equiv.symm_apply_eq, componentsStabilizeXEquiv_componentOfColumn, componentOfColumn_eq_iff]
  exact G.sameCycle_componentPerm_stabilizeX_newColumn newColumn newRow splitColumn

/-- An `X`-stabilization does not change the number of link components: the new column is spliced
into the component through the split marking. -/
@[simp]
theorem componentCount_stabilizeX :
    (G.stabilizeX newColumn newRow splitColumn).componentCount = G.componentCount := by
  rw [← natCard_components, ← natCard_components]
  exact (Nat.card_congr (G.componentsStabilizeXEquiv newColumn newRow splitColumn)).symm

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
