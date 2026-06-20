/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.GradingInteger

/-!
# The diagonal reflection of grid states and diagrams

This file adds the diagonal-reflection symmetry to the grid-combinatorial lane of the Heegaard
Floer roadmap. Reflecting an `n × n` grid across its main diagonal swaps the roles of rows and
columns: a grid state with permutation graph `σ` becomes the state with graph `σ⁻¹`, and a grid
diagram is reflected markwise. This is the elementary grid symmetry that sits alongside the row
and column relabelings already in `TauCeti.KnotTheory.Grid.Diagram`.

The geometric content is that the reflection `Prod.swap` of the plane fixes the
strict-southwest relation used by the grid `J`-function, since it acts symmetrically on the two
coordinates. Consequently every count built from that relation -- the ordered southwest count
`I`, the symmetrized `J`-function, and the Maslov and Alexander gradings -- is unchanged when a
grid state and grid diagram are reflected together.

## Main definitions

* `TauCeti.GridState.transpose`: the diagonal reflection of a grid state, with the inverse
  permutation graph.
* `TauCeti.GridDiagram.transpose`: the diagonal reflection of a grid diagram, reflecting both
  marking states.

## Main results

* `TauCeti.GridPoint.I_image_prodSwap`, `TauCeti.GridPoint.J_image_prodSwap`,
  `TauCeti.GridPoint.JDiff_image_prodSwap`: the southwest counts and the `J`-function are
  invariant under reflecting both point sets across the diagonal.
* `TauCeti.GridDiagram.maslovO_transpose`, `TauCeti.GridDiagram.maslovX_transpose`,
  `TauCeti.GridDiagram.alexander_transpose`: the Maslov and Alexander gradings are invariant
  under the diagonal reflection, with integer-valued counterparts
  `TauCeti.GridDiagram.maslovOℤ_transpose`, `TauCeti.GridDiagram.maslovXℤ_transpose`, and
  `TauCeti.GridDiagram.alexanderTwoℤ_transpose`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8,
"Symmetries and the genus bound", which calls for the symmetries of grid homology; the diagonal
reflection is the elementary one, and the gradings respecting it is the first symmetry fact. It
also extends the grid-state and grid-diagram symmetry API of Lane G.1 and the grading API of
Lane G.2. The diagonal symmetry of a grid diagram follows Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- The strict southwest relation is invariant under reflecting both points across the diagonal:
exchanging the column and row coordinates of both endpoints exchanges the two strict
inequalities. -/
theorem isSouthWest_prodSwap (p q : Fin n × Fin n) :
    IsSouthWest (Prod.swap p) (Prod.swap q) ↔ IsSouthWest p q := by
  unfold IsSouthWest
  exact and_comm

/-- The reflection map on pairs of grid squares is injective. -/
private theorem prodMap_swap_injective :
    Function.Injective
      (Prod.map (Prod.swap (α := Fin n) (β := Fin n)) (Prod.swap (α := Fin n) (β := Fin n))) :=
  Prod.swap_injective.prodMap Prod.swap_injective

/-- The ordered southwest count is invariant under reflecting both point sets across the
diagonal. -/
theorem I_image_prodSwap (s t : Finset (Fin n × Fin n)) :
    I (s.image Prod.swap) (t.image Prod.swap) = I s t := by
  rw [I_def, I_def, ← Finset.prodMap_image_product Prod.swap Prod.swap s t,
    Finset.filter_image, Finset.card_image_of_injective _ prodMap_swap_injective]
  congr 1
  exact Finset.filter_congr fun pq _ => isSouthWest_prodSwap pq.1 pq.2

/-- The numerator of the `J`-function is invariant under reflecting both point sets across the
diagonal. -/
theorem JNum_image_prodSwap (s t : Finset (Fin n × Fin n)) :
    JNum (s.image Prod.swap) (t.image Prod.swap) = JNum s t := by
  rw [JNum_def, JNum_def, I_image_prodSwap, I_image_prodSwap]

/-- The symmetrized grid `J`-function is invariant under reflecting both point sets across the
diagonal. -/
theorem J_image_prodSwap (s t : Finset (Fin n × Fin n)) :
    GridPoint.J (s.image Prod.swap) (t.image Prod.swap) = GridPoint.J s t := by
  rw [J_def, J_def, JNum_image_prodSwap]

/-- The bilinear `J`-function on formal differences is invariant under reflecting all four point
sets across the diagonal. -/
theorem JDiff_image_prodSwap (s a t b : Finset (Fin n × Fin n)) :
    JDiff (s.image Prod.swap) (a.image Prod.swap) (t.image Prod.swap) (b.image Prod.swap)
      = JDiff s a t b := by
  rw [JDiff_def, JDiff_def, J_image_prodSwap, J_image_prodSwap, J_image_prodSwap,
    J_image_prodSwap]

end GridPoint

namespace GridState

variable {n : ℕ}

/-- The diagonal reflection of a grid state.

Reflecting the occupied squares across the main diagonal exchanges columns and rows, so the new
permutation graph is the inverse of the old one. -/
def transpose (x : GridState n) : GridState n where
  toPerm := x.toPerm.symm

/-- The diagonal reflection evaluates by the inverse permutation graph. -/
@[simp]
theorem transpose_apply (x : GridState n) (c : Fin n) : x.transpose c = x.toPerm.symm c :=
  rfl

/-- The diagonal reflection is an involution on grid states. -/
@[simp]
theorem transpose_transpose (x : GridState n) : x.transpose.transpose = x := by
  cases x
  simp [transpose]

/-- A square lies in the reflected state exactly when its diagonal reflection lies in the
original state. -/
@[simp]
theorem mem_transpose_pointSet (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.transpose.pointSet ↔ Prod.swap p ∈ x.pointSet := by
  simp only [mem_pointSet, transpose_apply]
  rw [Equiv.symm_apply_eq, eq_comm]
  rfl

/-- The point set of the reflected state is the diagonal reflection of the original point set. -/
theorem transpose_pointSet (x : GridState n) :
    x.transpose.pointSet = x.pointSet.image Prod.swap := by
  ext p
  rw [mem_transpose_pointSet, Finset.mem_image]
  constructor
  · intro hp
    exact ⟨Prod.swap p, hp, Prod.swap_swap p⟩
  · rintro ⟨q, hq, rfl⟩
    rwa [Prod.swap_swap]

/-- The state-level grid `J`-function is invariant under reflecting both states. -/
theorem J_transpose (x y : GridState n) :
    GridState.J x.transpose y.transpose = GridState.J x y := by
  rw [J_def, J_def, transpose_pointSet, transpose_pointSet, GridPoint.J_image_prodSwap]

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The diagonal reflection of a grid diagram, reflecting both the `O` and `X` marking states.

Reflection across the main diagonal is a bijection of squares, so it preserves the condition
that no square carries both markings. -/
def transpose (G : GridDiagram n) : GridDiagram n where
  O := G.O.transpose
  X := G.X.transpose
  disjoint := by
    intro c h
    have h' : G.O.toPerm.symm c = G.X.toPerm.symm c := h
    refine G.disjoint (G.O.toPerm.symm c) ?_
    rw [Equiv.apply_symm_apply, h', Equiv.apply_symm_apply]

/-- The `O` marking state of the reflected diagram is the reflected `O` marking state. -/
@[simp]
theorem transpose_O : G.transpose.O = G.O.transpose :=
  rfl

/-- The `X` marking state of the reflected diagram is the reflected `X` marking state. -/
@[simp]
theorem transpose_X : G.transpose.X = G.X.transpose :=
  rfl

/-- The diagonal reflection is an involution on grid diagrams. -/
@[simp]
theorem transpose_transpose : G.transpose.transpose = G := by
  ext c <;> simp

/-- The `O`-marking set of the reflected diagram is the diagonal reflection of the original
`O`-marking set. -/
theorem transpose_OSet : G.transpose.OSet = G.OSet.image Prod.swap := by
  rw [OSet, OSet, transpose_O, GridState.transpose_pointSet]

/-- The `X`-marking set of the reflected diagram is the diagonal reflection of the original
`X`-marking set. -/
theorem transpose_XSet : G.transpose.XSet = G.XSet.image Prod.swap := by
  rw [XSet, XSet, transpose_X, GridState.transpose_pointSet]

/-- The `O`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovO_transpose (x : GridState n) :
    G.transpose.maslovO x.transpose = G.maslovO x := by
  rw [maslovO_def, maslovO_def, GridState.transpose_pointSet, transpose_OSet,
    GridPoint.JDiff_image_prodSwap]

/-- The `X`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovX_transpose (x : GridState n) :
    G.transpose.maslovX x.transpose = G.maslovX x := by
  rw [maslovX_def, maslovX_def, GridState.transpose_pointSet, transpose_XSet,
    GridPoint.JDiff_image_prodSwap]

/-- The Alexander grading is invariant under the diagonal reflection. The normalization shift
depends only on the common grid size, so it cancels between the two diagrams. -/
theorem alexander_transpose (x : GridState n) :
    G.transpose.alexander x.transpose = G.alexander x := by
  rw [alexander_def, alexander_def, maslovO_transpose, maslovX_transpose]

/-- The integer-valued `O`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovOℤ_transpose (x : GridState n) :
    G.transpose.maslovOℤ x.transpose = G.maslovOℤ x := by
  rw [maslovOℤ_def, maslovOℤ_def, GridState.transpose_pointSet, transpose_OSet,
    GridPoint.I_image_prodSwap, GridPoint.JNum_image_prodSwap, GridPoint.I_image_prodSwap]

/-- The integer-valued `X`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovXℤ_transpose (x : GridState n) :
    G.transpose.maslovXℤ x.transpose = G.maslovXℤ x := by
  rw [maslovXℤ_def, maslovXℤ_def, GridState.transpose_pointSet, transpose_XSet,
    GridPoint.I_image_prodSwap, GridPoint.JNum_image_prodSwap, GridPoint.I_image_prodSwap]

/-- The integer numerator of twice the Alexander grading is invariant under the diagonal
reflection. -/
theorem alexanderTwoℤ_transpose (x : GridState n) :
    G.transpose.alexanderTwoℤ x.transpose = G.alexanderTwoℤ x := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_transpose, maslovXℤ_transpose]

end GridDiagram

end TauCeti
