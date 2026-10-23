/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Components
public import TauCeti.KnotTheory.Grid.Move.Basic
public import TauCeti.KnotTheory.Grid.Stabilization.Components
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

/-!
# The number of components of a grid link

Cyclic permutations of the rows or columns, commutations and stabilizations all preserve the
number of components of the link a grid diagram represents. The number of components is therefore
an invariant of grid links, `GridLink.componentCount`, and so is the property of being a knot,
`GridLink.IsKnot`. The diagrams presenting a knot in this sense are exactly the knot grid
diagrams, on which invariants such as `τ` are defined.

As a first application, the `4 × 4` grid of the Hopf link and the standard unknot grids present
different grid links: no sequence of grid moves connects them.

## Main definitions

* `TauCeti.GridLink.componentCount`: the number of components of a grid link.
* `TauCeti.GridLink.IsKnot`: a grid link is a knot when it has exactly one component.

## Main results

* `TauCeti.GridDiagram.MovesTo.componentCount_eq` and `TauCeti.GridDiagram.MovesTo.isKnot_iff`:
  grid moves preserve the number of components and whether a diagram represents a knot.
* `TauCeti.GridLink.isKnot_toGridLink`: the grid link of a diagram is a knot exactly when the
  diagram represents a knot.
* `TauCeti.GridLink.toGridLink_torusLink_one_one_ne_toGridLink_unknot`: the Hopf link grid and
  the unknot grids present different grid links.

## References

The grid moves follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridLink

/-- The number of components of a grid link, read off any grid diagram presenting it. -/
def componentCount : GridLink → ℕ :=
  lift (fun _ G ↦ G.componentCount)
    (fun G ↦ (G.componentCount_relabelRows _).symm)
    (fun G ↦ (G.componentCount_relabelColumns _).symm)
    (fun h ↦ h.componentCount_eq.symm)
    (fun h ↦ h.componentCount_eq.symm)

/-- The number of components of the grid link of a diagram is that of the diagram. -/
@[simp]
theorem componentCount_toGridLink {n : ℕ} (G : GridDiagram n) :
    G.toGridLink.componentCount = G.componentCount :=
  -- The invariance proofs are passed again: unification does not assign proof arguments.
  lift_toGridLink _ (fun G ↦ (G.componentCount_relabelRows _).symm)
    (fun G ↦ (G.componentCount_relabelColumns _).symm) (fun h ↦ h.componentCount_eq.symm)
    (fun h ↦ h.componentCount_eq.symm) G

/-- A grid link is a knot when it has exactly one component. -/
def IsKnot (L : GridLink) : Prop :=
  L.componentCount = 1

/-- A grid link is a knot exactly when it has one component. -/
theorem isKnot_def (L : GridLink) : L.IsKnot ↔ L.componentCount = 1 :=
  Iff.rfl

/-- The grid link of a diagram is a knot exactly when the diagram represents a knot. -/
@[simp]
theorem isKnot_toGridLink {n : ℕ} (G : GridDiagram n) : G.toGridLink.IsKnot ↔ G.IsKnot := by
  rw [isKnot_def, componentCount_toGridLink, GridDiagram.isKnot_def]

end GridLink

namespace GridDiagram

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}

/-- Grid moves preserve the number of represented link components. -/
theorem MovesTo.componentCount_eq (h : MovesTo G G') : G'.componentCount = G.componentCount := by
  rw [← GridLink.componentCount_toGridLink, ← GridLink.componentCount_toGridLink,
    (G.toGridLink_eq_iff_movesTo).mpr h]

/-- Grid moves preserve whether a grid diagram represents a knot. -/
theorem MovesTo.isKnot_iff (h : MovesTo G G') : G'.IsKnot ↔ G.IsKnot := by
  rw [isKnot_def, h.componentCount_eq, isKnot_def]

end GridDiagram

namespace GridLink

/-- The `4 × 4` grid of the Hopf link and the standard unknot grid of any size present different
grid links: the Hopf link has two components. -/
theorem toGridLink_torusLink_one_one_ne_toGridLink_unknot (n : ℕ) :
    (GridDiagram.torusLink 1 1).toGridLink ≠ (GridDiagram.unknot n).toGridLink := by
  intro h
  have hcount := congrArg componentCount h
  rw [componentCount_toGridLink, componentCount_toGridLink,
    GridDiagram.componentCount_torusLink_one_one,
    (GridDiagram.isKnot_def _).mp (GridDiagram.isKnot_unknot n)] at hcount
  omega

end GridLink

end TauCeti
