/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.CyclicInterval
import TauCeti.KnotTheory.Grid.Commutation
import TauCeti.KnotTheory.Grid.Rotation

/-!
# Rotation and grid commutation arcs

This file records how the row and column arcs used in grid commutation hypotheses transform
under the half-turn rotation of a grid diagram. The commutation API in
`TauCeti.KnotTheory.Grid.Commutation` defines the oriented vertical and horizontal arcs from the
`O` marking to the `X` marking. Since `Fin.rev` reverses the cyclic order, rotating a diagram
sends these arcs to the reversed images of the corresponding arcs in the marking-swapped diagram.

## Main results

* `TauCeti.GridDiagram.OColumnOfRow_rotate` and
  `TauCeti.GridDiagram.XColumnOfRow_rotate`: row-to-column lookups commute with rotation up to
  `Fin.rev`.
* `TauCeti.GridDiagram.OColumnOfRow_swapMarkings` and
  `TauCeti.GridDiagram.XColumnOfRow_swapMarkings`: row-to-column lookups are exchanged by the
  marking swap.
* `TauCeti.GridDiagram.columnArc_rotate` and `TauCeti.GridDiagram.rowArc_rotate`: the oriented
  commutation arcs of the rotated diagram are the `Fin.rev`-images of the opposite oriented arcs
  of the original diagram.
* `TauCeti.GridDiagram.mem_columnArc_rotate` and `TauCeti.GridDiagram.mem_rowArc_rotate`: pointwise
  membership forms of those image formulas.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.5, "Invariance over 𝔽₂. Grid moves = commutation + (de)stabilization", where commutation maps
are built from the row and column marking arcs. The orientation convention follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- In the rotated diagram, the `O` marking in row `r` lies in the reversed column of the
original `O` marking in row `r.rev`. -/
@[simp]
theorem OColumnOfRow_rotate (r : Fin n) :
    OColumnOfRow G.rotate r = (OColumnOfRow G r.rev).rev := by
  apply G.rotate.O.toPerm.injective
  rw [OColumnOfRow_apply]
  simp [GridState.rotate_apply, Fin.rev_rev]

/-- In the rotated diagram, the `X` marking in row `r` lies in the reversed column of the
original `X` marking in row `r.rev`. -/
@[simp]
theorem XColumnOfRow_rotate (r : Fin n) :
    XColumnOfRow G.rotate r = (XColumnOfRow G r.rev).rev := by
  apply G.rotate.X.toPerm.injective
  rw [XColumnOfRow_apply]
  simp [GridState.rotate_apply, Fin.rev_rev]

/-- Swapping the `O` and `X` markings turns the `O` row-to-column lookup into the original
`X` row-to-column lookup. -/
@[simp]
theorem OColumnOfRow_swapMarkings (r : Fin n) :
    OColumnOfRow G.swapMarkings r = XColumnOfRow G r :=
  rfl

/-- Swapping the `O` and `X` markings turns the `X` row-to-column lookup into the original
`O` row-to-column lookup. -/
@[simp]
theorem XColumnOfRow_swapMarkings (r : Fin n) :
    XColumnOfRow G.swapMarkings r = OColumnOfRow G r :=
  rfl

/-- The column arc of the rotated diagram is the coordinate reversal of the opposite oriented
column arc in the original diagram. The `swapMarkings` appears because `Fin.rev` reverses the
cyclic orientation. -/
theorem columnArc_rotate (c : Fin n) :
    columnArc G.rotate c = (columnArc G.swapMarkings c.rev).image Fin.rev := by
  simp [columnArc, Grid.cIoo_image_rev]

/-- Membership in a rotated column arc is membership of the reversed row in the opposite oriented
column arc of the original diagram. -/
@[simp]
theorem mem_columnArc_rotate (c r : Fin n) :
    r ∈ columnArc G.rotate c ↔ r.rev ∈ columnArc G.swapMarkings c.rev := by
  rw [columnArc_rotate, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hsr⟩
    rwa [← hsr, Fin.rev_rev]
  · intro hr
    exact ⟨r.rev, hr, Fin.rev_rev r⟩

/-- The row arc of the rotated diagram is the coordinate reversal of the opposite oriented row
arc in the original diagram. The `swapMarkings` appears because `Fin.rev` reverses the cyclic
orientation. -/
theorem rowArc_rotate (r : Fin n) :
    rowArc G.rotate r = (rowArc G.swapMarkings r.rev).image Fin.rev := by
  simp [rowArc, Grid.cIoo_image_rev]

/-- Membership in a rotated row arc is membership of the reversed column in the opposite oriented
row arc of the original diagram. -/
@[simp]
theorem mem_rowArc_rotate (r c : Fin n) :
    c ∈ rowArc G.rotate r ↔ c.rev ∈ rowArc G.swapMarkings r.rev := by
  rw [rowArc_rotate, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hsc⟩
    rwa [← hsc, Fin.rev_rev]
  · intro hc
    exact ⟨c.rev, hc, Fin.rev_rev c⟩

end GridDiagram

end TauCeti
