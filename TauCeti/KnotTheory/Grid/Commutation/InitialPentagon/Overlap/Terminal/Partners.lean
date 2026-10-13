/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Terminal.Basic

/-!
# Geometric characterization of initial-side terminal-overlap partners

The recuts of counted rectangle--initial-side-pentagon domains sharing their terminal side
are characterized by two mixed-side configurations. If the rectangle starts where the
pentagon ends, the pentagon's top row lies strictly inside the rectangle's row interval.
If the rectangle ends where the pentagon starts, its bottom row lies strictly inside the
pentagon's rows and the turn row lies below that bottom row.

The characterization recognizes partners directly from their sides and rows, without
searching for a source. It supplies one part of the partition of pentagon--rectangle terms
in the commutation chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The inverse promotion follows the existing formal arguments in
`InitialPentagon.Overlap.Mixed.RightLeft.Partners` and the recut geometry in
`Differential.Square.Recut.Pairing`.
-/

public section

namespace TauCeti.GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem terminalInverse_sides
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (D : GridRectangleDecomposition x z) {r t : Fin n}
    (hm : D.middle = x.swapRows r t)
    (hsb : D.second.bottom = E.first.bottom)
    (hst : D.second.top = r) (hft : D.first.top = t)
    (hne_r : E.first.bottom ≠ r) (hne_t : E.first.bottom ≠ t) :
    D.first.right = D.second.right ∧ D.second.left = E.first.left := by
  have hsecondLeft : D.second.left = E.first.left := by
    apply x.toPerm.injective
    have h := (congrArg (fun y : GridState n => y D.second.left) hm).symm.trans
      (D.second.bottom_def.symm.trans hsb)
    rw [GridState.swapRows_apply, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_of_ne_of_ne hne_r hne_t] at h
    exact h.trans E.first.bottom_def
  have hright : D.first.right = D.second.right := by
    apply x.toPerm.injective
    have h := (congrArg (fun y : GridState n => y D.second.right) hm).symm.trans
      (D.second.top_def.symm.trans hst)
    rw [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact (D.first.top_def.symm.trans hft).trans h.symm
  exact ⟨hright, hsecondLeft⟩

private theorem terminalInverse_rightLeft_geometry
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.left) (hone : E.HasOneCommonSide)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hrow : E.first.top ∈ Grid.cIoo E.first.bottom E.second.top) :
    let D := E.recut hone hf hs
    D.first.right = D.second.right ∧ D.second.left = finRotate n a ∧
      s ∈ Grid.cIco D.second.bottom D.second.top := by
  intro D
  have hdata := E.isRecutOfRightEqLeft_recut hcommon hone hf hs
  obtain ⟨hft, hst⟩ := hdata.recut_sides
  rcases hdata.recut_branch with ⟨-, hm, -, hsb⟩ | ⟨hrow', -⟩
  · obtain ⟨hright, hsecondLeft⟩ := E.terminalInverse_sides D hm hsb hst hft
      E.first.bottom_ne_top
      (Grid.ne_left_of_mem_cIoo (Grid.mem_cIoo_cyclic_right hrow))
    refine ⟨hright, hsecondLeft.trans E.first_left_eq, ?_⟩
    rw [hsb, hst]
    exact E.first_turn_mem
  · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap E.first.bottom E.first.top)
      hrow' (Grid.mem_cIoo_cyclic_left hrow)).elim

private theorem terminalInverse_leftRight_geometry
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.left = E.second.right) (hone : E.HasOneCommonSide)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hrow : E.second.bottom ∈ Grid.cIoo E.first.bottom E.first.top)
    (hturn : s ∈ Grid.cIco E.first.bottom E.second.bottom) :
    let D := E.recut hone hf hs
    D.first.right = D.second.right ∧ D.second.left = finRotate n a ∧
      s ∈ Grid.cIco D.second.bottom D.second.top := by
  intro D
  have hdata := E.isRecutOfLeftEqRight_recut hcommon hone hf hs
  obtain ⟨-, hsb⟩ := hdata.recut_sides
  rcases hdata.recut_branch with ⟨hrow', -⟩ | ⟨-, hm, hft, hst⟩
  · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap E.first.bottom E.first.top)
      hrow (Grid.mem_cIoo_cyclic_right hrow')).elim
  · obtain ⟨hright, hsecondLeft⟩ := E.terminalInverse_sides D hm hsb hst hft
      (Grid.ne_left_of_mem_cIoo hrow).symm E.first.bottom_ne_top
    exact ⟨hright, hsecondLeft.trans E.first_left_eq, by rwa [hsb, hst]⟩

end TauCeti.GridInitialPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

private theorem mem_terminalOverlapPartners_of_recut_geometry
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hone : E.HasOneCommonSide) (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hgeometry : let D := E.recut hone hf hs
      D.first.right = D.second.right ∧ D.second.left = finRotate n C.column ∧
        C.turnRow ∈ Grid.cIco D.second.bottom D.second.top) :
    E ∈ G.initialPentagonTerminalOverlapPartners C x z := by
  let D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z :=
    { toGridRectangleDecomposition := E.recut hone hf hs
      second_left_eq := hgeometry.2.1
      second_turn_mem := hgeometry.2.2 }
  -- The promotion adds only the side and turn-row proof fields to the generic recut.
  have hDrect : D.toGridRectangleDecomposition = E.recut hone hf hs := rfl
  have hrecut : E.IsRecut D.toGridRectangleDecomposition := by
    rw [hDrect]
    exact E.isRecut_recut hone hf hs
  have hback := hrecut.symm hone hf hs
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.target_ne_source_of_hasOneCommonSide hone)
  have hcommon : D.first.right = D.second.right := hgeometry.1
  have hEq : D.recutRightEqRight hcommon hDone hrecut.isEmpty_first hrecut.isEmpty_second = E := by
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.existsUnique_isRecut hDone hrecut.isEmpty_first hrecut.isEmpty_second).unique
      (D.isRecut_recutRightEqRight hcommon hDone hrecut.isEmpty_first hrecut.isEmpty_second) hback
  have hsquares := D.coveredSquares_val_add_val_recutRightEqRight hcommon hDone
    hrecut.isEmpty_first hrecut.isEmpty_second
  rw [hEq] at hsquares
  have hD := G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq_initialPentagonRectangle
    C hE hrecut.isEmpty_first hrecut.isEmpty_second hsquares.symm
  exact (G.mem_initialPentagonTerminalOverlapPartners C E).2
    ⟨D, (G.mem_initialPentagonTerminalOverlapSources C D).2 ⟨hD, hcommon, hDone⟩, hback⟩

/-- A counted initial-side-pentagon--rectangle term whose rectangle starts where the pentagon
ends, with the pentagon's top strictly inside the rectangle's rows, is a terminal-overlap
partner. -/
theorem mem_initialPentagonTerminalOverlapPartners_of_right_eq_left
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.right = E.second.left)
    (hrow : E.first.top ∈ Grid.cIoo E.first.bottom E.second.top) :
    E ∈ G.initialPentagonTerminalOverlapPartners C x z := by
  obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  have hother : E.first.left ≠ E.second.right := by
    intro h
    have ht : E.second.top = E.first.top := by
      rw [GridRectangleBetween.top_def, ← h, E.first.map_left, GridRectangleBetween.top_def]
    exact Grid.ne_right_of_mem_cIoo hrow ht.symm
  have hone := E.hasOneCommonSide_of_right_eq_left hcommon hother
  exact G.mem_terminalOverlapPartners_of_recut_geometry C E hE hone hf hs
    (E.terminalInverse_rightLeft_geometry hcommon hone hf hs hrow)

/-- A counted initial-side-pentagon--rectangle term whose rectangle ends where the pentagon
starts, with the rectangle's bottom inside the pentagon's rows and above the turn row, is a
terminal-overlap partner. -/
theorem mem_initialPentagonTerminalOverlapPartners_of_left_eq_right
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.left = E.second.right)
    (hrow : E.second.bottom ∈ Grid.cIoo E.first.bottom E.first.top)
    (hturn : C.turnRow ∈ Grid.cIco E.first.bottom E.second.bottom) :
    E ∈ G.initialPentagonTerminalOverlapPartners C x z := by
  obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  have hother : E.first.right ≠ E.second.left := by
    intro h
    have hb : E.second.bottom = E.first.bottom := by
      rw [GridRectangleBetween.bottom_def, ← h, E.first.map_right,
        GridRectangleBetween.bottom_def]
    exact Grid.ne_left_of_mem_cIoo hrow hb
  have hone := E.hasOneCommonSide_of_left_eq_right hcommon hother
  exact G.mem_terminalOverlapPartners_of_recut_geometry C E hE hone hf hs
    (E.terminalInverse_leftRight_geometry hcommon hone hf hs hrow hturn)

private theorem initialPentagonTerminalOverlapPartner_sides
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonTerminalOverlapPartners C x z) :
    (E.first.right = E.second.left ∧
        E.first.top ∈ Grid.cIoo E.first.bottom E.second.top) ∨
      (E.first.left = E.second.right ∧
        E.second.bottom ∈ Grid.cIoo E.first.bottom E.first.top ∧
          C.turnRow ∈ Grid.cIco E.first.bottom E.second.bottom) := by
  obtain ⟨D, hD, hrecut⟩ := (G.mem_initialPentagonTerminalOverlapPartners C E).1 hE
  obtain ⟨hcounted, hcommon, hone⟩ := (G.mem_initialPentagonTerminalOverlapSources C D).1 hD
  obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcounted
  have hf := G.isEmpty_of_mem_unblockedRectangles hR
  have hs : D.second.IsEmpty := by
    simpa only [D.pentagon_toGridRectangleBetween] using ((G.mem_initialPentagons _).1 hP).1
  have hcanonical : E.toGridRectangleDecomposition = D.recut hone hf hs :=
    (D.existsUnique_isRecut hone hf hs).unique hrecut (D.isRecut_recut hone hf hs)
  have hdata : D.IsRecutOfRightEqRight E.toGridRectangleDecomposition := by
    rw [hcanonical]
    exact D.isRecutOfRightEqRight_recut hcommon hone hf hs
  have hother : D.first.left ≠ D.second.left := by
    intro h
    apply D.sideColumns_ne_of_hasOneCommonSide hone
    rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, h, hcommon]
  have hrow := (D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hother hf hs).2
  have hsecondBottom : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def, D.first.target_apply,
      Equiv.swap_apply_of_ne_of_ne hother.symm (hcommon ▸ D.second.left_ne_right)]
  have hsecondTop : D.second.top = x D.first.left := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.first.map_right]
  obtain ⟨hfl, hsl⟩ := hdata.recut_sides
  have hbottom : E.first.bottom = D.second.bottom := by
    rw [GridRectangleBetween.bottom_def, hfl, hsecondBottom]
  rcases hdata.recut_branch with ⟨-, hm, hfr, hsr⟩ | ⟨-, hm, hfr, hsr⟩
  · -- The pentagon keeps its rows and ends at the rectangle's initial side.
    have htop : E.first.top = D.first.bottom := by
      rw [GridRectangleBetween.top_def, hfr, GridRectangleBetween.bottom_def]
    have hrectangleTop : E.second.top = D.first.top := by
      rw [GridRectangleBetween.top_def, hsr, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne (hcommon ▸ D.second.left_ne_right.symm)
          D.first.left_ne_right.symm, GridRectangleBetween.top_def]
    exact Or.inl ⟨hfr.trans hsl.symm, by simpa only [hbottom, htop, hrectangleTop] using hrow⟩
  · -- The pentagon extends upwards, and its original top becomes the rectangle's bottom.
    have htop : E.first.top = D.first.top := by
      rw [GridRectangleBetween.top_def, hfr, GridRectangleBetween.top_def]
    have hrectangleBottom : E.second.bottom = D.first.bottom := by
      rw [GridRectangleBetween.bottom_def, hsl, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hother D.first.left_ne_right,
        GridRectangleBetween.bottom_def]
    refine Or.inr ⟨hfl.trans hsr.symm, ?_, ?_⟩
    · simpa only [hbottom, htop, hrectangleBottom] using hrow
    · rw [hbottom, hrectangleBottom, D.first.bottom_def, ← hsecondTop]
      exact D.second_turn_mem

/-- Terminal-overlap partners of initial-side pentagons are exactly the counted mixed domains
with either the pentagon's top inside the rectangle's rows, or the rectangle's bottom inside
the pentagon's rows and above the turn row. No search for a recut source is required. -/
@[grind =]
theorem mem_initialPentagonTerminalOverlapPartners_iff_sides
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonTerminalOverlapPartners C x z ↔
      E ∈ G.initialPentagonRectangleDecompositions C x z ∧
        ((E.first.right = E.second.left ∧
            E.first.top ∈ Grid.cIoo E.first.bottom E.second.top) ∨
          (E.first.left = E.second.right ∧
            E.second.bottom ∈ Grid.cIoo E.first.bottom E.first.top ∧
              C.turnRow ∈ Grid.cIco E.first.bottom E.second.bottom)) := by
  constructor
  · intro hE
    exact ⟨G.initialPentagonTerminalOverlapPartners_subset C hE,
      G.initialPentagonTerminalOverlapPartner_sides C E hE⟩
  · rintro ⟨hE, ⟨hcommon, hrow⟩ | ⟨hcommon, hrow, hturn⟩⟩
    · exact G.mem_initialPentagonTerminalOverlapPartners_of_right_eq_left C E hE hcommon hrow
    · exact G.mem_initialPentagonTerminalOverlapPartners_of_left_eq_right C E hE hcommon hrow hturn

end TauCeti.GridDiagram
