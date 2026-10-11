/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Cross.Sum

/-!
# Geometric characterization of terminal cross-overlap partners

The terminal cross-overlap partners are counted pentagon--rectangle domains in which the
rectangle ends where the pentagon starts, the rectangle's bottom row lies strictly inside the
pentagon's rows, and the turn row lies below that bottom row. This characterization does not
require finding a source domain. It supplies the terminal cross-overlap part of the partition
of pentagon--rectangle contributions to the commutation chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
-/

public section

namespace TauCeti.GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The generic recut splits the pentagon's rows at the rectangle's bottom row. -/
private theorem crossRecut_geometry (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hf : E.toRectangleDecomposition.first.IsEmpty)
    (hs : E.toRectangleDecomposition.second.IsEmpty)
    (hrow : E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top) :
    let D := E.toRectangleDecomposition.recut hone hf hs
    D.first.right = finRotate n a ∧ D.second.right = finRotate n a ∧
      D.first.bottom = E.rectangle.bottom ∧ D.first.top = E.pentagon.top ∧
        D.second.bottom = E.pentagon.bottom ∧ D.second.top = E.rectangle.bottom := by
  intro D
  have hdata := E.toRectangleDecomposition.isRecutOfLeftEqRight_recut
    (by simpa using hcommon.symm) hone hf hs
  have hfb : E.toRectangleDecomposition.first.bottom = E.pentagon.bottom := by
    simp [GridRectangleBetween.bottom_def]
  have hft : E.toRectangleDecomposition.first.top = E.pentagon.top := by
    simp [GridRectangleBetween.top_def]
  have hsb : E.toRectangleDecomposition.second.bottom = E.rectangle.bottom := by
    simp [GridRectangleBetween.bottom_def]
  obtain ⟨hDfb, hDsb⟩ := hdata.recut_sides
  rw [hsb] at hDfb
  rw [hfb] at hDsb
  have hb : x (finRotate n a) = E.pentagon.top := by
    rw [GridRectangleBetween.top_def, E.pentagon.right_eq]
  rcases hdata.recut_branch with ⟨hrow', -⟩ | ⟨-, hm, hDft, hDst⟩
  · rw [hfb, hsb, hft] at hrow'
    exact False.elim (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap E.pentagon.bottom E.pentagon.top) hrow
      (Grid.mem_cIoo_cyclic_right hrow'))
  · rw [hsb, hft] at hm
    rw [hft] at hDft
    rw [hsb] at hDst
    have hfirstRight : D.first.right = finRotate n a :=
      x.toPerm.injective ((GridRectangleBetween.top_def _).symm.trans (hDft.trans hb.symm))
    have hsecondRight : D.second.right = finRotate n a := by
      apply x.toPerm.injective
      have htop : x.swapRows E.rectangle.bottom E.pentagon.top D.second.right =
          E.rectangle.bottom :=
        (congrArg (fun y : GridState n => y D.second.right) hm).symm.trans
          ((GridRectangleBetween.top_def _).symm.trans hDst)
      rw [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at htop
      exact htop.trans hb.symm
    exact ⟨hfirstRight, hsecondRight, hDfb, hDft, hDsb, hDst⟩

/- The inverse promotion follows the formal recut argument in
`TauCeti.KnotTheory.Grid.Commutation.Overlap.PentagonTerminal.Mixed`, with the turn row in
the complementary interval. -/

/-- Promote the second recut piece, which contains the turn row. -/
private noncomputable def crossRecut (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hf : E.toRectangleDecomposition.first.IsEmpty)
    (hs : E.toRectangleDecomposition.second.IsEmpty)
    (hrow : E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top)
    (hturn : s ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    GridRectanglePentagonDecomposition a s x z where
  middle := (E.toRectangleDecomposition.recut hone hf hs).middle
  rectangle := (E.toRectangleDecomposition.recut hone hf hs).first
  pentagon := GridPentagonBetween.ofRightEq
    (E.toRectangleDecomposition.recut hone hf hs).second
    (E.crossRecut_geometry hcommon hone hf hs hrow).2.1
    (by rwa [(E.crossRecut_geometry hcommon hone hf hs hrow).2.2.2.2.1,
      (E.crossRecut_geometry hcommon hone hf hs hrow).2.2.2.2.2])

private theorem crossRecut_toRectangleDecomposition
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hf : E.toRectangleDecomposition.first.IsEmpty)
    (hs : E.toRectangleDecomposition.second.IsEmpty)
    (hrow : E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top)
    (hturn : s ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    (E.crossRecut hcommon hone hf hs hrow hturn).toRectangleDecomposition =
      E.toRectangleDecomposition.recut hone hf hs := by
  apply GridRectangleDecomposition.ext <;>
    simp [crossRecut, (E.crossRecut_geometry hcommon hone hf hs hrow).2.1]

/-- The inverse cross-recut shares its terminal side, with the pentagon starting inside the
rectangle's column interval. -/
private theorem crossRecut_terminal_overlap
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hf : E.toRectangleDecomposition.first.IsEmpty)
    (hs : E.toRectangleDecomposition.second.IsEmpty)
    (hrow : E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top)
    (hturn : s ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    let D := E.crossRecut hcommon hone hf hs hrow hturn
    D.rectangle.right = D.pentagon.right ∧
      D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right := by
  intro D
  have hDrect := E.crossRecut_toRectangleDecomposition hcommon hone hf hs hrow hturn
  have hrecut : E.toRectangleDecomposition.IsRecut D.toRectangleDecomposition := by
    rw [hDrect]
    exact E.toRectangleDecomposition.isRecut_recut hone hf hs
  have hback := hrecut.symm hone hf hs
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  obtain ⟨hfr, hsr, -, -, -, -⟩ := E.crossRecut_geometry hcommon hone hf hs hrow
  rw [← hDrect] at hfr hsr
  have hDcommon : D.rectangle.right = D.pentagon.right := by
    simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right] using
      hfr.trans hsr.symm
  refine ⟨hDcommon, ?_⟩
  rcases hback.orientation with h | h | h | h
  · refine absurd ?_ (D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hDone)
    rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, h.side_eq, hfr, hsr]
  · rcases h.recut_branch with ⟨-, -, hright, -⟩ | ⟨hcol, -⟩
    · rw [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
        E.pentagon.right_eq] at hright
      exact absurd (hright.symm.trans hfr.symm)
        D.toRectangleDecomposition.first.left_ne_right
    · simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right, hDcommon]
        using hcol
  · exact (D.toRectangleDecomposition.first.left_ne_right
      ((h.side_eq.trans hsr).trans hfr.symm)).elim
  · exact (D.toRectangleDecomposition.second.left_ne_right
      ((h.side_eq.symm.trans hfr).trans hsr.symm)).elim

end TauCeti.GridPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- The inverse cross-recut of a counted partner is counted in the original diagram. -/
private theorem crossRecut_mem_rectanglePentagonDecompositions
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hf : E.toRectangleDecomposition.first.IsEmpty)
    (hs : E.toRectangleDecomposition.second.IsEmpty)
    (hrow : E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top)
    (hturn : C.turnRow ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    let D := E.crossRecut hcommon hone hf hs hrow hturn
    D.rectangle.right = D.pentagon.right →
      D.toRectangleDecomposition.HasOneCommonSide →
        D.rectangle.IsEmpty → D.pentagon.IsEmpty →
          D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition →
            D ∈ G.rectanglePentagonDecompositions C x z := by
  intro D hDcommon hDone hr hp hback
  have hDrect := E.crossRecut_toRectangleDecomposition hcommon hone hf hs hrow hturn
  -- The first promotion of the inverse domain is `E`; check its corrected square multiset.
  obtain ⟨hfirst, hpromote⟩ :=
    D.exists_recutRightEqRightFirst_eq_of_isRecut E hDcommon hDone hr hp hback
  obtain ⟨-, -, -, -, hcols, ha, -⟩ :=
    D.recutRightEqRightFirst_rectangle_geometry hDcommon hDone hr hp hfirst
  rw [hpromote] at hcols ha
  have hb : finRotate n C.column ∉ E.rectangle.toGridRectangle.coveredColumns := fun hb =>
    Grid.right_notMem_cIco D.rectangle.left (finRotate n C.column) (by
      simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, hDcommon, D.pentagon.right_eq] using hcols hb)
  have hbottom : D.pentagon.bottom = E.pentagon.bottom := by
    have h := (E.crossRecut_geometry hcommon hone hf hs hrow).2.2.2.2.1
    rw [← hDrect] at h
    simpa only [GridRectangleBetween.bottom_def,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_middle,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] using h
  have hcovered := D.coveredSquares_val_add_val_eq_of_isRepartition E hback.isRepartition
    (fun t => by
      simp only [GridRectangle.mem_coveredSquares, ha, hb, hbottom, false_and, ↓reduceIte])
  -- Read the composite domain in the original diagram, including the column swap on `E`.
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles,
    ← G.disjoint_map_swapColumns_XSet_iff] at hE
  rw [mem_rectanglePentagonDecompositions, mem_unblockedRectangles, mem_pentagons]
  have hX (p : Fin n × Fin n)
      (hp : p ∈ D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
      p ∉ G.XSet := by
    rw [← hcovered] at hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · exact Finset.disjoint_left.mp hE.1.2 hp
    · exact Finset.disjoint_left.mp hE.2.2 hp
  exact ⟨⟨hr, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inl hp))⟩,
    hp, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inr hp))⟩

/-- A counted mixed overlap with the turn row below the rectangle's bottom row is the recut of
 a counted terminal cross-overlap source. -/
theorem mem_terminalCrossOverlapPartners_of_right_eq_left
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hrow : E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top)
    (hturn : C.turnRow ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    E ∈ G.terminalCrossOverlapPartners C x z := by
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
  have hf := E.underlying_first_isEmpty ((G.mem_pentagons _).1 hP).1
  have hs := E.underlying_second_isEmpty
    (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1
  have hother : E.rectangle.left ≠ E.pentagon.right := by
    intro h
    have hb : E.rectangle.bottom = E.pentagon.bottom := by
      rw [GridRectangleBetween.bottom_def, h, E.pentagon.map_right,
        GridRectangleBetween.bottom_def]
    exact Grid.ne_left_of_mem_cIoo hrow hb
  have hone := E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_right
    (by simpa using hcommon.symm) (by simpa using hother.symm)
  -- Recut the empty domain and use its returning orientation to fix the column order.
  set D := E.crossRecut hcommon hone hf hs hrow hturn
  have hDrect := E.crossRecut_toRectangleDecomposition hcommon hone hf hs hrow hturn
  have hrecut : E.toRectangleDecomposition.IsRecut D.toRectangleDecomposition := by
    rw [hDrect]
    exact E.toRectangleDecomposition.isRecut_recut hone hf hs
  have hback := hrecut.symm hone hf hs
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  obtain ⟨hDcommon, hDcol⟩ := E.crossRecut_terminal_overlap hcommon hone hf hs hrow hturn
  have hr := D.isEmpty_rectangle_of_isRecut hrecut
  have hp := D.isEmpty_pentagon_of_isRecut hrecut
  have hcounted := G.crossRecut_mem_rectanglePentagonDecompositions C E hE
    hcommon hone hf hs hrow hturn hDcommon hDone hr hp hback
  exact (G.mem_terminalCrossOverlapPartners C E).2 ⟨D,
    (G.mem_terminalCrossOverlapSources C D).2 ⟨hcounted, hDcommon, hDcol⟩, hback⟩

/-- Reading a counted terminal cross-overlap recut gives its sides and row order. -/
private theorem terminalCrossOverlapPartner_sides
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.terminalCrossOverlapPartners C x z) :
    E.rectangle.right = E.pentagon.left ∧
      E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top ∧
        C.turnRow ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom := by
  obtain ⟨D, hD, hrecut⟩ := (G.mem_terminalCrossOverlapPartners C E).1 hE
  obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_terminalCrossOverlapSources C D).1 hD
  obtain ⟨hR, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcounted
  have hr := ((G.mem_unblockedRectangles _).1 hR).1
  have hp := ((G.mem_pentagons _).1 hP).1
  have hone := D.hasOneCommonSide_of_right_eq_right hcommon (Grid.ne_left_of_mem_cIoo hcol).symm
  have hf : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hr
  have hs : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle] using hp
  obtain ⟨hfirst, hpromote⟩ :=
    D.exists_recutRightEqRightFirst_eq_of_isRecut E hcommon hone hr hp hrecut
  obtain ⟨-, hright, hb, -, -, -, -⟩ :=
    D.recutRightEqRightFirst_rectangle_geometry hcommon hone hr hp hfirst
  rw [hpromote] at hright hb
  obtain ⟨-, -, hleft⟩ :=
    D.first_recut_branch_data_of_right_eq_right hcommon hone hr hp hfirst
  have hPleft : E.pentagon.left = D.pentagon.left := by
    rw [← hpromote, D.recutRightEqRightFirst_pentagon_left]
    simpa using hleft
  have hPbottom : E.pentagon.bottom = D.pentagon.bottom := by
    rw [← hpromote, D.recutRightEqRightFirst_pentagon_bottom,
      GridRectangleBetween.bottom_def, hleft,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
      GridRectangleBetween.bottom_def]
    exact (D.rectangle.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol)
      (hcommon ▸ D.pentagon.left_ne_right)).symm
  have hPtop : E.pentagon.top = D.rectangle.top := by
    rw [GridRectangleBetween.top_def, E.pentagon.right_eq,
      ← D.pentagon.right_eq, ← hcommon, GridRectangleBetween.top_def]
  have hrow := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_right_eq_right
    (by simpa using hcommon) (by simpa using (Grid.ne_left_of_mem_cIoo hcol).symm) hf hs).2
  have hPtopD : D.pentagon.top = D.rectangle.bottom := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.rectangle.map_right,
      GridRectangleBetween.bottom_def]
  refine ⟨hright.trans hPleft.symm, ?_, ?_⟩
  · rw [hb, hPbottom, hPtop]
    simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_middle] using hrow
  · rw [hPbottom, hb, ← hPtopD]
    exact D.pentagon.turn_mem_cIco_bottom_top

/-- Terminal cross-overlap partners are exactly the counted mixed pentagon--rectangle domains
whose rectangle ends where the pentagon starts, whose rectangle's
bottom row lies inside the pentagon's rows, and whose turn row lies below that bottom row. -/
theorem mem_terminalCrossOverlapPartners_iff_sides
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.terminalCrossOverlapPartners C x z ↔
      E ∈ G.pentagonRectangleDecompositions C x z ∧
        E.rectangle.right = E.pentagon.left ∧
          E.rectangle.bottom ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top ∧
            C.turnRow ∈ Grid.cIco E.pentagon.bottom E.rectangle.bottom := by
  constructor
  · intro hE
    exact ⟨G.terminalCrossOverlapPartners_subset_pentagonRectangleDecompositions C hE,
      G.terminalCrossOverlapPartner_sides C E hE⟩
  · rintro ⟨hE, hcommon, hrow, hturn⟩
    exact G.mem_terminalCrossOverlapPartners_of_right_eq_left C E hE hcommon hrow hturn

end TauCeti.GridDiagram
