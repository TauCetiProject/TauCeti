/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Mixed.RightLeft.Basic

/-!
# Geometric characterization of mixed `right = left` recut partners

The recuts of counted rectangle--pentagon domains whose rectangle ends where the pentagon
starts and whose turn row lies above the rectangle's top row have two possible shapes.
Their pentagon and rectangle share either their terminal side, with the pentagon starting
inside the rectangle's columns, or their initial side, with the rectangle ending inside
the pentagon's columns. This file characterizes the partner family by these sides alone.
It gives the mixed `right = left` case of the partition of pentagon--rectangle terms in
the commutation chain-map equation.

The inverse empty-rectangle recut promotes its second piece to a pentagon. The forward
corrected-square identity transports marking avoidance back to that inverse source.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The inverse-promotion argument follows the existing formalizations
in `Commutation.Overlap.Mixed.LeftRight.Partners` and
`Commutation.InitialPentagon.Overlap.Mixed.RightLeft.Partners`.
-/

public section

namespace TauCeti.GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem exists_rightLeftInverse_of_right_eq_right
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.pentagon.right = E.rectangle.right)
    (hcol : E.pentagon.left ∈ Grid.cIoo E.rectangle.left E.pentagon.right)
    (hp : E.pentagon.IsEmpty) (hr : E.rectangle.IsEmpty) :
    ∃ D : GridRectangleDecomposition x z,
      E.toRectangleDecomposition.IsRecut D ∧ D.first.right = D.second.left ∧
        D.second.right = finRotate n a ∧ s ∈ Grid.cIco D.second.bottom D.second.top ∧
          s ∈ Grid.cIco D.first.top D.second.top := by
  let F := E.toRectangleDecomposition
  have hc : F.first.right = F.second.right := by simpa [F] using hcommon
  have hcol' : F.first.left ∈ Grid.cIoo F.second.left F.first.right := by
    simpa [F] using hcol
  have hf := E.underlying_first_isEmpty hp
  have hs := E.underlying_second_isEmpty hr
  let hone := F.hasOneCommonSide_of_right_eq_right hc (Grid.ne_left_of_mem_cIoo hcol')
  let D := F.recut hone hf hs
  have hdata := F.isRecutOfRightEqRight_recut hc hone hf hs
  obtain ⟨hfr, hsl, -, hft, hsb, hst⟩ :=
    F.recut_geometry_of_right_eq_right_of_mem_cIoo hc hcol' hf hs
  have hsr : D.second.right = F.first.right := by
    rcases hdata.recut_branch with ⟨-, -, -, h⟩ | ⟨h, -⟩
    · exact h
    · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap F.second.left F.first.right)
        hcol' (Grid.mem_cIoo_cyclic_right h)).elim
  have hturn : s ∈ Grid.cIco F.first.bottom F.first.top := by
    simpa [F, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
      using E.pentagon.turn_mem_cIco_bottom_top
  have hrow := (F.cyclicOrder_of_isEmpty_of_right_eq_right hc
    (Grid.ne_left_of_mem_cIoo hcol') hf hs).2
  refine ⟨D, F.isRecut_recut hone hf hs, hfr.trans hsl.symm,
    (by simpa [F] using hsr : D.second.right = E.pentagon.right).trans E.pentagon.right_eq, ?_, ?_⟩
  · rw [hsb, hst]
    exact Grid.cIco_subset_of_mem_cIoo hrow hturn
  · rwa [hft, hst]

private theorem exists_rightLeftInverse_of_left_eq_left
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hcol : E.rectangle.right ∈ Grid.cIoo E.pentagon.left E.pentagon.right)
    (hp : E.pentagon.IsEmpty) (hr : E.rectangle.IsEmpty) :
    ∃ D : GridRectangleDecomposition x z,
      E.toRectangleDecomposition.IsRecut D ∧ D.first.right = D.second.left ∧
        D.second.right = finRotate n a ∧ s ∈ Grid.cIco D.second.bottom D.second.top ∧
          s ∈ Grid.cIco D.first.top D.second.top := by
  let F := E.toRectangleDecomposition
  have hc : F.first.left = F.second.left := by simpa [F] using hcommon
  have hcol' : F.second.right ∈ Grid.cIoo F.first.left F.first.right := by
    simpa [F] using hcol
  have hf := E.underlying_first_isEmpty hp
  have hs := E.underlying_second_isEmpty hr
  let hone := F.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hc hcol'
  let D := F.recut hone hf hs
  have hdata := F.isRecutOfLeftEqLeft_recut hc hone hf hs
  obtain ⟨hfr, hsr⟩ := hdata.recut_sides
  obtain ⟨hm, hfl, hsl⟩ : D.middle = x.swapColumns F.first.left F.second.right ∧
      D.first.left = F.first.left ∧ D.second.left = F.second.right := by
    rcases hdata.recut_branch with ⟨h, -⟩ | ⟨-, hm, hfl, hsl⟩
    · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap F.first.left F.second.right)
        h (Grid.mem_cIoo_cyclic_left hcol')).elim
    · exact ⟨hm, hfl, hsl⟩
  have hsb : D.second.bottom = F.first.bottom := by
    rw [GridRectangleBetween.bottom_def, hsl, hm, GridState.swapColumns_apply,
      Equiv.swap_apply_right, GridRectangleBetween.bottom_def]
  have hst : D.second.top = F.first.top := by
    rw [GridRectangleBetween.top_def, hsr, hm, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne F.first.left_ne_right.symm
        (Grid.ne_right_of_mem_cIoo hcol').symm, GridRectangleBetween.top_def]
  have hft : D.first.top = F.second.top := by
    rw [GridRectangleBetween.top_def, hfr, GridRectangleBetween.top_def,
      F.first.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol') (Grid.ne_right_of_mem_cIoo hcol')]
  have hturn : s ∈ Grid.cIco F.first.bottom F.first.top := by
    simpa [F, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
      using E.pentagon.turn_mem_cIco_bottom_top
  have hrtop : E.rectangle.bottom = E.pentagon.top := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, E.pentagon.map_left,
      GridRectangleBetween.top_def]
  have hnot := E.turn_notMem_cIco_rectangle_of_left_eq_left hcommon
    (Grid.ne_right_of_mem_cIoo hcol).symm hp hr
  rw [hrtop] at hnot
  have hcut : s ∈ Grid.cIco E.rectangle.top E.pentagon.top :=
    (Grid.notMem_cIco_iff_mem_cIco_swap (hrtop ▸ E.rectangle.bottom_ne_top)).1 hnot
  refine ⟨D, F.isRecut_recut hone hf hs, hfr.trans hsl.symm,
    (by simpa [F] using hsr : D.second.right = E.pentagon.right).trans E.pentagon.right_eq, ?_, ?_⟩
  · rwa [hsb, hst]
  · simpa only [hft, hst, F, GridRectangleBetween.top_def,
      toRectangleDecomposition_middle, toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcut

end TauCeti.GridPentagonRectangleDecomposition

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem ne_rows_of_rightLeftRecut
    (D : GridRectanglePentagonDecomposition a s x z)
    (E : GridPentagonRectangleDecomposition a s x z)
    (hc : D.toRectangleDecomposition.first.right = D.toRectangleDecomposition.second.left)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top)
    (hdata : D.toRectangleDecomposition.IsRecutOfRightEqLeft E.toRectangleDecomposition) :
    E.toRectangleDecomposition.first.bottom ≠ E.toRectangleDecomposition.second.bottom ∧
      E.toRectangleDecomposition.first.top ≠ E.toRectangleDecomposition.second.top := by
  have hbottom : E.toRectangleDecomposition.first.bottom ≠
      E.toRectangleDecomposition.second.bottom := by
    have hb : D.toRectangleDecomposition.second.bottom =
        D.toRectangleDecomposition.first.bottom := by
      rw [GridRectangleBetween.bottom_def, ← hc, D.toRectangleDecomposition.first.map_right,
        GridRectangleBetween.bottom_def]
    rcases hdata.recut_branch with ⟨-, -, hfb, hsb⟩ | ⟨-, -, hfb, hsb⟩
    · rw [hfb, hsb]
      exact D.toRectangleDecomposition.first.bottom_ne_top.symm
    · rw [hfb, hsb, ← hb]
      exact D.toRectangleDecomposition.second.bottom_ne_top
  have htop : E.toRectangleDecomposition.first.top ≠ E.toRectangleDecomposition.second.top := by
    obtain ⟨hft, hst⟩ := hdata.recut_sides
    rw [hft, hst]
    have ht : s ∈ Grid.cIco D.toRectangleDecomposition.first.top
        D.toRectangleDecomposition.second.top := by
      simpa only [GridRectangleBetween.top_def,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_middle] using hturn
    intro heq
    rw [heq] at ht
    simp at ht
  exact ⟨hbottom, htop⟩

end TauCeti.GridRectanglePentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

private theorem mem_rightLeftOverlapPartners_of_inverse
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (D : GridRectangleDecomposition x z) (hrecut : E.toRectangleDecomposition.IsRecut D)
    (hcommon : D.first.right = D.second.left) (hside : D.second.right = finRotate n C.column)
    (hturn : C.turnRow ∈ Grid.cIco D.second.bottom D.second.top)
    (hcut : C.turnRow ∈ Grid.cIco D.first.top D.second.top) :
    E ∈ G.rightLeftOverlapPartners C x z := by
  let F : GridRectanglePentagonDecomposition C.column C.turnRow x z :=
    { middle := D.middle
      first := D.first
      second := GridPentagonBetween.ofRightEq D.second hside hturn }
  have hFrect : F.toRectangleDecomposition = D := by
    apply GridRectangleDecomposition.ext <;>
      simp [F, GridRectanglePentagonDecomposition.pentagon, hside]
  rw [← hFrect] at hrecut
  have hFc : F.rectangle.right = F.pentagon.left := by
    simpa [F, GridRectanglePentagonDecomposition.rectangle,
      GridRectanglePentagonDecomposition.pentagon] using hcommon
  have hFt : C.turnRow ∈ Grid.cIco F.rectangle.top F.pentagon.top := by
    simpa [F, GridRectanglePentagonDecomposition.rectangle,
      GridRectanglePentagonDecomposition.pentagon] using hcut
  have hr := F.isEmpty_rectangle_of_isRecut hrecut
  have hp := F.isEmpty_pentagon_of_isRecut hrecut
  have hone := F.hasOneCommonSide_of_right_eq_left hFc
    (F.rectangle_left_ne_pentagon_right_of_mem_cIco hFt)
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
  have hback := hrecut.symm
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrecut
      (F.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone))
    (E.underlying_first_isEmpty ((G.mem_pentagons _).1 hP).1)
    (E.underlying_second_isEmpty
      (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1)
  have hEq : F.recutRightEqLeft hFc hr hp hFt = E := by
    apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
    exact (F.toRectangleDecomposition.existsUnique_isRecut hone
      hrecut.isEmpty_first hrecut.isEmpty_second).unique
      (F.isRecut_recutRightEqLeft hFc hr hp hFt) hback
  have hsquares := F.coveredSquares_val_add_val_recutRightEqLeft hFc hr hp hFt
  rw [hEq] at hsquares
  -- Transport avoidance backwards through the corrected square identity, including the swap.
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles,
    ← G.disjoint_map_swapColumns_XSet_iff] at hE
  have hX (p : Fin n × Fin n)
      (hp : p ∈ F.rectangle.toGridRectangle.coveredSquares.val + F.pentagon.coveredSquares.val) :
      p ∉ G.XSet := by
    rw [← hsquares] at hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · exact Finset.disjoint_left.mp hE.1.2 hp
    · exact Finset.disjoint_left.mp hE.2.2 hp
  have hF : F ∈ G.rectanglePentagonDecompositions C x z := by
    rw [mem_rectanglePentagonDecompositions, mem_unblockedRectangles, mem_pentagons]
    exact ⟨⟨hr, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inl hp))⟩,
      hp, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inr hp))⟩
  exact (G.mem_rightLeftOverlapPartners C E).2
    ⟨F, (G.mem_rightLeftOverlapSources C F).2 ⟨hF, hFc, hFt⟩, hback⟩

/-- A counted common-terminal-side domain whose pentagon starts inside its rectangle's
columns is the recut of a counted mixed `right = left` source. -/
theorem mem_rightLeftOverlapPartners_of_right_eq_right
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hcommon : E.pentagon.right = E.rectangle.right)
    (hcol : E.pentagon.left ∈ Grid.cIoo E.rectangle.left E.pentagon.right) :
    E ∈ G.rightLeftOverlapPartners C x z := by
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
  obtain ⟨D, hd, hc, hb, ht, hcut⟩ := E.exists_rightLeftInverse_of_right_eq_right
    hcommon hcol ((G.mem_pentagons _).1 hP).1
    (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1
  exact G.mem_rightLeftOverlapPartners_of_inverse C E hE D hd hc hb ht hcut

/-- A counted common-initial-side domain whose rectangle ends inside its pentagon's
columns is the recut of a counted mixed `right = left` source. -/
theorem mem_rightLeftOverlapPartners_of_left_eq_left
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hcol : E.rectangle.right ∈ Grid.cIoo E.pentagon.left E.pentagon.right) :
    E ∈ G.rightLeftOverlapPartners C x z := by
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
  obtain ⟨D, hd, hc, hb, ht, hcut⟩ := E.exists_rightLeftInverse_of_left_eq_left
    hcommon hcol ((G.mem_pentagons _).1 hP).1
    (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1
  exact G.mem_rightLeftOverlapPartners_of_inverse C E hE D hd hc hb ht hcut

private theorem rightLeftOverlapPartner_sides
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.rightLeftOverlapPartners C x z) :
    (E.pentagon.right = E.rectangle.right ∧
        E.pentagon.left ∈ Grid.cIoo E.rectangle.left E.pentagon.right) ∨
      (E.pentagon.left = E.rectangle.left ∧
        E.rectangle.right ∈ Grid.cIoo E.pentagon.left E.pentagon.right) := by
  obtain ⟨D, hD, hrecut⟩ := (G.mem_rightLeftOverlapPartners C E).1 hE
  obtain ⟨hcounted, hcommon, hturn⟩ := (G.mem_rightLeftOverlapSources C D).1 hD
  obtain ⟨hR, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcounted
  have hr := ((G.mem_unblockedRectangles _).1 hR).1
  have hp := ((G.mem_pentagons _).1 hP).1
  have hone := D.hasOneCommonSide_of_right_eq_left hcommon
    (D.rectangle_left_ne_pentagon_right_of_mem_cIco hturn)
  have hf : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hr
  have hs : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle] using hp
  have hc : D.toRectangleDecomposition.first.right = D.toRectangleDecomposition.second.left := by
    simpa using hcommon
  have hEq := (D.toRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
    (D.toRectangleDecomposition.isRecut_recut hone hf hs) hrecut
  have hdata := D.toRectangleDecomposition.isRecutOfRightEqLeft_recut hc hone hf hs
  rw [hEq] at hdata
  have hback := hrecut.symm hone hf hs
  -- Distinct outer rows exclude mixed-side partners; inspect the two same-side orientations.
  obtain ⟨hbottom, htop⟩ := D.ne_rows_of_rightLeftRecut E hc hturn hdata
  rcases hback.orientation with h | h | h | h
  · right
    refine ⟨by simpa using h.side_eq, ?_⟩
    rcases h.recut_branch with ⟨-, -, hfl, hsl⟩ | ⟨hcol, -⟩
    · obtain ⟨hfr, -⟩ := h.recut_sides
      exact (E.toRectangleDecomposition.second.left_ne_right
        (h.side_eq.symm.trans (hsl.symm.trans (hc.symm.trans hfr)))).elim
    · simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right] using hcol
  · left
    refine ⟨by simpa using h.side_eq, ?_⟩
    rcases h.recut_branch with ⟨hcol, -⟩ | ⟨-, -, hfr, -⟩
    · simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left] using hcol
    · obtain ⟨-, hsl⟩ := h.recut_sides
      exact (E.toRectangleDecomposition.first.left_ne_right
        (hsl.symm.trans (hc.symm.trans hfr))).elim
  · exfalso
    apply htop
    simp only [GridRectangleBetween.top_def]
    rw [← h.side_eq, E.toRectangleDecomposition.first.map_left]
  · exfalso
    apply hbottom
    simp only [GridRectangleBetween.bottom_def]
    rw [← h.side_eq, E.toRectangleDecomposition.first.map_right]

/-- The mixed `right = left` partners are exactly the counted pentagon--rectangle domains
sharing their terminal side with the pentagon starting inside the rectangle's columns, or
sharing their initial side with the rectangle ending inside the pentagon's columns. -/
@[grind =]
theorem mem_rightLeftOverlapPartners_iff_sides
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.rightLeftOverlapPartners C x z ↔
      E ∈ G.pentagonRectangleDecompositions C x z ∧
        ((E.pentagon.right = E.rectangle.right ∧
            E.pentagon.left ∈ Grid.cIoo E.rectangle.left E.pentagon.right) ∨
          (E.pentagon.left = E.rectangle.left ∧
            E.rectangle.right ∈ Grid.cIoo E.pentagon.left E.pentagon.right)) := by
  constructor
  · intro hE
    exact ⟨G.rightLeftOverlapPartners_subset C hE, G.rightLeftOverlapPartner_sides C E hE⟩
  · rintro ⟨hE, ⟨hc, hcol⟩ | ⟨hc, hcol⟩⟩
    · exact G.mem_rightLeftOverlapPartners_of_right_eq_right C E hE hc hcol
    · exact G.mem_rightLeftOverlapPartners_of_left_eq_left C E hE hc hcol

end TauCeti.GridDiagram
