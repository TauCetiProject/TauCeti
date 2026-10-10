/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Mixed.LeftRight.Basic

/-!
# Geometric characterization of mixed `left = right` recut partners

The partners of a rectangle starting where a terminal-side commutation pentagon ends are
pentagon--rectangle domains sharing their initial side. The pentagon's terminal side lies
strictly inside the rectangle's column interval. This file characterizes the counted partners
by that geometry, without quantifying over recut sources. It supplies a case of the partition
of the pentagon--rectangle coefficient sum in the commutation chain-map equation.

The inverse recut starts its rectangle on the replaced line and ends its pentagon there.
The rectangle retains the following rectangle's rows, which avoid the turn row by emptiness
and the cyclic row order. The existing forward recut preserves corrected square multiplicities;
its inverse therefore transports marking avoidance as well as emptiness.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The forward recut is formalized in `LeftRight.Basic`.
-/

public section

namespace TauCeti.GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The turn row lies outside the following rectangle when two empty pieces share their
initial side and have distinct terminal sides. -/
theorem turn_notMem_cIco_rectangle_of_left_eq_left
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hother : E.pentagon.right ≠ E.rectangle.right)
    (hp : E.pentagon.IsEmpty) (hr : E.rectangle.IsEmpty) :
    s ∉ Grid.cIco E.rectangle.bottom E.rectangle.top := by
  have hrow := (E.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left
    (by simpa using hcommon) (by simpa using hother)
    (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)).2
  have hb := E.toRectangleDecomposition.second_bottom_eq_first_top_of_left_eq_left
    (by simpa using hcommon)
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
    toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left, toRectangleDecomposition_second_right,
    toRectangleDecomposition_middle] at hrow hb
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hb]
  exact fun hs => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow)
    E.pentagon.turn_mem hs

private theorem leftRightInverse_geometry (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hcol : E.pentagon.right ∈ Grid.cIoo E.pentagon.left E.rectangle.right)
    (hp : E.pentagon.IsEmpty) (hr : E.rectangle.IsEmpty) :
    let hone := E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left
      (by simpa using hcommon) (by simpa using Grid.ne_right_of_mem_cIoo hcol)
    let D := E.toRectangleDecomposition.recut hone
      (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)
    D.first.left = E.pentagon.right ∧ D.second.right = E.pentagon.right ∧
      D.second.bottom = E.pentagon.bottom ∧ D.second.top = E.rectangle.top ∧
        D.first.bottom = E.rectangle.bottom ∧ D.first.top = E.rectangle.top := by
  intro hone D
  have hdata := E.toRectangleDecomposition.isRecutOfLeftEqLeft_recut
    (by simpa using hcommon) hone
    (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)
  obtain ⟨hfr, hsr⟩ := hdata.recut_sides
  simp only [toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_right] at hfr hsr
  rcases hdata.recut_branch with ⟨-, hm, hfl, hsl⟩ | ⟨hcol', -⟩
  · simp only [toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] at hm hfl hsl
    have hbottom : D.second.bottom = E.pentagon.bottom := by
      rw [GridRectangleBetween.bottom_def, hsl, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne E.pentagon.left_ne_right
          (hcommon ▸ E.rectangle.left_ne_right), GridRectangleBetween.bottom_def]
    have hout : x E.rectangle.right = E.middle E.rectangle.right :=
      (E.pentagon.map_of_ne _ (hcommon ▸ E.rectangle.left_ne_right.symm)
        (Grid.ne_right_of_mem_cIoo hcol).symm).symm
    have hsecondTop : D.second.top = E.rectangle.top := by
      rw [GridRectangleBetween.top_def, hsr, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_left, GridRectangleBetween.top_def]
      exact hout
    have hfirstBottom : D.first.bottom = E.rectangle.bottom := by
      rw [GridRectangleBetween.bottom_def, hfl, GridRectangleBetween.bottom_def,
        ← hcommon, E.pentagon.map_left]
    have hfirstTop : D.first.top = E.rectangle.top := by
      rw [GridRectangleBetween.top_def, hfr, GridRectangleBetween.top_def]
      exact hout
    exact ⟨hfl, hsr, hbottom, hsecondTop, hfirstBottom, hfirstTop⟩
  · simp only [toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] at hcol'
    exact (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap E.pentagon.left E.rectangle.right)
      hcol (Grid.mem_cIoo_cyclic_left hcol')).elim

private noncomputable def leftRightInverse (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hcol : E.pentagon.right ∈ Grid.cIoo E.pentagon.left E.rectangle.right)
    (hp : E.pentagon.IsEmpty) (hr : E.rectangle.IsEmpty) :
    GridRectanglePentagonDecomposition a s x z where
  middle := (E.toRectangleDecomposition.recut
    (E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left (by simpa using hcommon)
      (by simpa using Grid.ne_right_of_mem_cIoo hcol))
    (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)).middle
  rectangle := (E.toRectangleDecomposition.recut
    (E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left (by simpa using hcommon)
      (by simpa using Grid.ne_right_of_mem_cIoo hcol))
    (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)).first
  pentagon := GridPentagonBetween.ofRightEq
    (E.toRectangleDecomposition.recut
      (E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left (by simpa using hcommon)
        (by simpa using Grid.ne_right_of_mem_cIoo hcol))
      (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)).second
    ((E.leftRightInverse_geometry hcommon hcol hp hr).2.1.trans E.pentagon.right_eq)
    (by
      rw [(E.leftRightInverse_geometry hcommon hcol hp hr).2.2.1,
        (E.leftRightInverse_geometry hcommon hcol hp hr).2.2.2.1]
      have hrow := (E.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left
        (by simpa using hcommon) (by simpa using Grid.ne_right_of_mem_cIoo hcol)
        (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)).2
      simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
        toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right, toRectangleDecomposition_middle] at hrow
      have hrow' : E.pentagon.top ∈ Grid.cIoo E.pentagon.bottom E.rectangle.top := by
        simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] using hrow
      rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow']
      exact Finset.mem_union_left _ E.pentagon.turn_mem)

private theorem leftRightInverse_toRectangleDecomposition
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hcol : E.pentagon.right ∈ Grid.cIoo E.pentagon.left E.rectangle.right)
    (hp : E.pentagon.IsEmpty) (hr : E.rectangle.IsEmpty) :
    (E.leftRightInverse hcommon hcol hp hr).toRectangleDecomposition =
      E.toRectangleDecomposition.recut
        (E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left (by simpa using hcommon)
          (by simpa using Grid.ne_right_of_mem_cIoo hcol))
        (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr) := by
  apply GridRectangleDecomposition.ext <;>
    simp [leftRightInverse, (E.leftRightInverse_geometry hcommon hcol hp hr).2.1]

end TauCeti.GridPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted common-initial-side pentagon--rectangle domain whose pentagon ends strictly inside
its rectangle's column interval is the recut of a counted mixed `left = right` source. -/
theorem mem_leftRightOverlapPartners_of_left_eq_left
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hcol : E.pentagon.right ∈ Grid.cIoo E.pentagon.left E.rectangle.right) :
    E ∈ G.leftRightOverlapPartners C x z := by
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
  have hp := ((G.mem_pentagons _).1 hP).1
  have hr := (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1
  have hone := E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left
    (by simpa using hcommon) (by simpa using Grid.ne_right_of_mem_cIoo hcol)
  -- Reconstruct the mixed source and use empty-rectangle recut uniqueness to recover E.
  let D := E.leftRightInverse hcommon hcol hp hr
  have hDrect := E.leftRightInverse_toRectangleDecomposition hcommon hcol hp hr
  have hrecut : E.toRectangleDecomposition.IsRecut D.toRectangleDecomposition := by
    rw [hDrect]
    exact E.toRectangleDecomposition.isRecut_recut hone
      (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)
  have hback := hrecut.symm hone (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  have hDr := D.isEmpty_rectangle_of_isRecut hrecut
  have hDp := D.isEmpty_pentagon_of_isRecut hrecut
  obtain ⟨hfl, hsr, -, -, hfb, hft⟩ := E.leftRightInverse_geometry hcommon hcol hp hr
  rw [← hDrect] at hfl hsr hfb hft
  have hDcommon : D.rectangle.left = D.pentagon.right := by
    simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right] using
      hfl.trans hsr.symm
  have hturn : C.turnRow ∉ Grid.cIco D.rectangle.bottom D.rectangle.top := by
    simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right] at hfb hft
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hfb, hft]
    exact E.turn_notMem_cIco_rectangle_of_left_eq_left hcommon
      (Grid.ne_right_of_mem_cIoo hcol) hp hr
  have hEq : D.recutLeftEqRight hDcommon hDr hDp hturn = E := by
    apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
    exact (D.toRectangleDecomposition.existsUnique_isRecut hDone
      hrecut.isEmpty_first hrecut.isEmpty_second).unique
      (D.isRecut_recutLeftEqRight hDcommon hDr hDp hturn) hback
  have hsquares := D.coveredSquares_val_add_val_recutLeftEqRight hDcommon hDr hDp hturn
  rw [hEq] at hsquares
  -- Use the forward square identity backwards: every square of the inverse domain avoids X.
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles,
    ← G.disjoint_map_swapColumns_XSet_iff] at hE
  have hX (p : Fin n × Fin n)
      (hp : p ∈ D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
      p ∉ G.XSet := by
    rw [← hsquares] at hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · exact Finset.disjoint_left.mp hE.1.2 hp
    · exact Finset.disjoint_left.mp hE.2.2 hp
  have hD : D ∈ G.rectanglePentagonDecompositions C x z := by
    rw [mem_rectanglePentagonDecompositions, mem_unblockedRectangles, mem_pentagons]
    exact ⟨⟨hDr, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inl hp))⟩,
      hDp, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inr hp))⟩
  exact (G.mem_leftRightOverlapPartners C E).2
    ⟨D, (G.mem_leftRightOverlapSources C D).2 ⟨hD, hDcommon, hturn⟩, hback⟩

/-- The mixed `left = right` partners are exactly the counted pentagon--rectangle domains
sharing their initial side, with the pentagon's terminal side strictly inside the rectangle's
column interval. -/
@[grind =]
theorem mem_leftRightOverlapPartners_iff_sides
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.leftRightOverlapPartners C x z ↔
      E ∈ G.pentagonRectangleDecompositions C x z ∧
        E.pentagon.left = E.rectangle.left ∧
          E.pentagon.right ∈ Grid.cIoo E.pentagon.left E.rectangle.right := by
  constructor
  · intro hE
    refine ⟨G.leftRightOverlapPartners_subset C hE, ?_⟩
    obtain ⟨D, hD, hrecut⟩ := (G.mem_leftRightOverlapPartners C E).1 hE
    obtain ⟨hcounted, hcommon, hturn⟩ := (G.mem_leftRightOverlapSources C D).1 hD
    obtain ⟨hR, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcounted
    have hr := ((G.mem_unblockedRectangles _).1 hR).1
    have hp := ((G.mem_pentagons _).1 hP).1
    have hone := D.hasOneCommonSide_of_left_eq_right hcommon
      (D.rectangle_right_ne_pentagon_left_of_left_eq_right hcommon hturn)
    have hEq : D.recutLeftEqRight hcommon hr hp hturn = E := by
      apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
      exact (D.toRectangleDecomposition.existsUnique_isRecut hone
        (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hr)
        (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
          using hp)).unique (D.isRecut_recutLeftEqRight hcommon hr hp hturn) hrecut
    obtain ⟨-, hpl, hrl, -, -, -, -⟩ := D.recutLeftEqRight_geometry hcommon hr hp hturn
    rw [hEq] at hpl hrl
    have hEcommon := hpl.trans hrl.symm
    refine ⟨hEcommon, ?_⟩
    have hback := hrecut.symm hone
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hr)
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
        using hp)
    have hEone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
      (D.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
    have hdata := hback.isRecutOfLeftEqLeft hEone (by simpa using hEcommon)
    rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, -, hleft, -⟩
    · simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right] using hcol
    · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left] at hleft
      exact (D.pentagon.left_ne_right (hpl.symm.trans (hleft.symm.trans hcommon))).elim
  · rintro ⟨hE, hcommon, hcol⟩
    exact G.mem_leftRightOverlapPartners_of_left_eq_left C E hE hcommon hcol

end TauCeti.GridDiagram
