/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.LeftRight
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.SameSum

/-!
# The mixed partners of initial-side same-sum pairs

Consider a rectangle of the original diagram followed by a commutation pentagon turning on its
initial side, which is the grid line `b = finRotate n a` replaced in the commutation.
`GridDiagram.initialPentagonInitialSelfPairs` collects the counted such domains whose two pieces
share their initial side `b`, the rectangle ending strictly inside the pentagon's column interval,
together with their recuts, which are again rectangle--initial-side-pentagon domains. This file
identifies these recuts without reference to the sources: they are exactly the counted mixed
overlaps in which the rectangle starts where the pentagon ends, with no other common side, and
whose recut does not have the turn row in its first rectangle. These are the mixed `left = right`
overlaps that `GridDiagram.initialPentagonLeftRightOverlapSources` leaves out.

When the first rectangle of the generic recut of such a mixed overlap misses the turn row, the
second recut rectangle starts on `b` and contains the turn row
(`GridRectangleInitialPentagonDecomposition.recutLeftEqRight_turn`), so the recut is again a
rectangle followed by an initial-side pentagon, both starting on `b`. Recutting it returns the
original domain, which does not start on `b`; this forces the recut's rectangle to end strictly
inside its pentagon's column interval. The recut is therefore a same-sum source, its own same-sum
recut is the original domain, and the two cover the same squares with the same multiplicities, so
the recut is counted (`GridDiagram.mem_initialPentagonInitialSelfPairs_of_left_eq_right`).

Conversely, the turn row of a same-sum source lies outside its rectangle's rows: the pentagon's
rows start at the rectangle's top row, which emptiness places strictly between the rectangle's
bottom row and the pentagon's top row
(`GridRectangleInitialPentagonDecomposition.turn_notMem_cIco_first_of_left_eq_left`). The recut of
a source's partner is the source, so no partner is a mixed `left = right` source
(`GridDiagram.mem_initialPentagonInitialSelfPairs_iff_sides`).

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.turn_notMem_cIco_first_of_left_eq_left`: the
  turn row of a domain whose two pieces share exactly their initial side, in particular of a
  same-sum source, lies outside its rectangle's rows.
* `TauCeti.GridDiagram.mem_initialPentagonInitialSelfPairs_of_left_eq_right`: a counted mixed
  `left = right` overlap outside `GridDiagram.initialPentagonLeftRightOverlapSources` is a
  same-sum pair.
* `TauCeti.GridDiagram.mem_initialPentagonInitialSelfPairs_iff_sides`: the same-sum pairs are the
  counted same-sum sources and the counted mixed `left = right` overlaps sharing one side column
  whose recut misses the turn row in its first rectangle.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- In a rectangle followed by an initial-side pentagon, both empty, sharing their initial side but
not their terminal side, the turn row lies outside the rectangle's rows. -/
theorem turn_notMem_cIco_first_of_left_eq_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    s ∉ Grid.cIco D.first.bottom D.first.top := by
  -- The pentagon's rows start at the rectangle's top row, which emptiness places strictly
  -- between the rectangle's bottom row and the pentagon's top row.
  have hrow := (D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    hright hfirst (by simpa only [pentagon_toGridRectangleBetween] using hpentagon)).2
  have hturn := D.second_turn_mem
  rw [D.toGridRectangleDecomposition.second_bottom_eq_first_top_of_left_eq_left hcommon] at hturn
  exact fun hs => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hs hturn

end TauCeti.GridRectangleInitialPentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted mixed `left = right` overlap with one common side whose recut misses the turn row in
its first rectangle is a same-sum pair: its recut is a counted rectangle--initial-side-pentagon
domain whose two pieces share their initial side, with the rectangle ending strictly inside the
pentagon's column interval. -/
theorem mem_initialPentagonInitialSelfPairs_of_left_eq_right
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z)
    (hcommon : D.first.left = D.second.right) (hother : D.first.right ≠ D.second.left)
    (hturn : ¬∃ E : GridRectangleDecomposition x z,
      D.toGridRectangleDecomposition.IsRecut E ∧ C.turnRow ∈ Grid.cIco E.first.bottom E.first.top) :
    D ∈ G.initialPentagonInitialSelfPairs C x z := by
  obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hD
  have hfirst := ((G.mem_unblockedRectangles _).1 hR).1
  have hpentagon := ((G.mem_initialPentagons _).1 hP).1
  have hone := D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother
  have hturn' : C.turnRow ∉ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hpentagon).first.bottom
      (D.leftRightRecut hcommon hother hfirst hpentagon).first.top := fun h =>
    hturn ⟨_, D.isRecut_leftRightRecut hcommon hother hfirst hpentagon, h⟩
  let E := D.recutLeftEqRightSecond hcommon hother hfirst hpentagon hturn'
  have hErect : E.toGridRectangleDecomposition = D.leftRightRecut hcommon hother hfirst hpentagon :=
    D.recutLeftEqRightSecond_toGridRectangleDecomposition hcommon hother hfirst hpentagon hturn'
  have hrecut : D.toGridRectangleDecomposition.IsRecut E.toGridRectangleDecomposition := by
    rw [hErect]
    exact D.isRecut_leftRightRecut hcommon hother hfirst hpentagon
  have hback := hrecut.symm hone hfirst
    (by simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
      using hpentagon)
  have hEone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (D.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  have hEfirst : E.first.IsEmpty := hrecut.isEmpty_first
  have hEpentagon : E.pentagon.IsEmpty := by
    simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
      using hrecut.isEmpty_second
  -- Both pieces of the recut start on the replaced line.
  have hEfirstLeft : E.first.left = D.second.left := by
    change E.toGridRectangleDecomposition.first.left = _
    rw [hErect]
    exact D.leftRightRecut_first_left hcommon hother hfirst hpentagon
  have hEcommon : E.first.left = E.second.left :=
    hEfirstLeft.trans (D.second_left_eq.trans E.second_left_eq.symm)
  -- Recutting the recut returns `D`, which does not start on the replaced line; this fixes the
  -- column order of the recut.
  have hEcol : E.first.right ∈ Grid.cIoo E.second.left E.second.right := by
    have hdata :
        E.toGridRectangleDecomposition.IsRecutOfLeftEqLeft D.toGridRectangleDecomposition := by
      rcases hback.orientation with h | h | h | h
      · exact h
      · refine absurd ?_ (E.toGridRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hEone)
        rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hEcommon,
          h.side_eq]
      · exact absurd (hEcommon.symm.trans h.side_eq) E.second.left_ne_right
      · exact absurd (h.side_eq.trans hEcommon.symm) E.first.left_ne_right.symm
    rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, -, hleft, -⟩
    · rwa [← hEcommon]
    · exact absurd (hcommon.symm.trans (hleft.trans hEfirstLeft)) D.second.left_ne_right.symm
  -- The same-sum recut of the recut is `D`, so the two cover the same squares.
  have hEq : E.recutInitialSelf hEcommon hEcol hEfirst hEpentagon = D := by
    apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
    exact (E.toGridRectangleDecomposition.existsUnique_isRecut hEone hEfirst
      hrecut.isEmpty_second).unique
      (E.isRecut_recutInitialSelf hEcommon hEcol hEfirst hEpentagon) hback
  have hsquares : D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val =
      E.first.toGridRectangle.coveredSquares.val + E.pentagon.coveredSquares.val := by
    rw [← hEq]
    exact E.coveredSquares_val_add_recutInitialSelf hEcommon hEcol hEfirst hEpentagon
  have hEcounted := G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq C hD hEfirst
    hEpentagon hsquares.symm
  exact (G.mem_initialPentagonInitialSelfPairs C D).2
    (Or.inr ⟨E, (G.mem_initialPentagonInitialSelfSources C E).2 ⟨hEcounted, hEcommon, hEcol⟩,
      hback⟩)

/-- The same-sum pairs of rectangle--initial-side-pentagon domains are the counted domains of two
kinds: those whose two pieces share their initial side, the rectangle ending strictly inside the
pentagon's column interval; and those in which the rectangle starts where the pentagon ends, with
no other common side, and whose recut misses the turn row in its first rectangle. -/
theorem mem_initialPentagonInitialSelfPairs_iff_sides
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.initialPentagonInitialSelfPairs C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        ((D.first.left = D.second.left ∧
            D.first.right ∈ Grid.cIoo D.second.left D.second.right) ∨
          (D.first.left = D.second.right ∧ D.first.right ≠ D.second.left ∧
            ¬∃ E : GridRectangleDecomposition x z,
              D.toGridRectangleDecomposition.IsRecut E ∧
                C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)) := by
  constructor
  · intro hpair
    refine ⟨G.initialPentagonInitialSelfPairs_subset C hpair, ?_⟩
    rcases (G.mem_initialPentagonInitialSelfPairs C D).1 hpair with hsource | ⟨S, hS, hrecut⟩
    · exact Or.inl ((G.mem_initialPentagonInitialSelfSources C D).1 hsource).2
    right
    obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_initialPentagonInitialSelfSources C S).1 hS
    obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C S).1 hcounted
    have hfirst := ((G.mem_unblockedRectangles _).1 hR).1
    have hpentagon := ((G.mem_initialPentagons _).1 hP).1
    have hsecond : S.second.IsEmpty := by
      simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
        using hpentagon
    have hone := S.hasOneCommonSide_of_initial_self hcommon hcol
    -- `D` is the same-sum recut of the source `S`.
    have hEq : S.recutInitialSelf hcommon hcol hfirst hpentagon = D := by
      apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
      exact (S.toGridRectangleDecomposition.existsUnique_isRecut hone hfirst hsecond).unique
        (S.isRecut_recutInitialSelf hcommon hcol hfirst hpentagon) hrecut
    obtain ⟨-, hfirstLeft, hfirstRight, hsecondLeft, hsecondRight, -, -⟩ :=
      S.recutInitialSelf_geometry hcommon hcol hfirst hpentagon
    rw [hEq] at hfirstLeft hfirstRight hsecondLeft hsecondRight
    refine ⟨hfirstLeft.trans hsecondRight.symm, fun h => ?_, ?_⟩
    · exact S.second.left_ne_right
        (hcommon.symm.trans (hsecondLeft.symm.trans (h.symm.trans hfirstRight)))
    -- Otherwise the recut of `D`, which is `S`, would have the turn row in its rectangle.
    rintro ⟨E, hE, hs⟩
    have hback := hrecut.symm hone hfirst hsecond
    have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
      (S.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
    have hES := (D.toGridRectangleDecomposition.existsUnique_isRecut hDone hrecut.isEmpty_first
      hrecut.isEmpty_second).unique hE hback
    rw [hES] at hs
    exact S.turn_notMem_cIco_first_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hcol) hfirst
      hpentagon hs
  · rintro ⟨hD, hsource | ⟨hcommon, hother, hturn⟩⟩
    · exact (G.mem_initialPentagonInitialSelfPairs C D).2 (Or.inl
        ((G.mem_initialPentagonInitialSelfSources C D).2 ⟨hD, hsource⟩))
    · exact G.mem_initialPentagonInitialSelfPairs_of_left_eq_right C D hD hcommon hother hturn

end TauCeti.GridDiagram
