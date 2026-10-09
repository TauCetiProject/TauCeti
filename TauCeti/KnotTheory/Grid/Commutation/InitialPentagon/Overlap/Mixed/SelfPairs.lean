/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.LeftRight
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.SameSum

/-!
# The mixed members of initial self-pairs

Consider a rectangle of the original diagram followed by a commutation pentagon turning on its
initial side, which is the grid line `b = finRotate n a` replaced in the commutation.
`GridDiagram.initialPentagonInitialSelfPairs` collects the counted such domains whose two pieces
share their initial side `b`, the rectangle ending strictly inside the pentagon's column interval,
together with their recuts, which are again rectangle--initial-side-pentagon domains. This file
identifies these recuts without reference to the sources: they are exactly the counted mixed
overlaps in which the rectangle starts where the pentagon ends, with no other common side, and
whose generic recut does not have the turn row in its first rectangle. These are the mixed
`left = right` overlaps that `GridDiagram.initialPentagonLeftRightOverlapSources` leaves out.

Write `f` and `q` for the rectangle's sides and `b`, `f` for the pentagon's. When the first
rectangle of the generic recut misses the turn row, the recut is again a rectangle followed by an
initial-side pentagon (`GridRectangleInitialPentagonDecomposition.recutLeftEqRightSecond`), and
both of its pieces start on `b`. Recutting it returns the original domain, whose rectangle starts
on `f`; the side data of this recut puts `f` strictly between `b` and `q`, so the promoted recut is
a common-initial-side self source. Its same-sum recut is the original domain, so the two composite
domains cover the same squares with the same multiplicities, and the promoted recut is counted
(`GridDiagram.mem_initialPentagonInitialSelfPairs_of_left_eq_right`).

Conversely, the turn row of a common-initial-side self source lies outside its rectangle's rows:
the pentagon's rows begin where the rectangle's end, and emptiness puts the rectangle's top row
strictly between its bottom row and the pentagon's top row
(`GridRectangleInitialPentagonDecomposition.turn_notMem_cIco_first_of_left_eq_left`). A recut
partner of a source has the source as its own recut, so the first rectangle of that recut misses
the turn row. The two descriptions therefore agree
(`GridDiagram.mem_initialPentagonInitialSelfPairs_iff_sides`); in particular no initial self-pair
is a mixed `left = right` source.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.turn_notMem_cIco_first_of_left_eq_left`: the
  turn row of a common-initial-side self source lies outside its rectangle's rows.
* `TauCeti.GridDiagram.mem_initialPentagonInitialSelfPairs_of_left_eq_right`: a counted mixed
  `left = right` overlap outside `GridDiagram.initialPentagonLeftRightOverlapSources` is an
  initial self-pair.
* `TauCeti.GridDiagram.mem_initialPentagonInitialSelfPairs_iff_sides`: the initial self-pairs are
  the counted common-initial-side self sources and the counted mixed `left = right` overlaps
  sharing one side column whose recut has the turn row outside its first rectangle.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- In a rectangle--initial-side-pentagon domain whose two pieces share their initial side, the
rectangle ending strictly inside the pentagon's column interval, the turn row lies outside the
rectangle's rows. -/
theorem turn_notMem_cIco_first_of_left_eq_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    s ∉ Grid.cIco D.first.bottom D.first.top := by
  -- The pentagon's rows begin at the rectangle's top row, which emptiness puts strictly between
  -- the rectangle's bottom row and the pentagon's top row.
  have horder := (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    (Grid.ne_right_of_mem_cIoo hcol) hfirst hsecond).2
  have hturn := D.second_turn_mem
  rw [D.second_bottom_eq_first_top_of_left_eq_left hcommon] at hturn
  exact fun hs => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo horder) hs hturn

end TauCeti.GridRectangleInitialPentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- The two pieces of a counted rectangle--initial-side-pentagon domain are empty. -/
private theorem isEmpty_of_mem_rectangleInitialPentagonDecompositions
    {D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z}
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.first.IsEmpty ∧ D.pentagon.IsEmpty ∧ D.second.IsEmpty := by
  rw [G.mem_rectangleInitialPentagonDecompositions, G.mem_unblockedRectangles,
    G.mem_initialPentagons] at hD
  refine ⟨hD.1.1, hD.2.1, ?_⟩
  simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] using
    hD.2.1

/-- A counted mixed `left = right` overlap, with no other common side, whose generic recut has the
turn row outside its first rectangle is an initial self-pair: its recut is a counted
rectangle--initial-side-pentagon domain whose two pieces share their initial side, with the
rectangle ending strictly inside the pentagon's column interval. -/
theorem mem_initialPentagonInitialSelfPairs_of_left_eq_right
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z)
    (hcommon : D.first.left = D.second.right) (hother : D.first.right ≠ D.second.left)
    (hturn : ¬∃ E : GridRectangleDecomposition x z,
      D.IsRecut E ∧ C.turnRow ∈ Grid.cIco E.first.bottom E.first.top) :
    D ∈ G.initialPentagonInitialSelfPairs C x z := by
  obtain ⟨hfirst, hpentagon, hsecond⟩ :=
    G.isEmpty_of_mem_rectangleInitialPentagonDecompositions C hD
  have hone := D.hasOneCommonSide_of_left_eq_right hcommon hother
  have hrecut := D.isRecut_leftRightRecut hcommon hother hfirst hpentagon
  have hturn' : C.turnRow ∉
      Grid.cIco (D.leftRightRecut hcommon hother hfirst hpentagon).first.bottom
        (D.leftRightRecut hcommon hother hfirst hpentagon).first.top := fun h =>
    hturn ⟨_, hrecut, h⟩
  let E := D.recutLeftEqRightSecond hcommon hother hfirst hpentagon hturn'
  have hE : E.toGridRectangleDecomposition = D.leftRightRecut hcommon hother hfirst hpentagon :=
    D.recutLeftEqRightSecond_toGridRectangleDecomposition hcommon hother hfirst hpentagon hturn'
  have hErecut : D.IsRecut E.toGridRectangleDecomposition := hE ▸ hrecut
  have hback := hErecut.symm hone hfirst hsecond
  have hEone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (D.target_ne_source_of_hasOneCommonSide hone)
  have hEfirst : E.first.IsEmpty := hErecut.isEmpty_first
  have hEsecond : E.second.IsEmpty := hErecut.isEmpty_second
  have hEpentagon : E.pentagon.IsEmpty := by
    simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] using
      hEsecond
  -- Both pieces of the promoted recut start on the replaced line.
  have hEcommon : E.first.left = E.second.left := by
    have h := D.leftRightRecut_first_left hcommon hother hfirst hpentagon
    rw [← hE] at h
    exact h.trans (D.second_left_eq.trans E.second_left_eq.symm)
  -- Recutting the promoted recut returns `D`, whose rectangle does not start on the replaced line;
  -- this fixes the column order of the promoted recut.
  have hEcol : E.first.right ∈ Grid.cIoo E.second.left E.second.right := by
    rcases hback.orientation with h | h | h | h
    · rcases h.recut_branch with ⟨hcol, -⟩ | ⟨-, -, hleft, -⟩
      · rwa [← hEcommon]
      · exact (D.second.left_ne_right ((D.second_left_eq.trans E.second_left_eq.symm).trans
          (hEcommon.symm.trans (hleft.symm.trans hcommon)))).elim
    · refine absurd ?_ (E.toGridRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hEone)
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hEcommon, h.side_eq]
    · exact (E.second.left_ne_right (hEcommon.symm.trans h.side_eq)).elim
    · exact (E.first.left_ne_right (hEcommon.trans h.side_eq.symm)).elim
  -- The same-sum recut of the promoted recut is `D`, so the two cover the same squares.
  have heq : E.recutInitialSelf hEcommon hEcol hEfirst hEpentagon = D :=
    GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
      ((E.toGridRectangleDecomposition.existsUnique_isRecut hEone hEfirst hEsecond).unique
        (E.isRecut_recutInitialSelf hEcommon hEcol hEfirst hEpentagon) hback)
  have hcov : D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val =
      E.first.toGridRectangle.coveredSquares.val + E.pentagon.coveredSquares.val := by
    rw [← heq]
    exact E.coveredSquares_val_add_recutInitialSelf hEcommon hEcol hEfirst hEpentagon
  refine (G.mem_initialPentagonInitialSelfPairs C D).2 (Or.inr ⟨E, ?_, hback⟩)
  exact (G.mem_initialPentagonInitialSelfSources C E).2
    ⟨G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq C hD hEfirst hEpentagon
      hcov.symm, hEcommon, hEcol⟩

/-- The initial self-pairs are the counted rectangle--initial-side-pentagon domains of two kinds:
those whose two pieces share their initial side, the rectangle ending strictly inside the
pentagon's column interval; and those in which the rectangle starts where the pentagon ends, with
no other common side, and whose recut has the turn row outside its first rectangle. -/
theorem mem_initialPentagonInitialSelfPairs_iff_sides
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.initialPentagonInitialSelfPairs C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        ((D.first.left = D.second.left ∧
            D.first.right ∈ Grid.cIoo D.second.left D.second.right) ∨
          (D.first.left = D.second.right ∧ D.first.right ≠ D.second.left ∧
            ¬∃ E : GridRectangleDecomposition x z,
              D.IsRecut E ∧ C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)) := by
  constructor
  · intro hpair
    refine ⟨G.initialPentagonInitialSelfPairs_subset C hpair, ?_⟩
    rcases (G.mem_initialPentagonInitialSelfPairs C D).1 hpair with hsource | ⟨D₀, hD₀, hrecut⟩
    · exact Or.inl ((G.mem_initialPentagonInitialSelfSources C D).1 hsource).2
    right
    obtain ⟨hcounted₀, hcommon₀, hcol₀⟩ := (G.mem_initialPentagonInitialSelfSources C D₀).1 hD₀
    obtain ⟨hfirst₀, hpentagon₀, hsecond₀⟩ :=
      G.isEmpty_of_mem_rectangleInitialPentagonDecompositions C hcounted₀
    have hone₀ := D₀.hasOneCommonSide_of_initial_self hcommon₀ hcol₀
    -- The partner is the same-sum recut of the source.
    have heq : D₀.recutInitialSelf hcommon₀ hcol₀ hfirst₀ hpentagon₀ = D :=
      GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
        ((D₀.toGridRectangleDecomposition.existsUnique_isRecut hone₀ hfirst₀ hsecond₀).unique
          (D₀.isRecut_recutInitialSelf hcommon₀ hcol₀ hfirst₀ hpentagon₀) hrecut)
    obtain ⟨-, hfl, hfr, hsl, hsr, -, -⟩ :=
      D₀.recutInitialSelf_geometry hcommon₀ hcol₀ hfirst₀ hpentagon₀
    rw [heq] at hfl hfr hsl hsr
    refine ⟨hfl.trans hsr.symm, fun h => D₀.second.left_ne_right
      (hcommon₀.symm.trans (hsl.symm.trans (h.symm.trans hfr))), ?_⟩
    -- The only recut of the partner is the source, whose rectangle misses the turn row.
    rintro ⟨E, hE, hs⟩
    have hback := hrecut.symm hone₀ hfirst₀ hsecond₀
    have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
      (D₀.target_ne_source_of_hasOneCommonSide hone₀)
    rw [(D.existsUnique_isRecut hone hrecut.isEmpty_first hrecut.isEmpty_second).unique hE
      hback] at hs
    exact D₀.turn_notMem_cIco_first_of_left_eq_left hcommon₀ hcol₀ hfirst₀ hsecond₀ hs
  · rintro ⟨hD, hsource | ⟨hcommon, hother, hturn⟩⟩
    · exact (G.mem_initialPentagonInitialSelfPairs C D).2 (Or.inl
        ((G.mem_initialPentagonInitialSelfSources C D).2 ⟨hD, hsource⟩))
    · exact G.mem_initialPentagonInitialSelfPairs_of_left_eq_right C D hD hcommon hother hturn

end TauCeti.GridDiagram
