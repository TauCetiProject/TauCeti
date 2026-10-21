/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Recut

/-!
# Off-diagonal unpaired hexagon composites have a mixed-side overlap

On the left-hand side `∂ ∘ H + H ∘ ∂` of the homotopy equation of a column commutation, a counted
hexagon composite whose two rectangles share exactly one side column cancels against its recut
whenever that recut is again a counted composite (`Homotopy.Recut`). This file shows that this
always happens when the shared column is initial for both rectangles or terminal for both.
Consequently, off the diagonal, every unpaired composite has a mixed-side overlap.

The argument has two independent parts.

* *Markings.* A counted composite covers exactly one `X`-marking, that of the column its hexagon
  cuts away. If a repartition of its domain into two empty rectangles has a piece with the shape of
  a commutation hexagon, that piece covers the `X`-marking of its own cut-away column, which must
  therefore be the single one. Its hexagon carries no `X`-marking, the other piece carries none
  either, and the repartition is a counted composite
  (`GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition`).
* *Shapes.* For a same-side overlap, the recut cuts the L-shaped union the other way. Its two
  pieces keep the outer sides of the original rectangles in the same position, and their rows
  are either the rows of the corresponding original rectangle or the union of both row
  intervals. The replaced grid line is a side of the original hexagon. If it is that hexagon's
  outer side, the corresponding recut piece keeps it; if it is the common side, the recut piece
  spanning both row intervals has it. In both cases the two turn rows remain on that side, in
  the same order, so this piece has the shape of a commutation hexagon of the same kind.

## Main results

* `TauCeti.GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition`: a repartition of a
  counted composite into empty rectangles, one of which underlies a commutation hexagon, underlies
  a counted composite.
* `TauCeti.GridDiagram.exists_isRecut_of_hasSameSideOverlap`: the recut of a counted composite
  with a same-side overlap underlies a counted composite.
* `TauCeti.GridDiagram.hasMixedSideOverlap_of_mem_unpairedHexagonComposites`: off the diagonal,
  every unpaired composite has a mixed-side overlap.

## References

This is the same-side case of the hexagon--rectangle juxtaposition argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Promoting a repartition to a counted composite -/

/-- Every `X`-marking covered by a counted composite is one and the same. -/
private theorem exists_eq_of_mem_XSet_of_mem_coveredSquares_union {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z) :
    ∃ c : Fin n, ∀ p ∈ G.XSet,
      p ∈ F.toRectangleDecomposition.first.toGridRectangle.coveredSquares ∪
          F.toRectangleDecomposition.second.toGridRectangle.coveredSquares →
        p = (c, G.X c) := by
  have hhex {u v : GridState n}
      {P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow u v}
      (hP : P ∈ G.commutationHexagons C u v) {p : Fin n × Fin n} (hX : p ∈ G.XSet)
      (hp : p ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares) :
      p = (P.cutColumn, G.X P.cutColumn) := by
    have hmem := Finset.mem_inter.mpr ⟨hX, hp⟩
    rw [G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP] at hmem
    exact Finset.mem_singleton.mp hmem
  cases F with
  | inl F =>
    obtain ⟨hP, hr⟩ := (G.mem_hexagonRectangleDecompositions C F).mp
      ((G.inl_mem_hexagonCompositeDecompositions C F).mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hX hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hhex hP hX hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hX).elim
  | inr F =>
    obtain ⟨hr, hP⟩ := (G.mem_rectangleHexagonDecompositions C F).mp
      ((G.inr_mem_hexagonCompositeDecompositions C F).mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hX hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hX).elim
    · exact hhex hP hX hp

/-- A commutation hexagon whose underlying rectangle lies in a domain covering at most one
`X`-marking carries no `X`-marking, and its underlying rectangle covers that one. -/
private theorem disjoint_XSet_and_mem_of_coveredSquares_subset {u v : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow u v)
    {S : Finset (Fin n × Fin n)} {c : Fin n} (hc : ∀ p ∈ G.XSet, p ∈ S → p = (c, G.X c))
    (hsub : P.toGridRectangleBetween.toGridRectangle.coveredSquares ⊆ S) :
    Disjoint P.coveredSquares G.XSet ∧
      (c, G.X c) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
  have hcut := G.cutColumn_X_mem_toGridRectangle_coveredSquares C P
  have heq := hc _ ((G.mk_mem_XSet _ _).mpr rfl) (hsub hcut)
  refine ⟨Finset.disjoint_left.mpr fun {p} hp hX => ?_, heq ▸ hcut⟩
  obtain ⟨d, r⟩ := p
  -- A covered square lies outside both columns next to the replaced line, so in the rectangle.
  have hda : d ≠ a := fun h => P.mk_notMem_coveredSquares_left_column r (h ▸ hp)
  have hdb : d ≠ b := fun h => P.mk_notMem_coveredSquares_right_column r (h ▸ hp)
  have hrect := (P.mem_coveredSquares_iff_of_ne hda hdb).mp hp
  have hcol : d = P.cutColumn := (Prod.mk.inj ((hc _ hX (hsub hrect)).trans heq.symm)).1
  cases P with
  | inl P => exact hda (by rwa [GridCommutationHexagonBetween.cutColumn_inl] at hcol)
  | inr P => exact hdb (by rwa [GridCommutationHexagonBetween.cutColumn_inr] at hcol)

/-- A repartition of a counted composite into two empty rectangles, one of which underlies a
commutation hexagon, is the underlying rectangle decomposition of a counted composite. -/
theorem exists_toRectangleDecomposition_eq_of_isRepartition {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z) {E : GridRectangleDecomposition x z}
    (hrep : F.toRectangleDecomposition.IsRepartition E) (hfirst : E.first.IsEmpty)
    (hsecond : E.second.IsEmpty)
    (hhex : (∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow x E.middle,
        P.toGridRectangleBetween = E.first) ∨
      ∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow E.middle z,
        P.toGridRectangleBetween = E.second) :
    ∃ F' ∈ G.hexagonCompositeDecompositions C x z, F'.toRectangleDecomposition = E := by
  obtain ⟨c, hc⟩ := G.exists_eq_of_mem_XSet_of_mem_coveredSquares_union C hF
  rw [← hrep.coveredSquares_union_eq] at hc
  -- The piece without the hexagon misses the single `X`-marking, which the hexagon piece covers.
  have hdisj := Finset.disjoint_left.mp hrep.disjoint_coveredSquares_right
  rcases hhex with ⟨P, hP⟩ | ⟨P, hP⟩
  · obtain ⟨hPX, hcP⟩ := G.disjoint_XSet_and_mem_of_coveredSquares_subset C P hc
      (hP ▸ Finset.subset_union_left)
    refine ⟨Sum.inl ⟨E.middle, P, E.second⟩, ?_, ?_⟩
    · simp only [inl_mem_hexagonCompositeDecompositions, mem_hexagonRectangleDecompositions,
        mem_commutationHexagons, mem_unblockedRectangles]
      refine ⟨⟨hP ▸ hfirst, hPX⟩, hsecond, Finset.disjoint_left.mpr fun {p} hp hX => ?_⟩
      obtain rfl := hc p hX (Finset.mem_union_right _ hp)
      exact hdisj (hP ▸ hcP) hp
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        GridHexagonRectangleDecomposition.toRectangleDecomposition, hP]
  · obtain ⟨hPX, hcP⟩ := G.disjoint_XSet_and_mem_of_coveredSquares_subset C P hc
      (hP ▸ Finset.subset_union_right)
    refine ⟨Sum.inr ⟨E.middle, E.first, P⟩, ?_, ?_⟩
    · simp only [inr_mem_hexagonCompositeDecompositions, mem_rectangleHexagonDecompositions,
        mem_commutationHexagons, mem_unblockedRectangles]
      refine ⟨⟨hfirst, Finset.disjoint_left.mpr fun {p} hp hX => ?_⟩, hP ▸ hsecond, hPX⟩
      obtain rfl := hc p hX (Finset.mem_union_left _ hp)
      exact hdisj hp (hP ▸ hcP)
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        GridRectangleHexagonDecomposition.toRectangleDecomposition, hP]

/-! ### Hexagon shapes in a same-side recut -/

/-- An oriented rectangle has the shape of a commutation hexagon of `C`: its terminal side is the
replaced grid line, carrying the opposite turn row and above it the turn row, or its initial side
is the replaced grid line, carrying the turn row and above it the opposite turn row. -/
private def IsHexagonShape {u v : GridState n} (e : GridRectangleBetween u v) : Prop :=
  (e.right = b ∧ C.oppositeTurnRow ∈ Grid.cIco e.bottom e.top ∧
      C.turnRow ∈ Grid.cIoo C.oppositeTurnRow e.top) ∨
    (e.left = b ∧ C.turnRow ∈ Grid.cIco e.bottom e.top ∧
      C.oppositeTurnRow ∈ Grid.cIoo C.turnRow e.top)

/-- An oriented rectangle of hexagon shape underlies a commutation hexagon. -/
private theorem exists_of_isHexagonShape {u v : GridState n} {e : GridRectangleBetween u v}
    (he : G.IsHexagonShape C e) :
    ∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow u v,
      P.toGridRectangleBetween = e := by
  rcases he with ⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩
  · exact ⟨Sum.inl ⟨e, hr, hs, hs'⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inl _⟩
  · exact ⟨Sum.inr ⟨e, hl, hs, hs'⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inr _⟩

/-- The rectangle under the hexagon of a composite has hexagon shape. -/
private theorem isHexagonShape_first_or_isHexagonShape_second {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    G.IsHexagonShape C F.toRectangleDecomposition.first ∨
      G.IsHexagonShape C F.toRectangleDecomposition.second := by
  -- The composite is rewritten as a whole: its pieces have types depending on its middle state.
  rcases F with ⟨m, P | P, r⟩ | ⟨m, r, P | P⟩
  · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    dsimp only [GridHexagonRectangleDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact Or.inl (Or.inl ⟨P.right_eq, P.lower_mem, P.upper_mem⟩)
  · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    dsimp only [GridHexagonRectangleDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inr]
    exact Or.inl (Or.inr ⟨P.left_eq, P.lower_mem, P.upper_mem⟩)
  · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    dsimp only [GridRectangleHexagonDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact Or.inr (Or.inl ⟨P.right_eq, P.lower_mem, P.upper_mem⟩)
  · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    dsimp only [GridRectangleHexagonDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inr]
    exact Or.inr (Or.inr ⟨P.left_eq, P.lower_mem, P.upper_mem⟩)

/-- In the recut of two empty rectangles sharing their terminal side, a piece has hexagon shape
when one of the original rectangles has. -/
private theorem isHexagonShape_recut_of_right_eq_right {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hcommon : D.first.right = D.second.right)
    (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hD : G.IsHexagonShape C D.first ∨ G.IsHexagonShape C D.second) :
    G.IsHexagonShape C (D.recut hone hfirst hsecond).first ∨
      G.IsHexagonShape C (D.recut hone hfirst hsecond).second := by
  have hleft : D.first.left ≠ D.second.left := fun h =>
    D.sideColumns_ne_of_hasOneCommonSide hone (by
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, h, hcommon])
  -- The second rectangle lies directly below the first; their rows join at the first's bottom.
  obtain ⟨-, hrow⟩ := D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hleft hfirst hsecond
  have htop : D.second.top = D.first.bottom := by
    rw [GridRectangleBetween.top_def, GridRectangleBetween.bottom_def, ← hcommon]
    exact D.first.map_right
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hfirst hsecond
  obtain ⟨hfl, hsl⟩ := hdata.recut_sides
  unfold IsHexagonShape at hD ⊢
  rw [hfl, hsl]
  rcases hdata.recut_branch with ⟨hcol, -, -, hsr⟩ | ⟨hcol, -, hfr, -⟩
  · -- The first piece has the second rectangle's rows; the second spans both row intervals.
    obtain ⟨-, -, hfb, hft, hsb, hst⟩ :=
      D.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol hfirst hsecond
    rw [hfb, hft, hsb, hst, hsr]
    rcases hD with (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩) | (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩)
    · exact Or.inr (Or.inl ⟨hr, Grid.cIco_subset_of_mem_cIoo hrow hs, hs'⟩)
    · exact Or.inr (Or.inr ⟨hl, Grid.cIco_subset_of_mem_cIoo hrow hs, hs'⟩)
    · rw [htop] at hs hs'
      exact Or.inr (Or.inl ⟨hcommon.trans hr, Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hs hrow,
        Grid.mem_cIoo_of_mem_cIco_of_mem_cIoo hrow hs hs'⟩)
    · rw [htop] at hs hs'
      exact Or.inl (Or.inr ⟨hl, hs, hs'⟩)
  · -- The first piece spans both row intervals; the second has the first rectangle's rows.
    obtain ⟨-, -, hfb, hft, hsb, hst⟩ :=
      D.recut_geometry_of_right_eq_right_of_second_left_mem_cIoo hcommon hcol hfirst hsecond
    rw [hfb, hft, hsb, hst, hfr]
    rcases hD with (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩) | (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩)
    · exact Or.inl (Or.inl ⟨hr, Grid.cIco_subset_of_mem_cIoo hrow hs, hs'⟩)
    · exact Or.inr (Or.inr ⟨hl, hs, hs'⟩)
    · rw [htop] at hs hs'
      exact Or.inl (Or.inl ⟨hcommon.trans hr, Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hs hrow,
        Grid.mem_cIoo_of_mem_cIco_of_mem_cIoo hrow hs hs'⟩)
    · rw [htop] at hs hs'
      exact Or.inl (Or.inr ⟨hl, Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hs hrow,
        Grid.mem_cIoo_of_mem_cIco_of_mem_cIoo hrow hs hs'⟩)

/-- In the recut of two empty rectangles sharing their initial side, a piece has hexagon shape
when one of the original rectangles has. -/
private theorem isHexagonShape_recut_of_left_eq_left {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hcommon : D.first.left = D.second.left)
    (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hD : G.IsHexagonShape C D.first ∨ G.IsHexagonShape C D.second) :
    G.IsHexagonShape C (D.recut hone hfirst hsecond).first ∨
      G.IsHexagonShape C (D.recut hone hfirst hsecond).second := by
  have hright : D.first.right ≠ D.second.right := fun h =>
    D.sideColumns_ne_of_hasOneCommonSide hone (by
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, h, hcommon])
  -- The second rectangle lies directly above the first; their rows join at the first's top.
  obtain ⟨hcol, hrow⟩ := D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hright hfirst hsecond
  have hbottom := D.second_bottom_eq_first_top_of_left_eq_left hcommon
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hfirst hsecond
  obtain ⟨hfr, hsr⟩ := hdata.recut_sides
  unfold IsHexagonShape at hD ⊢
  rcases hcol with hcol | hcol
  · -- The first piece has the second rectangle's rows; the second spans both row intervals.
    obtain ⟨-, -, hsl, -⟩ :=
      D.recut_sides_of_left_eq_left_of_first_right_mem_cIoo hcommon hcol hfirst hsecond
    obtain ⟨hfb, hft⟩ := D.recut_first_bottom_top_of_left_eq_left_of_first_right_mem_cIoo
      hcommon hcol hfirst hsecond
    obtain ⟨hsb, hst⟩ := D.recut_second_bottom_top_of_left_eq_left_of_first_right_mem_cIoo
      hcommon hcol hfirst hsecond
    rw [hfr, hsr, hfb, hft, hsb, hst, hsl]
    rcases hD with (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩) | (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩)
    · exact Or.inr (Or.inl ⟨hr, Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hs hrow,
        Grid.mem_cIoo_of_mem_cIco_of_mem_cIoo hrow hs hs'⟩)
    · exact Or.inr (Or.inr ⟨hl, Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hs hrow,
        Grid.mem_cIoo_of_mem_cIco_of_mem_cIoo hrow hs hs'⟩)
    · rw [hbottom] at hs
      exact Or.inl (Or.inl ⟨hr, hs, hs'⟩)
    · rw [hbottom] at hs
      exact Or.inr (Or.inr ⟨hcommon.trans hl, Grid.cIco_subset_of_mem_cIoo hrow hs, hs'⟩)
  · -- The first piece spans both row intervals; the second has the first rectangle's rows.
    obtain ⟨hfl, -, -, -⟩ :=
      D.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hcol hfirst hsecond
    obtain ⟨hfb, hft⟩ :=
      D.recut_first_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hcol hfirst hsecond
    obtain ⟨hsb, hst⟩ :=
      D.recut_second_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hcol hfirst hsecond
    rw [hfr, hsr, hfb, hft, hsb, hst, hfl]
    rcases hD with (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩) | (⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩)
    · exact Or.inr (Or.inl ⟨hr, hs, hs'⟩)
    · exact Or.inl (Or.inr ⟨hl, Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hs hrow,
        Grid.mem_cIoo_of_mem_cIco_of_mem_cIoo hrow hs hs'⟩)
    · rw [hbottom] at hs
      exact Or.inl (Or.inl ⟨hr, Grid.cIco_subset_of_mem_cIoo hrow hs, hs'⟩)
    · rw [hbottom] at hs
      exact Or.inl (Or.inr ⟨hcommon.trans hl, Grid.cIco_subset_of_mem_cIoo hrow hs, hs'⟩)

/-! ### Same-side composites are paired -/

/-- The recut of a counted composite whose two rectangles share a side column with the same
orientation, initial for both or terminal for both, is the underlying rectangle decomposition of a
counted composite. -/
theorem exists_isRecut_of_hasSameSideOverlap {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z)
    (hsame : F.toRectangleDecomposition.HasSameSideOverlap) :
    ∃ F' ∈ G.hexagonCompositeDecompositions C x z,
      F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition := by
  obtain ⟨hfirst, hsecond⟩ := G.isEmpty_of_mem_hexagonCompositeDecompositions C hF
  obtain ⟨hone, hside⟩ := F.toRectangleDecomposition.hasSameSideOverlap_iff.mp hsame
  have hrecut := F.toRectangleDecomposition.isRecut_recut hone hfirst hsecond
  have hshape := G.isHexagonShape_first_or_isHexagonShape_second C F
  have hshape' : G.IsHexagonShape C (F.toRectangleDecomposition.recut hone hfirst hsecond).first ∨
      G.IsHexagonShape C (F.toRectangleDecomposition.recut hone hfirst hsecond).second := by
    rcases hside with hcommon | hcommon
    · exact G.isHexagonShape_recut_of_left_eq_left C _ hcommon hone hfirst hsecond hshape
    · exact G.isHexagonShape_recut_of_right_eq_right C _ hcommon hone hfirst hsecond hshape
  obtain ⟨F', hF', hF'E⟩ := G.exists_toRectangleDecomposition_eq_of_isRepartition C hF
    hrecut.isRepartition hrecut.isEmpty_first hrecut.isEmpty_second
    (hshape'.imp (G.exists_of_isHexagonShape C) (G.exists_of_isHexagonShape C))
  exact ⟨F', hF', hF'E ▸ hrecut⟩

/-- Off the diagonal, every unpaired hexagon composite has a mixed-side overlap: its two
rectangles share exactly one side column, initial for one and terminal for the other. -/
theorem hasMixedSideOverlap_of_mem_unpairedHexagonComposites {x z : GridState n} (hzx : z ≠ x)
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.unpairedHexagonComposites C x z) :
    F.toRectangleDecomposition.HasMixedSideOverlap := by
  obtain ⟨hF, hdisj, hnot⟩ := (G.mem_unpairedHexagonComposites C F).mp hF
  refine ((F.toRectangleDecomposition
    |>.not_hasDisjointSides_iff_sameSideOverlap_or_mixedSideOverlap_of_ne hzx).mp hdisj)
    |>.resolve_left fun hsame => ?_
  obtain ⟨F', hF', hrecut⟩ := G.exists_isRecut_of_hasSameSideOverlap C hF hsame
  exact hnot F' hF' hrecut

end TauCeti.GridDiagram
