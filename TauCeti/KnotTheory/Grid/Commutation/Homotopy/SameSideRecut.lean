/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Hexagon shapes in a same-side recut

A hexagon composite `F : GridHexagonCompositeDecomposition a s s' x z` is a commutation hexagon
followed by a rectangle, or a rectangle followed by a commutation hexagon. The left-hand sides of
the homotopy equations of a column commutation and of a crossing change both count such
composites, with different conditions on the markings. When the two rectangles of `F` are empty
and share exactly one side column, initial for both or terminal for both, the recut from the
proof of `∂² = 0` cuts their L-shaped union the other way. This file shows that one piece of
that recut again underlies a commutation hexagon for the same column and rows.

The recut keeps the outer sides of the original rectangles in the same position, and the rows of
each of its pieces are either the rows of the corresponding original rectangle or the union of
both row intervals. The replaced grid line is a side of the hexagon of `F`. If it is that
hexagon's outer side, the corresponding recut piece keeps it; if it is the common side, the recut
piece spanning both row intervals has it. In both cases the two turn rows remain on that side, in
the same order, so this piece has the shape of a commutation hexagon of the same kind.

Whether that hexagon is counted depends on the markings. Both homotopies count a hexagon exactly
when its rectangle is empty and carries only the `X`-marking of the column the hexagon cuts away,
which that rectangle always covers. For any family of hexagons counted this way, a counted
composite covers exactly one `X`-marking, so a repartition of its domain into two empty rectangles,
one of which underlies a hexagon, is again a counted composite; in particular so is the recut of a
same-side overlap. Each homotopy instantiates this with its own counted hexagons.

## Main results

* `TauCeti.GridHexagonCompositeDecomposition.exists_hexagon_of_isRecut`: for a hexagon composite
  whose two empty rectangles have a same-side overlap, one piece of its recut underlies a
  commutation hexagon.
* `TauCeti.GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff`: for a
  hexagon family counted by its markings, a repartition of a counted composite into empty
  rectangles, one of which underlies a hexagon, underlies a counted composite.
* `TauCeti.GridDiagram.exists_isRecut_of_hasSameSideOverlap_of_mem_iff`: for such a family, the
  recut of a counted composite with a same-side overlap underlies a counted composite.

## References

This is the same-side case of the hexagon--rectangle juxtaposition argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridHexagonCompositeDecomposition

variable {n : ℕ} {a s s' : Fin n}

/-- An oriented rectangle has the shape of a commutation hexagon for column `a`, turn row `s`
and opposite turn row `s'`: its terminal side is the replaced grid line, carrying `s'` and above
it `s`, or its initial side is the replaced grid line, carrying `s` and above it `s'`. -/
private def IsHexagonShape (a s s' : Fin n) {u v : GridState n} (e : GridRectangleBetween u v) :
    Prop :=
  (e.right = finRotate n a ∧ s' ∈ Grid.cIco e.bottom e.top ∧ s ∈ Grid.cIoo s' e.top) ∨
    (e.left = finRotate n a ∧ s ∈ Grid.cIco e.bottom e.top ∧ s' ∈ Grid.cIoo s e.top)

/-- An oriented rectangle of hexagon shape underlies a commutation hexagon. -/
private theorem exists_of_isHexagonShape {u v : GridState n} {e : GridRectangleBetween u v}
    (he : IsHexagonShape a s s' e) :
    ∃ P : GridCommutationHexagonBetween a s s' u v, P.toGridRectangleBetween = e := by
  rcases he with ⟨hr, hs, hs'⟩ | ⟨hl, hs, hs'⟩
  · exact ⟨Sum.inl ⟨e, hr, hs, hs'⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inl _⟩
  · exact ⟨Sum.inr ⟨e, hl, hs, hs'⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inr _⟩

/-- The rectangle under the hexagon of a composite has hexagon shape. -/
private theorem isHexagonShape_first_or_isHexagonShape_second {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a s s' x z) :
    IsHexagonShape a s s' F.toRectangleDecomposition.first ∨
      IsHexagonShape a s s' F.toRectangleDecomposition.second := by
  -- The composite is rewritten as a whole: its pieces have types depending on its middle state.
  rcases F with ⟨m, P | P, r⟩ | ⟨m, r, P | P⟩
  · rw [toRectangleDecomposition_inl]
    dsimp only [GridHexagonRectangleDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact Or.inl (Or.inl ⟨P.right_eq, P.lower_mem, P.upper_mem⟩)
  · rw [toRectangleDecomposition_inl]
    dsimp only [GridHexagonRectangleDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inr]
    exact Or.inl (Or.inr ⟨P.left_eq, P.lower_mem, P.upper_mem⟩)
  · rw [toRectangleDecomposition_inr]
    dsimp only [GridRectangleHexagonDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact Or.inr (Or.inl ⟨P.right_eq, P.lower_mem, P.upper_mem⟩)
  · rw [toRectangleDecomposition_inr]
    dsimp only [GridRectangleHexagonDecomposition.toRectangleDecomposition]
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inr]
    exact Or.inr (Or.inr ⟨P.left_eq, P.lower_mem, P.upper_mem⟩)

/-- In the recut of two empty rectangles sharing their terminal side, a piece has hexagon shape
when one of the original rectangles has. -/
private theorem isHexagonShape_recut_of_right_eq_right {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hcommon : D.first.right = D.second.right)
    (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hD : IsHexagonShape a s s' D.first ∨ IsHexagonShape a s s' D.second) :
    IsHexagonShape a s s' (D.recut hone hfirst hsecond).first ∨
      IsHexagonShape a s s' (D.recut hone hfirst hsecond).second := by
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
    (hD : IsHexagonShape a s s' D.first ∨ IsHexagonShape a s s' D.second) :
    IsHexagonShape a s s' (D.recut hone hfirst hsecond).first ∨
      IsHexagonShape a s s' (D.recut hone hfirst hsecond).second := by
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

/-- If the two rectangles of a hexagon composite are empty and share exactly one side column,
initial for both or terminal for both, then one piece of the recut of their union underlies a
commutation hexagon for the same column and rows. -/
theorem exists_hexagon_of_isRecut {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a s s' x z)
    (hsame : F.toRectangleDecomposition.HasSameSideOverlap)
    (hfirst : F.toRectangleDecomposition.first.IsEmpty)
    (hsecond : F.toRectangleDecomposition.second.IsEmpty) {E : GridRectangleDecomposition x z}
    (hE : F.toRectangleDecomposition.IsRecut E) :
    (∃ P : GridCommutationHexagonBetween a s s' x E.middle, P.toGridRectangleBetween = E.first) ∨
      ∃ P : GridCommutationHexagonBetween a s s' E.middle z,
        P.toGridRectangleBetween = E.second := by
  obtain ⟨hone, hside⟩ := F.toRectangleDecomposition.hasSameSideOverlap_iff.mp hsame
  obtain rfl := (F.toRectangleDecomposition.existsUnique_isRecut hone hfirst hsecond).unique hE
    (F.toRectangleDecomposition.isRecut_recut hone hfirst hsecond)
  have hshape := isHexagonShape_first_or_isHexagonShape_second F
  refine Or.imp exists_of_isHexagonShape exists_of_isHexagonShape ?_
  rcases hside with hcommon | hcommon
  · exact isHexagonShape_recut_of_left_eq_left _ hcommon hone hfirst hsecond hshape
  · exact isHexagonShape_recut_of_right_eq_right _ hcommon hone hfirst hsecond hshape

end TauCeti.GridHexagonCompositeDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} {G : GridDiagram n} {a s s' : Fin n}
  {H : ∀ u v : GridState n, Finset (GridCommutationHexagonBetween a s s' u v)}
  (hH : ∀ {u v : GridState n} (P : GridCommutationHexagonBetween a s s' u v),
    P ∈ H u v ↔ P.toGridRectangleBetween.IsEmpty ∧
      G.XSet ∩ P.toGridRectangleBetween.toGridRectangle.coveredSquares =
        {(P.cutColumn, G.X P.cutColumn)})
  (hcut : ∀ {u v : GridState n} (P : GridCommutationHexagonBetween a s s' u v),
    (P.cutColumn, G.X P.cutColumn) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares)

/-! ### Promoting a repartition to a counted composite

Both homotopies count a hexagon exactly when its rectangle is empty and carries only the
`X`-marking of its cut-away column, which that rectangle always covers. The argument below is
stated for any family of hexagons counted this way, with the composites counted as a counted
hexagon and an unblocked rectangle in either order. -/

include hH

/-- If a hexagon family is counted by its markings, every `X`-marking covered by a counted
composite is one and the same. -/
private theorem exists_eq_of_mem_XSet_of_mem_coveredSquares_union
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a s s' x z}
    (hF : F ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
      (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z)) :
    ∃ c : Fin n, ∀ p ∈ G.XSet,
      p ∈ F.toRectangleDecomposition.first.toGridRectangle.coveredSquares ∪
          F.toRectangleDecomposition.second.toGridRectangle.coveredSquares →
        p = (c, G.X c) := by
  have hhex {u v : GridState n} {P : GridCommutationHexagonBetween a s s' u v} (hP : P ∈ H u v)
      {p : Fin n × Fin n} (hXp : p ∈ G.XSet)
      (hp : p ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares) :
      p = (P.cutColumn, G.X P.cutColumn) := by
    have hmem := Finset.mem_inter.mpr ⟨hXp, hp⟩
    rw [((hH P).mp hP).2] at hmem
    exact Finset.mem_singleton.mp hmem
  cases F with
  | inl F =>
    obtain ⟨hP, hr⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ F).mp
      (Finset.inl_mem_disjSum.mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hXp hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hhex hP hXp hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hXp).elim
  | inr F =>
    obtain ⟨hr, hP⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ F).mp
      (Finset.inr_mem_disjSum.mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hXp hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hXp).elim
    · exact hhex hP hXp hp

include hcut in
/-- If a hexagon family is counted by its markings, a hexagon whose empty underlying rectangle lies
in a domain covering at most one `X`-marking is counted, and its underlying rectangle covers that
marking. -/
private theorem mem_and_mem_of_coveredSquares_subset
    {u v : GridState n} (P : GridCommutationHexagonBetween a s s' u v)
    (hempty : P.toGridRectangleBetween.IsEmpty)
    {S : Finset (Fin n × Fin n)} {c : Fin n} (hc : ∀ p ∈ G.XSet, p ∈ S → p = (c, G.X c))
    (hsub : P.toGridRectangleBetween.toGridRectangle.coveredSquares ⊆ S) :
    P ∈ H u v ∧ (c, G.X c) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
  have heq := hc _ ((G.mk_mem_XSet _ _).mpr rfl) (hsub (hcut P))
  refine ⟨(hH P).mpr ⟨hempty, ?_⟩, heq ▸ hcut P⟩
  ext p
  simp only [Finset.mem_inter, Finset.mem_singleton]
  exact ⟨fun ⟨hXp, hp⟩ => (hc p hXp (hsub hp)).trans heq.symm,
    fun h => h ▸ ⟨(G.mk_mem_XSet _ _).mpr rfl, hcut P⟩⟩

include hcut in
/-- For a hexagon family counted by its markings, a repartition of a counted composite into two
empty rectangles, one of which underlies a hexagon, is the underlying rectangle decomposition of a
counted composite. -/
theorem exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a s s' x z}
    (hF : F ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
      (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z))
    {E : GridRectangleDecomposition x z} (hrep : F.toRectangleDecomposition.IsRepartition E)
    (hfirst : E.first.IsEmpty) (hsecond : E.second.IsEmpty)
    (hhex : (∃ P : GridCommutationHexagonBetween a s s' x E.middle,
        P.toGridRectangleBetween = E.first) ∨
      ∃ P : GridCommutationHexagonBetween a s s' E.middle z,
        P.toGridRectangleBetween = E.second) :
    ∃ F' : GridHexagonCompositeDecomposition a s s' x z,
      F' ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z) ∧
      F'.toRectangleDecomposition = E := by
  obtain ⟨c, hc⟩ := exists_eq_of_mem_XSet_of_mem_coveredSquares_union hH hF
  rw [← hrep.coveredSquares_union_eq] at hc
  -- The piece without the hexagon misses the single `X`-marking, which the hexagon piece covers.
  have hdisj := Finset.disjoint_left.mp hrep.disjoint_coveredSquares_right
  rcases hhex with ⟨P, hP⟩ | ⟨P, hP⟩
  · obtain ⟨hPc, hcP⟩ := mem_and_mem_of_coveredSquares_subset hH hcut P (hP ▸ hfirst) hc
      (hP ▸ Finset.subset_union_left)
    refine ⟨Sum.inl ⟨E.middle, P, E.second⟩, ?_, ?_⟩
    · simp only [Finset.inl_mem_disjSum, GridTwoStepDecomposition.mem_decompositionsOf,
        mem_unblockedRectangles]
      refine ⟨hPc, hsecond, Finset.disjoint_left.mpr fun {p} hp hXp => ?_⟩
      obtain rfl := hc p hXp (Finset.mem_union_right _ hp)
      exact hdisj (hP ▸ hcP) hp
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        GridHexagonRectangleDecomposition.toRectangleDecomposition, hP]
  · obtain ⟨hPc, hcP⟩ := mem_and_mem_of_coveredSquares_subset hH hcut P (hP ▸ hsecond) hc
      (hP ▸ Finset.subset_union_right)
    refine ⟨Sum.inr ⟨E.middle, E.first, P⟩, ?_, ?_⟩
    · simp only [Finset.inr_mem_disjSum, GridTwoStepDecomposition.mem_decompositionsOf,
        mem_unblockedRectangles]
      refine ⟨⟨hfirst, Finset.disjoint_left.mpr fun {p} hp hXp => ?_⟩, hPc⟩
      obtain rfl := hc p hXp (Finset.mem_union_left _ hp)
      exact hdisj hp (hP ▸ hcP)
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        GridRectangleHexagonDecomposition.toRectangleDecomposition, hP]

include hcut in
/-- For a hexagon family counted by its markings, the recut of a counted composite whose two
rectangles share a side column with the same orientation, initial for both or terminal for both,
is the underlying rectangle decomposition of a counted composite. -/
theorem exists_isRecut_of_hasSameSideOverlap_of_mem_iff
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a s s' x z}
    (hF : F ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
      (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z))
    (hsame : F.toRectangleDecomposition.HasSameSideOverlap) :
    ∃ F' : GridHexagonCompositeDecomposition a s s' x z,
      F' ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z) ∧
      F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition := by
  have hempty : F.toRectangleDecomposition.first.IsEmpty ∧
      F.toRectangleDecomposition.second.IsEmpty := by
    cases F with
    | inl F =>
      obtain ⟨hP, hr⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ F).mp
        (Finset.inl_mem_disjSum.mp hF)
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
      exact ⟨((hH _).mp hP).1, G.isEmpty_of_mem_unblockedRectangles hr⟩
    | inr F =>
      obtain ⟨hr, hP⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ F).mp
        (Finset.inr_mem_disjSum.mp hF)
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
      exact ⟨G.isEmpty_of_mem_unblockedRectangles hr, ((hH _).mp hP).1⟩
  obtain ⟨hfirst, hsecond⟩ := hempty
  have hrecut := F.toRectangleDecomposition.isRecut_recut
    (F.toRectangleDecomposition.hasSameSideOverlap_iff.mp hsame).1 hfirst hsecond
  obtain ⟨F', hF', hF'E⟩ := exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff hH hcut
    hF hrecut.isRepartition hrecut.isEmpty_first hrecut.isEmpty_second
    (F.exists_hexagon_of_isRecut hsame hfirst hsecond hrecut)
  exact ⟨F', hF', hF'E ▸ hrecut⟩

end TauCeti.GridDiagram
