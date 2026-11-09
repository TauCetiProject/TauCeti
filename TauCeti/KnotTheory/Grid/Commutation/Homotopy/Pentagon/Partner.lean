/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.SameSideRecut
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry

/-!
# Unpaired hexagon composites are pentagon partners

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `s'` be a second row. The homotopy equations of a column commutation and of a
crossing change both compare a hexagon-counting map `H`, whose hexagons have corners in the rows
`s` and `s'`, with the round trip `Ψ ∘ Φ` of two pentagon-counting maps: `Φ` counts the pentagons
of `G` turning in row `s`, and `Ψ` those of `G' = G.swapColumns a b` at a column turn `C'` of the
same column `a` turning in row `s'`. After the cancellations on the left-hand side, what remains
of `∂ ∘ H + H ∘ ∂` off the diagonal are the counted hexagon composites whose recut underlies no
counted composite. Such a composite has a
mixed-side overlap, so its two rectangles lie on opposite sides of their common column. This file
shows that each of them is the partner of a counted pentagon pair: either the recut of a pair
whose pentagons turn on the same side of the replaced grid line `b`, or the composite with the
rectangles of a pair turning on opposite sides.

The argument is shared by both homotopies. It needs only that the hexagons are counted by their
markings, as in `TauCeti.GridDiagram.exists_isRecut_of_hasSameSideOverlap_of_mem_iff`, and that
the `X`-marking of column `a` lies in the rows from `s'` up to `s` and that of column `b` in the
rows from `s` up to `s'`. One of the two rectangles of the composite is the rectangle of its
hexagon, which has `b` as a side and contains both turn rows.

* If the common column is `b`, the two rectangles are a pentagon of `G` followed by one of `G'`,
  provided the non-hexagon rectangle contains its own turn row. When it does not, the recut
  contains a piece of hexagon shape, so the composite would be paired.
* Otherwise, either a piece of the recut has hexagon shape, and again the composite would be
  paired, or the recut consists of two rectangles with common side `b` of the same orientation,
  each containing exactly one turn row. These are the rectangles of a same-side pentagon pair.

In both cases the pentagons avoid every `X`-marking. Off the two exchanged columns this holds
because the composite covers only the `X`-marking of the column its hexagon cuts away. In those
columns it holds because of the positions of their `X`-markings relative to the turn rows and,
when the common column is `b`, because the non-hexagon rectangle misses the marking of the column
the hexagon does not cut away.

## Main results

* `TauCeti.GridDiagram.exists_pentagonPair_of_hasMixedSideOverlap_of_mem_iff`: a counted hexagon
  composite with a mixed-side overlap whose recut underlies no counted composite is the recut of a
  counted same-side pentagon pair, or has the rectangles of a counted mixed-side pentagon pair.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 5.1 and 6.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C C' : ColumnTurn n) {s' : Fin n}
  (hcol : C'.column = C.column) (hturn : C'.turnRow = s')
  (hXcol : G.X C.column ∈ insert C.turnRow (Grid.cIco s' C.turnRow))
  (hXnext : G.X (finRotate n C.column) ∈ insert s' (Grid.cIco C.turnRow s'))
  {H : ∀ u v : GridState n, Finset (GridCommutationHexagonBetween C.column C.turnRow s' u v)}
  (hH : ∀ {u v : GridState n} (P : GridCommutationHexagonBetween C.column C.turnRow s' u v),
    P ∈ H u v ↔ P.toGridRectangleBetween.IsEmpty ∧
      G.XSet ∩ P.toGridRectangleBetween.toGridRectangle.coveredSquares =
        {(P.cutColumn, G.X P.cutColumn)})
  (hcut : ∀ {u v : GridState n} (P : GridCommutationHexagonBetween C.column C.turnRow s' u v),
    (P.cutColumn, G.X P.cutColumn) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-- A pentagon pair is counted when its first pentagon is counted by the commutation map of `C`
and its second by the commutation map of `G.swapColumns a b` at `C'`. -/
private abbrev IsCountedPentagonPair {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z) : Prop :=
  D.first ∈ (G.pentagons C x D.middle).disjSum (G.initialPentagons C x D.middle) ∧
    D.second ∈ ((G.swapColumns a b).pentagons C' D.middle z).disjSum
      ((G.swapColumns a b).initialPentagons C' D.middle z)

/-! ### Promoting rectangles to counted pentagons -/

/-- The cut-away column of the replaced line lies in a rectangle with terminal side that line. -/
private theorem column_mem_cIco {u v : GridState n} (e : GridRectangleBetween u v)
    (hr : e.right = b) : a ∈ Grid.cIco e.left e.right := by
  rw [hr]
  exact Grid.self_mem_cIco_finRotate (hr ▸ e.left_ne_right)

/-- The column after the replaced line lies in a rectangle with initial side that line. -/
private theorem next_mem_cIco {u v : GridState n} (e : GridRectangleBetween u v)
    (hl : e.left = b) : b ∈ Grid.cIco e.left e.right := by
  rw [← hl]
  exact Grid.left_mem_cIco e.left_ne_right

/-- An empty rectangle with terminal side the replaced line, whose rows contain the turn row,
underlies a counted pentagon when it covers no `X`-marking outside the two exchanged columns and
the markings of those columns avoid the squares the pentagon covers there. -/
private theorem exists_pentagon {u v : GridState n} (e : GridRectangleBetween u v)
    (he : e.IsEmpty) (hr : e.right = b) (ht : C.turnRow ∈ Grid.cIco e.bottom e.top)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ e.toGridRectangle.coveredSquares)
    (hXa : G.X a ∉ Grid.cIoo C.turnRow e.top) (hXb : G.X b ∉ Grid.cIco e.bottom C.turnRow) :
    ∃ P : GridPentagonBetween a C.turnRow u v,
      P.toGridRectangleBetween = e ∧ P ∈ G.pentagons C u v := by
  refine ⟨⟨e, hr, ht⟩, rfl, (G.mem_pentagons _).mpr ⟨he,
    (GridPentagonBetween.disjoint_coveredSquares_XSet_iff _ G).mpr
      ⟨fun c hca hc hXc => hX c hca ?_ ?_, hXa, hXb⟩⟩⟩
  · rintro rfl
    exact Grid.right_notMem_cIco _ _ hc
  · exact e.mem_toGridRectangle_coveredSquares.mpr ⟨by rw [hr]; exact hc, hXc⟩

/-- An empty rectangle with initial side the replaced line, whose rows contain the turn row,
underlies a counted initial-side pentagon under the same conditions on `X`-markings. -/
private theorem exists_initialPentagon {u v : GridState n} (e : GridRectangleBetween u v)
    (he : e.IsEmpty) (hl : e.left = b) (ht : C.turnRow ∈ Grid.cIco e.bottom e.top)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ e.toGridRectangle.coveredSquares)
    (hXa : G.X a ∉ Grid.cIoo C.turnRow e.top) (hXb : G.X b ∉ Grid.cIco e.bottom C.turnRow) :
    ∃ P : GridInitialPentagonBetween a C.turnRow u v,
      P.toGridRectangleBetween = e ∧ P ∈ G.initialPentagons C u v := by
  refine ⟨⟨e, hl, ht⟩, rfl, (G.mem_initialPentagons _).mpr ⟨he,
    (GridInitialPentagonBetween.disjoint_coveredSquares_XSet_iff _ G).mpr
      ⟨fun c hcb hc hXc => hX c ?_ hcb ?_, hXa, hXb⟩⟩⟩
  · rintro rfl
    exact (by simp : a ∉ Grid.cIco b e.right) hc
  · exact e.mem_toGridRectangle_coveredSquares.mpr ⟨by rw [hl]; exact hc, hXc⟩

include hcol hturn in
/-- An empty rectangle with terminal side the replaced line, whose rows contain the second turn
row `s'`, underlies a counted pentagon of the exchanged diagram turning in row `s'` when it covers
no `X`-marking outside the two exchanged columns and the exchanged markings of those columns avoid
the squares the pentagon covers there. -/
private theorem exists_reversePentagon {u v : GridState n} (e : GridRectangleBetween u v)
    (he : e.IsEmpty) (hr : e.right = b) (ht : s' ∈ Grid.cIco e.bottom e.top)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ e.toGridRectangle.coveredSquares)
    (hXa : G.X b ∉ Grid.cIoo s' e.top)
    (hXb : G.X a ∉ Grid.cIco e.bottom s') :
    ∃ Q : GridPentagonBetween C'.column C'.turnRow u v,
      Q.toGridRectangleBetween = e ∧
        Q ∈ (G.swapColumns a b).pentagons C' u v := by
  refine ⟨⟨e, hr.trans (congrArg (finRotate n) hcol).symm, ?_⟩, rfl, ?_⟩
  · rw [hturn, ← e.bottom_def, ← e.top_def]
    exact ht
  rw [(G.swapColumns a b).mem_pentagons (C := C'),
    GridPentagonBetween.disjoint_coveredSquares_XSet_iff]
  simp only [hcol, hturn, swapColumns_X, GridState.swapColumns_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  refine ⟨he, fun c hca hc hXc => ?_, hXa, hXb⟩
  have hcb : c ≠ b := by
    rintro rfl
    exact Grid.right_notMem_cIco _ _ hc
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb] at hXc
  exact hX c hca hcb (e.mem_toGridRectangle_coveredSquares.mpr ⟨by rw [hr]; exact hc, hXc⟩)

include hcol hturn in
/-- An empty rectangle with initial side the replaced line, whose rows contain the second turn row
`s'`, underlies a counted initial-side pentagon of the exchanged diagram turning in row `s'` under
the same conditions on `X`-markings. -/
private theorem exists_reverseInitialPentagon {u v : GridState n} (e : GridRectangleBetween u v)
    (he : e.IsEmpty) (hl : e.left = b) (ht : s' ∈ Grid.cIco e.bottom e.top)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ e.toGridRectangle.coveredSquares)
    (hXa : G.X b ∉ Grid.cIoo s' e.top)
    (hXb : G.X a ∉ Grid.cIco e.bottom s') :
    ∃ Q : GridInitialPentagonBetween C'.column C'.turnRow u v,
      Q.toGridRectangleBetween = e ∧
        Q ∈ (G.swapColumns a b).initialPentagons C' u v := by
  refine ⟨⟨e, hl.trans (congrArg (finRotate n) hcol).symm, ?_⟩, rfl, ?_⟩
  · rw [hturn, ← e.bottom_def, ← e.top_def]
    exact ht
  rw [(G.swapColumns a b).mem_initialPentagons (C := C'),
    GridInitialPentagonBetween.disjoint_coveredSquares_XSet_iff]
  simp only [hcol, hturn, swapColumns_X, GridState.swapColumns_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  refine ⟨he, fun c hcb hc hXc => ?_, hXa, hXb⟩
  have hca : c ≠ a := by
    rintro rfl
    exact (by simp : a ∉ Grid.cIco b e.right) hc
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb] at hXc
  exact hX c hca hcb (e.mem_toGridRectangle_coveredSquares.mpr ⟨by rw [hl]; exact hc, hXc⟩)

/-! ### Pentagon pairs from rectangle decompositions -/

include hcol hturn hXcol hXnext in
/-- A decomposition into empty rectangles with common terminal side the replaced line, covering
no `X`-marking outside the two exchanged columns, is that of a counted terminal--terminal pentagon
pair when the first rectangle contains the turn row but not the second turn row `s'`, and the
second rectangle contains `s'` but not the turn row. -/
private theorem exists_terminalTerminal {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hr1 : E.first.right = b)
    (hr2 : E.second.right = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (ht' : s' ∉ Grid.cIco E.first.bottom E.first.top)
    (hs' : s' ∈ Grid.cIco E.second.bottom E.second.top)
    (hs : C.turnRow ∉ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares) :
    ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D ∧ D.first.isLeft = D.second.isLeft ∧
        D.toRectangleDecomposition = E := by
  obtain ⟨hPa, hPb⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco ht ht'
      hXcol hXnext
  obtain ⟨hQb, hQa⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hs' hs
      hXnext hXcol
  obtain ⟨P, hPe, hP⟩ := G.exists_pentagon C _ h1 hr1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reversePentagon C C' hcol hturn _ h2 hr2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inl P, .inl Q⟩, ⟨Finset.inl_mem_disjSum.mpr hP,
    Finset.inl_mem_disjSum.mpr hQ⟩, rfl, ?_⟩
  simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
    GridCommutationPentagonBetween.toGridRectangleBetween_inl, hPe, hQe]

include hcol hturn hXcol hXnext in
/-- The initial--initial counterpart of `exists_terminalTerminal`. -/
private theorem exists_initialInitial {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hl1 : E.first.left = b)
    (hl2 : E.second.left = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (ht' : s' ∉ Grid.cIco E.first.bottom E.first.top)
    (hs' : s' ∈ Grid.cIco E.second.bottom E.second.top)
    (hs : C.turnRow ∉ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares) :
    ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D ∧ D.first.isLeft = D.second.isLeft ∧
        D.toRectangleDecomposition = E := by
  obtain ⟨hPa, hPb⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco ht ht'
      hXcol hXnext
  obtain ⟨hQb, hQa⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hs' hs
      hXnext hXcol
  obtain ⟨P, hPe, hP⟩ := G.exists_initialPentagon C _ h1 hl1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reverseInitialPentagon C C' hcol hturn _ h2 hl2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inr P, .inr Q⟩, ⟨Finset.inr_mem_disjSum.mpr hP,
    Finset.inr_mem_disjSum.mpr hQ⟩, rfl, ?_⟩
  simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
    GridCommutationPentagonBetween.toGridRectangleBetween_inr, hPe, hQe]

include hcol hturn in
/-- A decomposition into empty rectangles meeting along the replaced line, terminal for the
first and initial for the second, is that of a counted terminal--initial pentagon pair when the
first contains the turn row, the second the second turn row `s'`, neither covers an `X`-marking
outside the two exchanged columns, and the markings of those columns avoid the pentagons. -/
private theorem exists_terminalInitial {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hr1 : E.first.right = b)
    (hl2 : E.second.left = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (hs' : s' ∈ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares)
    (hPa : G.X a ∉ Grid.cIoo C.turnRow E.first.top)
    (hPb : G.X b ∉ Grid.cIco E.first.bottom C.turnRow)
    (hQb : G.X b ∉ Grid.cIoo s' E.second.top)
    (hQa : G.X a ∉ Grid.cIco E.second.bottom s') :
    ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D ∧ D.first.isLeft ≠ D.second.isLeft ∧
        D.toRectangleDecomposition = E := by
  obtain ⟨P, hPe, hP⟩ := G.exists_pentagon C _ h1 hr1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reverseInitialPentagon C C' hcol hturn _ h2 hl2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inl P, .inr Q⟩, ⟨Finset.inl_mem_disjSum.mpr hP,
    Finset.inr_mem_disjSum.mpr hQ⟩, by simp, ?_⟩
  simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
    GridCommutationPentagonBetween.toGridRectangleBetween_inl,
    GridCommutationPentagonBetween.toGridRectangleBetween_inr, hPe, hQe]

include hcol hturn in
/-- The initial--terminal counterpart of `exists_terminalInitial`. -/
private theorem exists_initialTerminal {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hl1 : E.first.left = b)
    (hr2 : E.second.right = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (hs' : s' ∈ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares)
    (hPa : G.X a ∉ Grid.cIoo C.turnRow E.first.top)
    (hPb : G.X b ∉ Grid.cIco E.first.bottom C.turnRow)
    (hQb : G.X b ∉ Grid.cIoo s' E.second.top)
    (hQa : G.X a ∉ Grid.cIco E.second.bottom s') :
    ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D ∧ D.first.isLeft ≠ D.second.isLeft ∧
        D.toRectangleDecomposition = E := by
  obtain ⟨P, hPe, hP⟩ := G.exists_initialPentagon C _ h1 hl1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reversePentagon C C' hcol hturn _ h2 hr2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inr P, .inl Q⟩, ⟨Finset.inr_mem_disjSum.mpr hP,
    Finset.inl_mem_disjSum.mpr hQ⟩, by simp, ?_⟩
  simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
    GridCommutationPentagonBetween.toGridRectangleBetween_inl,
    GridCommutationPentagonBetween.toGridRectangleBetween_inr, hPe, hQe]

/-! ### Hexagon pieces of recuts -/

/-- One of the two rectangles of a decomposition underlies a commutation hexagon. -/
private def HasHexagonPiece (s' : Fin n) {x z : GridState n} (E : GridRectangleDecomposition x z) :
    Prop :=
  (∃ P : GridCommutationHexagonBetween a C.turnRow s' x E.middle,
      P.toGridRectangleBetween = E.first) ∨
    ∃ P : GridCommutationHexagonBetween a C.turnRow s' E.middle z,
      P.toGridRectangleBetween = E.second

/-- A first rectangle with terminal side the replaced line containing the second turn row `s'` and,
above it, the turn row underlies a commutation hexagon. -/
private theorem hasHexagonPiece_first_terminal {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hr : E.first.right = b)
    (hl : s' ∈ Grid.cIco E.first.bottom E.first.top)
    (hu : C.turnRow ∈ Grid.cIoo s' E.first.top) : HasHexagonPiece C s' E :=
  Or.inl ⟨.inl ⟨E.first, hr, hl, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inl _⟩

/-- A first rectangle with initial side the replaced line containing the turn row and, above it,
the second turn row `s'` underlies a commutation hexagon. -/
private theorem hasHexagonPiece_first_initial {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hl : E.first.left = b)
    (hlow : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (hu : s' ∈ Grid.cIoo C.turnRow E.first.top) : HasHexagonPiece C s' E :=
  Or.inl ⟨.inr ⟨E.first, hl, hlow, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inr _⟩

/-- The second-rectangle version of `hasHexagonPiece_first_terminal`. -/
private theorem hasHexagonPiece_second_terminal {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hr : E.second.right = b)
    (hl : s' ∈ Grid.cIco E.second.bottom E.second.top)
    (hu : C.turnRow ∈ Grid.cIoo s' E.second.top) : HasHexagonPiece C s' E :=
  Or.inr ⟨.inl ⟨E.second, hr, hl, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inl _⟩

/-- The second-rectangle version of `hasHexagonPiece_first_initial`. -/
private theorem hasHexagonPiece_second_initial {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hl : E.second.left = b)
    (hlow : C.turnRow ∈ Grid.cIco E.second.bottom E.second.top)
    (hu : s' ∈ Grid.cIoo C.turnRow E.second.top) : HasHexagonPiece C s' E :=
  Or.inr ⟨.inr ⟨E.second, hl, hlow, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inr _⟩

include hH hcut in
/-- The recut of a counted composite whose recut underlies no counted composite has no piece
underlying a commutation hexagon. -/
private theorem not_hasHexagonPiece_of_isRecut {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow s' x z}
    (hF : F ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
      (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z))
    (hnot : ∀ F' : GridHexagonCompositeDecomposition a C.turnRow s' x z,
      F' ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z) →
      ¬F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition)
    {E : GridRectangleDecomposition x z} (hE : F.toRectangleDecomposition.IsRecut E) :
    ¬HasHexagonPiece C s' E := fun hhex => by
  obtain ⟨F', hF', hF'E⟩ := exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff hH hcut
    hF hE.isRepartition hE.isEmpty_first hE.isEmpty_second hhex
  exact hnot F' hF' (hF'E ▸ hE)

/-- A recut covers no `X`-marking outside the two exchanged columns when the original
decomposition covers none. -/
private theorem notMem_of_isRecut {x z : GridState n} {D E : GridRectangleDecomposition x z}
    (hE : D.IsRecut E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) :
    (∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares) ∧
      ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares := by
  rw [← hE.isRepartition.coveredSquares_union_eq] at hX
  exact ⟨fun c ha hb h => hX c ha hb (Finset.mem_union_left _ h),
    fun c ha hb h => hX c ha hb (Finset.mem_union_right _ h)⟩

/-! ### Composites across the replaced line -/

section Mixed

variable {x z : GridState n} (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
  (h1 : D.first.IsEmpty) (h2 : D.second.IsEmpty)

include hcol hturn hXcol hXnext hone h1 h2

/-- A terminal-side hexagon followed by a rectangle across the replaced line has the rectangles of
a counted terminal--initial pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_terminal_first
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E) (hcommon : D.first.right = D.second.left)
    (hr : D.first.right = b) (hlow : s' ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : C.turnRow ∈ Grid.cIoo s' D.first.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = a) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft ≠ D'.second.isLeft ∧
        D'.toRectangleDecomposition = D := by
  have hbot := D.second_bottom_eq_first_bottom_of_right_eq_left hcommon
  have hl : D.second.left = b := hcommon.symm.trans hr
  have hXb : G.X b ∉ Grid.cIco D.second.bottom D.second.top := fun h =>
    C.column_ne_next (hX b (Finset.mem_union_right _
      (D.second.mem_toGridRectangle_coveredSquares.mpr ⟨next_mem_cIco C _ hl, h⟩))).symm
  rw [hbot] at hXb
  by_cases hs : s' ∈ Grid.cIco D.first.bottom D.second.top
  · obtain ⟨hPa, hQa⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup hXcol
    exact G.exists_terminalInitial C C' hcol hturn D h1 h2 hr hl
      (Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)) (by rwa [hbot])
      (fun c ha _ h => ha (hX c (Finset.mem_union_left _ h)))
      (fun c ha _ h => ha (hX c (Finset.mem_union_right _ h))) hPa
      (Grid.notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hlow hup hs hXnext hXb)
      (fun h => hXb (Grid.cIoo_subset_cIco_of_mem_cIco hs h)) (by rwa [hbot])
  · rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
      ⟨hrow, -, -, -, -, -, -, -, -⟩ | ⟨hrow, -, -, -, h2r, -, -, h2b, h2t⟩
    · exact (hs (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hlow hrow)).elim
    · refine (hfalse _ (D.isRecut_recut hone h1 h2)
        (hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow hrow hs
      · rw [h2t]
        exact hup

/-- A rectangle followed by an initial-side hexagon across the replaced line has the rectangles of
a counted terminal--initial pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_initial_second
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E) (hcommon : D.first.right = D.second.left)
    (hl : D.second.left = b) (hlow : C.turnRow ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : s' ∈ Grid.cIoo C.turnRow D.second.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = b) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft ≠ D'.second.isLeft ∧
        D'.toRectangleDecomposition = D := by
  have hbot := D.second_bottom_eq_first_bottom_of_right_eq_left hcommon
  have hr : D.first.right = b := hcommon.trans hl
  have hXa : G.X a ∉ Grid.cIco D.first.bottom D.first.top := fun h =>
    C.column_ne_next (hX a (Finset.mem_union_left _
      (D.first.mem_toGridRectangle_coveredSquares.mpr ⟨column_mem_cIco C _ hr, h⟩)))
  rw [hbot] at hlow
  by_cases hs : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
  · obtain ⟨hQb, hPb⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup hXnext
    refine G.exists_terminalInitial C C' hcol hturn D h1 h2 hr hl hs ?_
      (fun c _ hb h => hb (hX c (Finset.mem_union_left _ h)))
      (fun c _ hb h => hb (hX c (Finset.mem_union_right _ h)))
      (fun h => hXa (Grid.cIoo_subset_cIco_of_mem_cIco hs h)) hPb hQb ?_
    · rw [hbot]
      exact Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
    · rw [hbot]
      exact Grid.notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hlow hup hs hXcol hXa
  · rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
      ⟨hrow, h1l, -, -, -, h1b, h1t, -, -⟩ | ⟨hrow, -, -, -, -, -, -, -, -⟩
    · refine (hfalse _ (D.isRecut_recut hone h1 h2)
        (hasHexagonPiece_first_initial C _ (h1l.trans hr) ?_ ?_)).elim
      · rw [h1b, h1t]
        exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow hrow hs
      · rw [h1t]
        exact hup
    · exact (hs (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hlow hrow)).elim

/-- An initial-side hexagon followed by a rectangle across the replaced line has the rectangles of
a counted initial--terminal pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_initial_first
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E) (hcommon : D.first.left = D.second.right)
    (hl : D.first.left = b) (hlow : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : s' ∈ Grid.cIoo C.turnRow D.first.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = b) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft ≠ D'.second.isLeft ∧
        D'.toRectangleDecomposition = D := by
  have htop := D.second_top_eq_first_top_of_left_eq_right hcommon
  have hr : D.second.right = b := hcommon.symm.trans hl
  have hXa : G.X a ∉ Grid.cIco D.second.bottom D.second.top := fun h =>
    C.column_ne_next (hX a (Finset.mem_union_right _
      (D.second.mem_toGridRectangle_coveredSquares.mpr ⟨column_mem_cIco C _ hr, h⟩)))
  rw [htop] at hXa
  by_cases hs : s' ∈ Grid.cIco D.second.bottom D.first.top
  · obtain ⟨hQb, hPb⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup hXnext
    exact G.exists_initialTerminal C C' hcol hturn D h1 h2 hl hr hlow (by rwa [htop])
      (fun c _ hb h => hb (hX c (Finset.mem_union_left _ h)))
      (fun c _ hb h => hb (hX c (Finset.mem_union_right _ h)))
      (Grid.notMem_cIoo_of_mem_insert_cIco_of_notMem_cIco hup hs hXcol hXa) hPb
      (by rwa [htop])
      (fun h => hXa (Grid.cIco_subset_cIco_of_mem_cIco hs h))
  · rcases (D.isRecutOfLeftEqRight_recut hcommon hone h1 h2).recut_geometry hone with
      ⟨hrow, -, -, -, -, -, -, -, -⟩ | ⟨hrow, -, -, h2l, -, -, -, h2b, h2t⟩
    · exact (hs (Grid.cIco_subset_of_mem_cIoo hrow
        (Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)))).elim
    · obtain ⟨hA, hB⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup
        (Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right
          (Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)) hrow hs)
      refine (hfalse _ (D.isRecut_recut hone h1 h2)
        (hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact hA
      · rw [h2t]
        exact hB

/-- A rectangle followed by a terminal-side hexagon across the replaced line has the rectangles of
a counted initial--terminal pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_terminal_second
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E) (hcommon : D.first.left = D.second.right)
    (hr : D.second.right = b) (hlow : s' ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : C.turnRow ∈ Grid.cIoo s' D.second.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = a) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft ≠ D'.second.isLeft ∧
        D'.toRectangleDecomposition = D := by
  have htop := D.second_top_eq_first_top_of_left_eq_right hcommon
  have hl : D.first.left = b := hcommon.trans hr
  have hXb : G.X b ∉ Grid.cIco D.first.bottom D.first.top := fun h =>
    C.column_ne_next (hX b (Finset.mem_union_left _
      (D.first.mem_toGridRectangle_coveredSquares.mpr ⟨next_mem_cIco C _ hl, h⟩))).symm
  rw [htop] at hlow hup
  by_cases hs : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
  · obtain ⟨hPa, hQa⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup hXcol
    refine G.exists_initialTerminal C C' hcol hturn D h1 h2 hl hr hs ?_
      (fun c ha _ h => ha (hX c (Finset.mem_union_left _ h)))
      (fun c ha _ h => ha (hX c (Finset.mem_union_right _ h))) hPa
      (fun h => hXb (Grid.cIco_subset_cIco_of_mem_cIco hs h)) ?_ hQa
    · rw [htop]
      exact hlow
    · rw [htop]
      exact Grid.notMem_cIoo_of_mem_insert_cIco_of_notMem_cIco hup hs hXnext hXb
  · rcases (D.isRecutOfLeftEqRight_recut hcommon hone h1 h2).recut_geometry hone with
      ⟨hrow, -, h1r, -, -, h1b, h1t, -, -⟩ | ⟨hrow, -, -, -, -, -, -, -, -⟩
    · obtain ⟨hA, hB⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup
        (Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right
          (Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)) hrow hs)
      refine (hfalse _ (D.isRecut_recut hone h1 h2)
        (hasHexagonPiece_first_terminal C _ (h1r.trans hl) ?_ ?_)).elim
      · rw [h1b, h1t]
        exact hA
      · rw [h1t]
        exact hB
    · exact (hs (Grid.cIco_subset_of_mem_cIoo hrow
        (Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)))).elim

end Mixed

/-! ### Composites with a common column away from the replaced line -/

section SameSide

variable {x z : GridState n} (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
  (h1 : D.first.IsEmpty) (h2 : D.second.IsEmpty)

include hcol hturn hXcol hXnext hone h1 h2

/-- An initial-side hexagon followed by a rectangle meeting it away from the replaced line is the
recut of a counted initial--initial pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_initial_first
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.right = D.second.left)
    (hl : D.first.left = b) (hlow : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : s' ∈ Grid.cIoo C.turnRow D.first.top) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft = D'.second.isLeft ∧
        D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, -, -, h2l, -, -, -, h2b, h2t⟩ | ⟨hrow, h1l, -, h2l, -, h1b, h1t, h2b, h2t⟩
  · refine (hfalse _ hrecut (hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hlow
    · rw [h2t]
      exact hup
  by_cases hA : s' ∈ Grid.cIco D.first.bottom D.second.top
  · obtain ⟨hA1, hA2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hA
    refine (hfalse _ hrecut (hasHexagonPiece_first_initial C _ (h1l.trans hl) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hA1
    · rw [h1t]
      exact hA2
  by_cases hB : C.turnRow ∈ Grid.cIco D.second.top D.first.top
  · refine (hfalse _ hrecut (hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hB
    · rw [h2t]
      exact hup
  have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
  obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
  obtain ⟨D', hD', hside, hD'E⟩ := G.exists_initialInitial C C' hcol hturn hXcol hXnext _
    hrecut.isEmpty_first hrecut.isEmpty_second (h1l.trans hl) (h2l.trans hl)
    (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hB)
    (by rw [h1b, h1t]; exact hA)
    (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hA)
    (by rw [h2b, h2t]; exact hB) hX1 hX2
  exact ⟨D', hD', hside, by rw [hD'E]; exact hrecut.symm h1 h2⟩

/-- A rectangle followed by a terminal-side hexagon meeting it away from the replaced line is the
recut of a counted terminal--terminal pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_terminal_second
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.right = D.second.left)
    (hr : D.second.right = b) (hlow : s' ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : C.turnRow ∈ Grid.cIoo s' D.second.top) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft = D'.second.isLeft ∧
        D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rw [D.second_bottom_eq_first_bottom_of_right_eq_left hcommon] at hlow
  rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, -, h1r, -, h2r, h1b, h1t, h2b, h2t⟩ | ⟨hrow, -, h1r, -, -, h1b, h1t, -, -⟩
  · by_cases hA : s' ∈ Grid.cIco D.first.top D.second.top
    · refine (hfalse _ hrecut (hasHexagonPiece_first_terminal C _ (h1r.trans hr) ?_ ?_)).elim
      · rw [h1b, h1t]
        exact hA
      · rw [h1t]
        exact hup
    by_cases hB : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
    · obtain ⟨hB1, hB2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hB
      refine (hfalse _ hrecut (hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact hB1
      · rw [h2t]
        exact hB2
    have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
    obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
    obtain ⟨D', hD', hside, hD'E⟩ := G.exists_terminalTerminal C C' hcol hturn hXcol hXnext _
      hrecut.isEmpty_first hrecut.isEmpty_second (h1r.trans hr) (h2r.trans hr)
      (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hB)
      (by rw [h1b, h1t]; exact hA)
      (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hA)
      (by rw [h2b, h2t]; exact hB) hX1 hX2
    exact ⟨D', hD', hside, by rw [hD'E]; exact hrecut.symm h1 h2⟩
  · refine (hfalse _ hrecut (hasHexagonPiece_first_terminal C _ (h1r.trans hr) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hlow
    · rw [h1t]
      exact hup

/-- A terminal-side hexagon followed by a rectangle meeting it away from the replaced line is the
recut of a counted terminal--terminal pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_terminal_first
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.left = D.second.right)
    (hr : D.first.right = b) (hlow : s' ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : C.turnRow ∈ Grid.cIoo s' D.first.top) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft = D'.second.isLeft ∧
        D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rcases (D.isRecutOfLeftEqRight_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, -, -, -, h2r, -, -, h2b, h2t⟩ | ⟨hrow, -, h1r, -, h2r, h1b, h1t, h2b, h2t⟩
  · refine (hfalse _ hrecut (hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hlow
    · rw [h2t]
      exact hup
  by_cases hA : s' ∈ Grid.cIco D.second.bottom D.first.top
  · refine (hfalse _ hrecut (hasHexagonPiece_first_terminal C _ (h1r.trans hr) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hA
    · rw [h1t]
      exact hup
  by_cases hB : C.turnRow ∈ Grid.cIco D.first.bottom D.second.bottom
  · obtain ⟨hB1, hB2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hB
    refine (hfalse _ hrecut (hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hB1
    · rw [h2t]
      exact hB2
  have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
  obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
  obtain ⟨D', hD', hside, hD'E⟩ := G.exists_terminalTerminal C C' hcol hturn hXcol hXnext _
    hrecut.isEmpty_first hrecut.isEmpty_second (h1r.trans hr) (h2r.trans hr)
    (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hB)
    (by rw [h1b, h1t]; exact hA)
    (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hA)
    (by rw [h2b, h2t]; exact hB) hX1 hX2
  exact ⟨D', hD', hside, by rw [hD'E]; exact hrecut.symm h1 h2⟩

/-- A rectangle followed by an initial-side hexagon meeting it away from the replaced line is the
recut of a counted initial--initial pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_initial_second
    (hfalse : ∀ E, D.IsRecut E → ¬HasHexagonPiece C s' E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.left = D.second.right)
    (hl : D.second.left = b) (hlow : C.turnRow ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : s' ∈ Grid.cIoo C.turnRow D.second.top) :
    ∃ D' : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D' ∧ D'.first.isLeft = D'.second.isLeft ∧
        D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rw [D.second_top_eq_first_top_of_left_eq_right hcommon] at hlow hup
  rcases (D.isRecutOfLeftEqRight_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, h1l, -, h2l, -, h1b, h1t, h2b, h2t⟩ | ⟨hrow, h1l, -, -, -, h1b, h1t, -, -⟩
  · by_cases hA : s' ∈ Grid.cIco D.second.bottom D.first.bottom
    · obtain ⟨hA1, hA2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hA
      refine (hfalse _ hrecut (hasHexagonPiece_first_initial C _ (h1l.trans hl) ?_ ?_)).elim
      · rw [h1b, h1t]
        exact hA1
      · rw [h1t]
        exact hA2
    by_cases hB : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
    · refine (hfalse _ hrecut (hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact hB
      · rw [h2t]
        exact hup
    have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
    obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
    obtain ⟨D', hD', hside, hD'E⟩ := G.exists_initialInitial C C' hcol hturn hXcol hXnext _
      hrecut.isEmpty_first hrecut.isEmpty_second (h1l.trans hl) (h2l.trans hl)
      (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hB)
      (by rw [h1b, h1t]; exact hA)
      (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hA)
      (by rw [h2b, h2t]; exact hB) hX1 hX2
    exact ⟨D', hD', hside, by rw [hD'E]; exact hrecut.symm h1 h2⟩
  · refine (hfalse _ hrecut (hasHexagonPiece_first_initial C _ (h1l.trans hl) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hlow
    · rw [h1t]
      exact hup

end SameSide

/-! ### Exhausting the unpaired composites -/

include hH in
/-- The rectangle of a counted hexagon covers no `X`-marking outside the column it cuts away. -/
private theorem eq_cutColumn_of_mem {u v : GridState n}
    {P : GridCommutationHexagonBetween a C.turnRow s' u v} (hP : P ∈ H u v) {c : Fin n}
    (h : (c, G.X c) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares) :
    c = P.cutColumn := by
  have hmem := Finset.mem_inter.mpr ⟨(G.mk_mem_XSet _ _).mpr rfl, h⟩
  rw [((hH P).mp hP).2] at hmem
  exact (Prod.mk.inj (Finset.mem_singleton.mp hmem)).1

open GridHexagonCompositeDecomposition in
include hcol hturn hXcol hXnext hH hcut in
/-- The case of `exists_pentagonPair_of_hasMixedSideOverlap_of_mem_iff` in which the composite is a
hexagon followed by a rectangle. -/
private theorem exists_pentagonPair_of_hasMixedSideOverlap_of_inl {x z : GridState n}
    {F : GridHexagonRectangleDecomposition a C.turnRow s' x z}
    (hF : (Sum.inl F : GridHexagonCompositeDecomposition a C.turnRow s' x z) ∈
      (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z))
    (hnot : ∀ F' : GridHexagonCompositeDecomposition a C.turnRow s' x z,
      F' ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z) →
      ¬(toRectangleDecomposition (.inl F)).IsRecut F'.toRectangleDecomposition)
    (hmixed : (toRectangleDecomposition (.inl F)).HasMixedSideOverlap) :
    (∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D ∧ D.first.isLeft = D.second.isLeft ∧
        D.toRectangleDecomposition.IsRecut (toRectangleDecomposition (.inl F))) ∨
      ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
        G.IsCountedPentagonPair C C' D ∧ D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = toRectangleDecomposition (.inl F) := by
  obtain ⟨hone, hside⟩ := (GridRectangleDecomposition.hasMixedSideOverlap_iff _).mp hmixed
  obtain ⟨h1, h2⟩ := isEmpty_of_mem_disjSum_of_mem_iff hH hF
  have hfalse : ∀ E, (toRectangleDecomposition (.inl F)).IsRecut E → ¬HasHexagonPiece C s' E :=
    fun _ hE => G.not_hasHexagonPiece_of_isRecut C hH hcut hF hnot hE
  -- Split by the kind of hexagon; in each case, the orientation of the common side decides
  -- between the lemmas above.
  rcases F with ⟨m, P | P, S⟩
  · obtain ⟨hP, hS⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ _).mp
      (Finset.inl_mem_disjSum.mp hF)
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hone hside h1 h2 hfalse ⊢
    simp only [GridHexagonRectangleDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ P.toGridRectangle.coveredSquares ∪
        S.toGridRectangle.coveredSquares → c = a := fun c hc =>
      (Finset.mem_union.mp hc).elim (fun h => (G.eq_cutColumn_of_mem C hH (P := .inl P) hP
          (by rwa [GridCommutationHexagonBetween.toGridRectangleBetween_inl])).trans
          (GridCommutationHexagonBetween.cutColumn_inl P))
        fun h => (G.X_notMem_toGridRectangle_coveredSquares_of_mem_unblockedRectangles hS c h).elim
    rcases hside with hcommon | hcommon
    · exact Or.inl (G.exists_sameSide_of_terminal_first C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse (fun c ha _ hc => ha (hX c hc)) hcommon P.right_eq P.lower_mem P.upper_mem)
    · exact Or.inr (G.exists_mixed_of_terminal_first C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse hcommon P.right_eq P.lower_mem P.upper_mem hX)
  · obtain ⟨hP, hS⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ _).mp
      (Finset.inl_mem_disjSum.mp hF)
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hone hside h1 h2 hfalse ⊢
    simp only [GridHexagonRectangleDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ P.toGridRectangle.coveredSquares ∪
        S.toGridRectangle.coveredSquares → c = b := fun c hc =>
      (Finset.mem_union.mp hc).elim (fun h => (G.eq_cutColumn_of_mem C hH (P := .inr P) hP
          (by rwa [GridCommutationHexagonBetween.toGridRectangleBetween_inr])).trans
          (GridCommutationHexagonBetween.cutColumn_inr P))
        fun h => (G.X_notMem_toGridRectangle_coveredSquares_of_mem_unblockedRectangles hS c h).elim
    rcases hside with hcommon | hcommon
    · exact Or.inr (G.exists_mixed_of_initial_first C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse hcommon P.left_eq P.lower_mem P.upper_mem hX)
    · exact Or.inl (G.exists_sameSide_of_initial_first C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse (fun c _ hb hc => hb (hX c hc)) hcommon P.left_eq P.lower_mem P.upper_mem)

open GridHexagonCompositeDecomposition in
include hcol hturn hXcol hXnext hH hcut in
/-- The case of `exists_pentagonPair_of_hasMixedSideOverlap_of_mem_iff` in which the composite is a
rectangle followed by a hexagon. -/
private theorem exists_pentagonPair_of_hasMixedSideOverlap_of_inr {x z : GridState n}
    {F : GridRectangleHexagonDecomposition a C.turnRow s' x z}
    (hF : (Sum.inr F : GridHexagonCompositeDecomposition a C.turnRow s' x z) ∈
      (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z))
    (hnot : ∀ F' : GridHexagonCompositeDecomposition a C.turnRow s' x z,
      F' ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z) →
      ¬(toRectangleDecomposition (.inr F)).IsRecut F'.toRectangleDecomposition)
    (hmixed : (toRectangleDecomposition (.inr F)).HasMixedSideOverlap) :
    (∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D ∧ D.first.isLeft = D.second.isLeft ∧
        D.toRectangleDecomposition.IsRecut (toRectangleDecomposition (.inr F))) ∨
      ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
        G.IsCountedPentagonPair C C' D ∧ D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = toRectangleDecomposition (.inr F) := by
  obtain ⟨hone, hside⟩ := (GridRectangleDecomposition.hasMixedSideOverlap_iff _).mp hmixed
  obtain ⟨h1, h2⟩ := isEmpty_of_mem_disjSum_of_mem_iff hH hF
  have hfalse : ∀ E, (toRectangleDecomposition (.inr F)).IsRecut E → ¬HasHexagonPiece C s' E :=
    fun _ hE => G.not_hasHexagonPiece_of_isRecut C hH hcut hF hnot hE
  -- Split by the kind of hexagon; in each case, the orientation of the common side decides
  -- between the lemmas above.
  rcases F with ⟨m, S, P | P⟩
  · obtain ⟨hS, hP⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ _).mp
      (Finset.inr_mem_disjSum.mp hF)
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hone hside h1 h2 hfalse ⊢
    simp only [GridRectangleHexagonDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ S.toGridRectangle.coveredSquares ∪
        P.toGridRectangle.coveredSquares → c = a := fun c hc =>
      (Finset.mem_union.mp hc).elim
        (absurd · (G.X_notMem_toGridRectangle_coveredSquares_of_mem_unblockedRectangles hS c))
        (fun h => (G.eq_cutColumn_of_mem C hH (P := .inl P) hP
          (by rwa [GridCommutationHexagonBetween.toGridRectangleBetween_inl])).trans
          (GridCommutationHexagonBetween.cutColumn_inl P))
    rcases hside with hcommon | hcommon
    · exact Or.inr (G.exists_mixed_of_terminal_second C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse hcommon P.right_eq P.lower_mem P.upper_mem hX)
    · exact Or.inl (G.exists_sameSide_of_terminal_second C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse (fun c ha _ hc => ha (hX c hc)) hcommon P.right_eq P.lower_mem P.upper_mem)
  · obtain ⟨hS, hP⟩ := (GridTwoStepDecomposition.mem_decompositionsOf _ _ _).mp
      (Finset.inr_mem_disjSum.mp hF)
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hone hside h1 h2 hfalse ⊢
    simp only [GridRectangleHexagonDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ S.toGridRectangle.coveredSquares ∪
        P.toGridRectangle.coveredSquares → c = b := fun c hc =>
      (Finset.mem_union.mp hc).elim
        (absurd · (G.X_notMem_toGridRectangle_coveredSquares_of_mem_unblockedRectangles hS c))
        (fun h => (G.eq_cutColumn_of_mem C hH (P := .inr P) hP
          (by rwa [GridCommutationHexagonBetween.toGridRectangleBetween_inr])).trans
          (GridCommutationHexagonBetween.cutColumn_inr P))
    rcases hside with hcommon | hcommon
    · exact Or.inl (G.exists_sameSide_of_initial_second C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse (fun c _ hb hc => hb (hX c hc)) hcommon P.left_eq P.lower_mem P.upper_mem)
    · exact Or.inr (G.exists_mixed_of_initial_second C C' hcol hturn hXcol hXnext _ hone h1 h2
        hfalse hcommon P.left_eq P.lower_mem P.upper_mem hX)

include hcol hturn hXcol hXnext hH hcut in
/-- **Unpaired composites are pentagon partners.** Let the `X`-marking of column `a` lie in the
rows from `s'` up to the turn row `s` of `C`, and that of column `b` in the rows from `s` up to
`s'`, and let the hexagons with corners in the rows `s` and `s'` be counted by their markings. A
counted hexagon composite with a mixed-side overlap whose recut underlies no counted composite is
then the partner of a pentagon pair, made of a counted pentagon of `G` turning in row `s` and a
counted pentagon of `G.swapColumns a b` at a column turn `C'` of the column `a` turning in row
`s'`: either both pentagons turn on the same side of the replaced grid line and the pair recuts
the composite, or they turn on opposite sides and the pair has the rectangles of the composite. -/
theorem exists_pentagonPair_of_hasMixedSideOverlap_of_mem_iff {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow s' x z}
    (hF : F ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
      (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z))
    (hnot : ∀ F' : GridHexagonCompositeDecomposition a C.turnRow s' x z,
      F' ∈ (GridTwoStepDecomposition.decompositionsOf H G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles H x z) →
      ¬F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition)
    (hmixed : F.toRectangleDecomposition.HasMixedSideOverlap) :
    ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      (D.first ∈ (G.pentagons C x D.middle).disjSum (G.initialPentagons C x D.middle) ∧
        D.second ∈ ((G.swapColumns a b).pentagons C' D.middle z).disjSum
          ((G.swapColumns a b).initialPentagons C' D.middle z)) ∧
      (D.first.isLeft = D.second.isLeft ∧
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∨
        D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = F.toRectangleDecomposition) := by
  suffices h : (∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
      G.IsCountedPentagonPair C C' D ∧ D.first.isLeft = D.second.isLeft ∧
        D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition) ∨
      ∃ D : GridPentagonPairDecomposition a C.turnRow C'.column C'.turnRow x z,
        G.IsCountedPentagonPair C C' D ∧ D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = F.toRectangleDecomposition by
    rcases h with ⟨D, hD, hside, hD'⟩ | ⟨D, hD, hside, hD'⟩
    exacts [⟨D, hD, Or.inl ⟨hside, hD'⟩⟩, ⟨D, hD, Or.inr ⟨hside, hD'⟩⟩]
  rcases F with F | F
  · exact G.exists_pentagonPair_of_hasMixedSideOverlap_of_inl C C' hcol hturn hXcol hXnext hH hcut
      hF hnot hmixed
  · exact G.exists_pentagonPair_of_hasMixedSideOverlap_of_inr C C' hcol hturn hXcol hXnext hH hcut
      hF hnot hmixed

end TauCeti.GridDiagram
