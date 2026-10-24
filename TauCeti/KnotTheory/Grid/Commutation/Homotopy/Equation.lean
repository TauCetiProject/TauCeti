/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Unpaired
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Mixed.Side
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry

/-!
# The homotopy equation of a grid commutation

Let `C` be a validated column commutation of a grid diagram `G`, with commutation map
`Φ : GC⁻(G) → GC⁻(G')`, reverse commutation map `Ψ : GC⁻(G') → GC⁻(G)` and hexagon-counting map
`H : GC⁻(G) → GC⁻(G)`. This file proves the homotopy equation

  `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ`

over every commutative semiring of characteristic two.

By the diagonal, disjoint, recut and pentagon-pair cancellations, the equation says that, off
the diagonal, every unpaired hexagon composite is the partner of a pentagon pair: either the recut
of a same-side pair, or the composite with the rectangles of a mixed-side pair. This is
`GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_sum_residual_eq_zero`.
An unpaired composite has a mixed-side overlap
(`GridDiagram.hasMixedSideOverlap_of_mem_unpairedHexagonComposites`), so its two rectangles lie
on opposite sides of their common column and have a common bottom row or a common top row. One
of them is the rectangle of a commutation hexagon, which has the replaced grid line `b` as a side
and contains both intersection rows.

* If the common column is `b`, the two rectangles are a pentagon for `C` followed by one for the
  reverse commutation, provided the non-hexagon rectangle contains its own intersection row. When
  it does not, the recut contains a piece of hexagon shape, so the composite would be paired.
* Otherwise, either a piece of the recut has hexagon shape, and again the composite would be
  paired, or the recut consists of two rectangles with common side `b` of the same orientation,
  each containing exactly one intersection row. These are the rectangles of a same-side pentagon
  pair.

In both cases the pentagons avoid every `X`-marking. Off the two commuted columns this holds
because the composite covers only the `X`-marking of the column its hexagon cuts away. In those
columns it holds because the markings lie in the bigons between the intersection rows and, when
the common column is `b`, because the non-hexagon rectangle misses the marking of the column the
hexagon does not cut away.

## Main results

* `TauCeti.GridDiagram.mem_sameSidePentagonPartners_or_mem_mixedSidePentagonPartners`: off the
  diagonal, every unpaired hexagon composite is a same-side or a mixed-side pentagon partner.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq`: the homotopy equation
  `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ` in characteristic two.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

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
underlies a counted pentagon when it covers no `X`-marking outside the two commuted columns and
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

/-- An empty rectangle with terminal side the replaced line, whose rows contain the opposite turn
row, underlies a counted pentagon of the reverse commutation when it covers no `X`-marking
outside the two commuted columns and the exchanged markings of those columns avoid the squares
the pentagon covers there. -/
private theorem exists_reversePentagon {u v : GridState n} (e : GridRectangleBetween u v)
    (he : e.IsEmpty) (hr : e.right = b) (ht : C.oppositeTurnRow ∈ Grid.cIco e.bottom e.top)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ e.toGridRectangle.coveredSquares)
    (hXa : G.X b ∉ Grid.cIoo C.oppositeTurnRow e.top)
    (hXb : G.X a ∉ Grid.cIco e.bottom C.oppositeTurnRow) :
    ∃ Q : GridPentagonBetween C.reverse.column C.reverse.turnRow u v,
      Q.toGridRectangleBetween = e ∧ Q ∈ (G.swapColumns a b).pentagons C.reverse u v := by
  refine ⟨⟨e, hr.trans (congrArg (finRotate n) C.reverse_column).symm, ?_⟩, rfl, ?_⟩
  · rw [C.reverse_turnRow, ← e.bottom_def, ← e.top_def]
    exact ht
  rw [mem_pentagons, GridPentagonBetween.disjoint_coveredSquares_XSet_iff]
  simp only [C.reverse_column, C.reverse_turnRow, swapColumns_X, GridState.swapColumns_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  refine ⟨he, fun c hca hc hXc => ?_, hXa, hXb⟩
  have hcb : c ≠ b := by
    rintro rfl
    exact Grid.right_notMem_cIco _ _ hc
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb] at hXc
  exact hX c hca hcb (e.mem_toGridRectangle_coveredSquares.mpr ⟨by rw [hr]; exact hc, hXc⟩)

/-- An empty rectangle with initial side the replaced line, whose rows contain the opposite turn
row, underlies a counted initial-side pentagon of the reverse commutation under the same
conditions on `X`-markings. -/
private theorem exists_reverseInitialPentagon {u v : GridState n} (e : GridRectangleBetween u v)
    (he : e.IsEmpty) (hl : e.left = b) (ht : C.oppositeTurnRow ∈ Grid.cIco e.bottom e.top)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ e.toGridRectangle.coveredSquares)
    (hXa : G.X b ∉ Grid.cIoo C.oppositeTurnRow e.top)
    (hXb : G.X a ∉ Grid.cIco e.bottom C.oppositeTurnRow) :
    ∃ Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow u v,
      Q.toGridRectangleBetween = e ∧ Q ∈ (G.swapColumns a b).initialPentagons C.reverse u v := by
  refine ⟨⟨e, hl.trans (congrArg (finRotate n) C.reverse_column).symm, ?_⟩, rfl, ?_⟩
  · rw [C.reverse_turnRow, ← e.bottom_def, ← e.top_def]
    exact ht
  rw [mem_initialPentagons, GridInitialPentagonBetween.disjoint_coveredSquares_XSet_iff]
  simp only [C.reverse_column, C.reverse_turnRow, swapColumns_X, GridState.swapColumns_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  refine ⟨he, fun c hcb hc hXc => ?_, hXa, hXb⟩
  have hca : c ≠ a := by
    rintro rfl
    exact (by simp : a ∉ Grid.cIco b e.right) hc
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb] at hXc
  exact hX c hca hcb (e.mem_toGridRectangle_coveredSquares.mpr ⟨by rw [hl]; exact hc, hXc⟩)

/-! ### Pentagon pairs from rectangle decompositions -/

/-- A decomposition into empty rectangles with common terminal side the replaced line, covering
no `X`-marking outside the two commuted columns, is that of a counted terminal--terminal pentagon
pair when the first rectangle contains the turn row but not the opposite one and the second the
opposite turn row but not the turn row. -/
private theorem exists_terminalTerminal {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hr1 : E.first.right = b)
    (hr2 : E.second.right = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (ht' : C.oppositeTurnRow ∉ Grid.cIco E.first.bottom E.first.top)
    (hs' : C.oppositeTurnRow ∈ Grid.cIco E.second.bottom E.second.top)
    (hs : C.turnRow ∉ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares) :
    ∃ D ∈ G.sameSidePentagonPairs C x z, D.toRectangleDecomposition = E := by
  obtain ⟨hPa, hPb⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco ht ht'
      C.X_column_below C.X_next_above
  obtain ⟨hQb, hQa⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hs' hs
      C.X_next_above C.X_column_below
  obtain ⟨P, hPe, hP⟩ := G.exists_pentagon C _ h1 hr1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reversePentagon C _ h2 hr2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inl P, .inl Q⟩, ?_, ?_⟩
  · rw [mem_sameSidePentagonPairs, mem_pentagonPairDecompositions]
    exact ⟨⟨(G.inl_mem_commutationPentagons C _).mpr hP,
      ((G.swapColumns a b).inl_mem_commutationPentagons C.reverse _).mpr hQ⟩, rfl⟩
  · simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl, hPe, hQe]

/-- The initial--initial counterpart of `exists_terminalTerminal`. -/
private theorem exists_initialInitial {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hl1 : E.first.left = b)
    (hl2 : E.second.left = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (ht' : C.oppositeTurnRow ∉ Grid.cIco E.first.bottom E.first.top)
    (hs' : C.oppositeTurnRow ∈ Grid.cIco E.second.bottom E.second.top)
    (hs : C.turnRow ∉ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares) :
    ∃ D ∈ G.sameSidePentagonPairs C x z, D.toRectangleDecomposition = E := by
  obtain ⟨hPa, hPb⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco ht ht'
      C.X_column_below C.X_next_above
  obtain ⟨hQb, hQa⟩ :=
    Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hs' hs
      C.X_next_above C.X_column_below
  obtain ⟨P, hPe, hP⟩ := G.exists_initialPentagon C _ h1 hl1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reverseInitialPentagon C _ h2 hl2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inr P, .inr Q⟩, ?_, ?_⟩
  · rw [mem_sameSidePentagonPairs, mem_pentagonPairDecompositions]
    exact ⟨⟨(G.inr_mem_commutationPentagons C _).mpr hP,
      ((G.swapColumns a b).inr_mem_commutationPentagons C.reverse _).mpr hQ⟩, rfl⟩
  · simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr, hPe, hQe]

/-- A decomposition into empty rectangles meeting along the replaced line, terminal for the
first and initial for the second, is that of a counted terminal--initial pentagon pair when the
first contains the turn row, the second the opposite turn row, neither covers an `X`-marking
outside the two commuted columns, and the markings of those columns avoid the pentagons. -/
private theorem exists_terminalInitial {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hr1 : E.first.right = b)
    (hl2 : E.second.left = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (hs' : C.oppositeTurnRow ∈ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares)
    (hPa : G.X a ∉ Grid.cIoo C.turnRow E.first.top)
    (hPb : G.X b ∉ Grid.cIco E.first.bottom C.turnRow)
    (hQb : G.X b ∉ Grid.cIoo C.oppositeTurnRow E.second.top)
    (hQa : G.X a ∉ Grid.cIco E.second.bottom C.oppositeTurnRow) :
    ∃ D ∈ G.mixedSidePentagonPairs C x z, D.toRectangleDecomposition = E := by
  obtain ⟨P, hPe, hP⟩ := G.exists_pentagon C _ h1 hr1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reverseInitialPentagon C _ h2 hl2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inl P, .inr Q⟩, ?_, ?_⟩
  · rw [mem_mixedSidePentagonPairs, mem_pentagonPairDecompositions]
    exact ⟨⟨(G.inl_mem_commutationPentagons C _).mpr hP,
      ((G.swapColumns a b).inr_mem_commutationPentagons C.reverse _).mpr hQ⟩, by simp⟩
  · simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr, hPe, hQe]

/-- The initial--terminal counterpart of `exists_terminalInitial`. -/
private theorem exists_initialTerminal {x z : GridState n} (E : GridRectangleDecomposition x z)
    (h1 : E.first.IsEmpty) (h2 : E.second.IsEmpty) (hl1 : E.first.left = b)
    (hr2 : E.second.right = b) (ht : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (hs' : C.oppositeTurnRow ∈ Grid.cIco E.second.bottom E.second.top)
    (hX1 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.first.toGridRectangle.coveredSquares)
    (hX2 : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ E.second.toGridRectangle.coveredSquares)
    (hPa : G.X a ∉ Grid.cIoo C.turnRow E.first.top)
    (hPb : G.X b ∉ Grid.cIco E.first.bottom C.turnRow)
    (hQb : G.X b ∉ Grid.cIoo C.oppositeTurnRow E.second.top)
    (hQa : G.X a ∉ Grid.cIco E.second.bottom C.oppositeTurnRow) :
    ∃ D ∈ G.mixedSidePentagonPairs C x z, D.toRectangleDecomposition = E := by
  obtain ⟨P, hPe, hP⟩ := G.exists_initialPentagon C _ h1 hl1 ht hX1 hPa hPb
  obtain ⟨Q, hQe, hQ⟩ := G.exists_reversePentagon C _ h2 hr2 hs' hX2 hQb hQa
  refine ⟨⟨E.middle, .inr P, .inl Q⟩, ?_, ?_⟩
  · rw [mem_mixedSidePentagonPairs, mem_pentagonPairDecompositions]
    exact ⟨⟨(G.inr_mem_commutationPentagons C _).mpr hP,
      ((G.swapColumns a b).inl_mem_commutationPentagons C.reverse _).mpr hQ⟩, by simp⟩
  · simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr, hPe, hQe]

/-! ### Hexagon pieces of recuts -/

/-- One of the two rectangles of a decomposition underlies a commutation hexagon. -/
private def HasHexagonPiece {x z : GridState n} (E : GridRectangleDecomposition x z) : Prop :=
  (∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow x E.middle,
      P.toGridRectangleBetween = E.first) ∨
    ∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow E.middle z,
      P.toGridRectangleBetween = E.second

/-- A first rectangle with terminal side the replaced line containing the opposite turn row and,
above it, the turn row underlies a commutation hexagon. -/
private theorem hasHexagonPiece_first_terminal {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hr : E.first.right = b)
    (hl : C.oppositeTurnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (hu : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow E.first.top) : G.HasHexagonPiece C E :=
  Or.inl ⟨.inl ⟨E.first, hr, hl, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inl _⟩

/-- A first rectangle with initial side the replaced line containing the turn row and, above it,
the opposite turn row underlies a commutation hexagon. -/
private theorem hasHexagonPiece_first_initial {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hl : E.first.left = b)
    (hlow : C.turnRow ∈ Grid.cIco E.first.bottom E.first.top)
    (hu : C.oppositeTurnRow ∈ Grid.cIoo C.turnRow E.first.top) : G.HasHexagonPiece C E :=
  Or.inl ⟨.inr ⟨E.first, hl, hlow, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inr _⟩

/-- The second-rectangle version of `hasHexagonPiece_first_terminal`. -/
private theorem hasHexagonPiece_second_terminal {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hr : E.second.right = b)
    (hl : C.oppositeTurnRow ∈ Grid.cIco E.second.bottom E.second.top)
    (hu : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow E.second.top) : G.HasHexagonPiece C E :=
  Or.inr ⟨.inl ⟨E.second, hr, hl, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inl _⟩

/-- The second-rectangle version of `hasHexagonPiece_first_initial`. -/
private theorem hasHexagonPiece_second_initial {x z : GridState n}
    (E : GridRectangleDecomposition x z) (hl : E.second.left = b)
    (hlow : C.turnRow ∈ Grid.cIco E.second.bottom E.second.top)
    (hu : C.oppositeTurnRow ∈ Grid.cIoo C.turnRow E.second.top) : G.HasHexagonPiece C E :=
  Or.inr ⟨.inr ⟨E.second, hl, hlow, hu⟩, GridCommutationHexagonBetween.toGridRectangleBetween_inr _⟩

/-- The recut of a counted composite whose recut underlies no counted composite has no piece
underlying a commutation hexagon. -/
private theorem not_hasHexagonPiece_of_isRecut {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z)
    (hnot : ∀ F' ∈ G.hexagonCompositeDecompositions C x z,
      ¬F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition)
    {E : GridRectangleDecomposition x z} (hE : F.toRectangleDecomposition.IsRecut E) :
    ¬G.HasHexagonPiece C E := fun hhex => by
  obtain ⟨F', hF', hF'E⟩ := G.exists_toRectangleDecomposition_eq_of_isRepartition C hF
    hE.isRepartition hE.isEmpty_first hE.isEmpty_second hhex
  exact hnot F' hF' (hF'E ▸ hE)

/-- A recut covers no `X`-marking outside the two commuted columns when the original
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

include hone h1 h2

/-- A terminal-side hexagon followed by a rectangle across the replaced line has the rectangles of
a counted terminal--initial pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_terminal_first
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E) (hcommon : D.first.right = D.second.left)
    (hr : D.first.right = b) (hlow : C.oppositeTurnRow ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow D.first.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = a) :
    ∃ D' ∈ G.mixedSidePentagonPairs C x z, D'.toRectangleDecomposition = D := by
  have hbot := D.second_bottom_eq_first_bottom_of_right_eq_left hcommon
  have hl : D.second.left = b := hcommon.symm.trans hr
  have hXb : G.X b ∉ Grid.cIco D.second.bottom D.second.top := fun h =>
    C.column_ne_next (hX b (Finset.mem_union_right _
      (D.second.mem_toGridRectangle_coveredSquares.mpr ⟨G.next_mem_cIco C _ hl, h⟩))).symm
  rw [hbot] at hXb
  by_cases hs : C.oppositeTurnRow ∈ Grid.cIco D.first.bottom D.second.top
  · obtain ⟨hPa, hQa⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup C.X_column_below
    exact G.exists_terminalInitial C D h1 h2 hr hl
      (Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)) (by rwa [hbot])
      (fun c ha _ h => ha (hX c (Finset.mem_union_left _ h)))
      (fun c ha _ h => ha (hX c (Finset.mem_union_right _ h))) hPa
      (Grid.notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hlow hup hs C.X_next_above hXb)
      (fun h => hXb (Grid.cIoo_subset_cIco_of_mem_cIco hs h)) (by rwa [hbot])
  · rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
      ⟨hrow, -, -, -, -, -, -, -, -⟩ | ⟨hrow, -, -, -, h2r, -, -, h2b, h2t⟩
    · exact (hs (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hlow hrow)).elim
    · refine (hfalse _ (D.isRecut_recut hone h1 h2)
        (G.hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow hrow hs
      · rw [h2t]
        exact hup

/-- A rectangle followed by an initial-side hexagon across the replaced line has the rectangles of
a counted terminal--initial pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_initial_second
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E) (hcommon : D.first.right = D.second.left)
    (hl : D.second.left = b) (hlow : C.turnRow ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : C.oppositeTurnRow ∈ Grid.cIoo C.turnRow D.second.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = b) :
    ∃ D' ∈ G.mixedSidePentagonPairs C x z, D'.toRectangleDecomposition = D := by
  have hbot := D.second_bottom_eq_first_bottom_of_right_eq_left hcommon
  have hr : D.first.right = b := hcommon.trans hl
  have hXa : G.X a ∉ Grid.cIco D.first.bottom D.first.top := fun h =>
    C.column_ne_next (hX a (Finset.mem_union_left _
      (D.first.mem_toGridRectangle_coveredSquares.mpr ⟨G.column_mem_cIco C _ hr, h⟩)))
  rw [hbot] at hlow
  by_cases hs : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
  · obtain ⟨hQb, hPb⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup C.X_next_above
    refine G.exists_terminalInitial C D h1 h2 hr hl hs ?_
      (fun c _ hb h => hb (hX c (Finset.mem_union_left _ h)))
      (fun c _ hb h => hb (hX c (Finset.mem_union_right _ h)))
      (fun h => hXa (Grid.cIoo_subset_cIco_of_mem_cIco hs h)) hPb hQb ?_
    · rw [hbot]
      exact Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
    · rw [hbot]
      exact Grid.notMem_cIco_of_mem_insert_cIco_of_notMem_cIco hlow hup hs C.X_column_below hXa
  · rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
      ⟨hrow, h1l, -, -, -, h1b, h1t, -, -⟩ | ⟨hrow, -, -, -, -, -, -, -, -⟩
    · refine (hfalse _ (D.isRecut_recut hone h1 h2)
        (G.hasHexagonPiece_first_initial C _ (h1l.trans hr) ?_ ?_)).elim
      · rw [h1b, h1t]
        exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow hrow hs
      · rw [h1t]
        exact hup
    · exact (hs (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hlow hrow)).elim

/-- An initial-side hexagon followed by a rectangle across the replaced line has the rectangles of
a counted initial--terminal pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_initial_first
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E) (hcommon : D.first.left = D.second.right)
    (hl : D.first.left = b) (hlow : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : C.oppositeTurnRow ∈ Grid.cIoo C.turnRow D.first.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = b) :
    ∃ D' ∈ G.mixedSidePentagonPairs C x z, D'.toRectangleDecomposition = D := by
  have htop := D.second_top_eq_first_top_of_left_eq_right hcommon
  have hr : D.second.right = b := hcommon.symm.trans hl
  have hXa : G.X a ∉ Grid.cIco D.second.bottom D.second.top := fun h =>
    C.column_ne_next (hX a (Finset.mem_union_right _
      (D.second.mem_toGridRectangle_coveredSquares.mpr ⟨G.column_mem_cIco C _ hr, h⟩)))
  rw [htop] at hXa
  by_cases hs : C.oppositeTurnRow ∈ Grid.cIco D.second.bottom D.first.top
  · obtain ⟨hQb, hPb⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup C.X_next_above
    exact G.exists_initialTerminal C D h1 h2 hl hr hlow (by rwa [htop])
      (fun c _ hb h => hb (hX c (Finset.mem_union_left _ h)))
      (fun c _ hb h => hb (hX c (Finset.mem_union_right _ h)))
      (Grid.notMem_cIoo_of_mem_insert_cIco_of_notMem_cIco hup hs C.X_column_below hXa) hPb
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
        (G.hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact hA
      · rw [h2t]
        exact hB

/-- A rectangle followed by a terminal-side hexagon across the replaced line has the rectangles of
a counted initial--terminal pentagon pair, provided its recut has no piece underlying a commutation
hexagon. -/
private theorem exists_mixed_of_terminal_second
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E) (hcommon : D.first.left = D.second.right)
    (hr : D.second.right = b) (hlow : C.oppositeTurnRow ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow D.second.top)
    (hX : ∀ c, (c, G.X c) ∈ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares → c = a) :
    ∃ D' ∈ G.mixedSidePentagonPairs C x z, D'.toRectangleDecomposition = D := by
  have htop := D.second_top_eq_first_top_of_left_eq_right hcommon
  have hl : D.first.left = b := hcommon.trans hr
  have hXb : G.X b ∉ Grid.cIco D.first.bottom D.first.top := fun h =>
    C.column_ne_next (hX b (Finset.mem_union_left _
      (D.first.mem_toGridRectangle_coveredSquares.mpr ⟨G.next_mem_cIco C _ hl, h⟩))).symm
  rw [htop] at hlow hup
  by_cases hs : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
  · obtain ⟨hPa, hQa⟩ :=
      Grid.notMem_cIoo_and_notMem_cIco_of_mem_insert_cIco_of_mem_cIoo hlow hup C.X_column_below
    refine G.exists_initialTerminal C D h1 h2 hl hr hs ?_
      (fun c ha _ h => ha (hX c (Finset.mem_union_left _ h)))
      (fun c ha _ h => ha (hX c (Finset.mem_union_right _ h))) hPa
      (fun h => hXb (Grid.cIco_subset_cIco_of_mem_cIco hs h)) ?_ hQa
    · rw [htop]
      exact hlow
    · rw [htop]
      exact Grid.notMem_cIoo_of_mem_insert_cIco_of_notMem_cIco hup hs C.X_next_above hXb
  · rcases (D.isRecutOfLeftEqRight_recut hcommon hone h1 h2).recut_geometry hone with
      ⟨hrow, -, h1r, -, -, h1b, h1t, -, -⟩ | ⟨hrow, -, -, -, -, -, -, -, -⟩
    · obtain ⟨hA, hB⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup
        (Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right
          (Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)) hrow hs)
      refine (hfalse _ (D.isRecut_recut hone h1 h2)
        (G.hasHexagonPiece_first_terminal C _ (h1r.trans hl) ?_ ?_)).elim
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

include hone h1 h2

/-- An initial-side hexagon followed by a rectangle meeting it away from the replaced line is the
recut of a counted initial--initial pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_initial_first
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.right = D.second.left)
    (hl : D.first.left = b) (hlow : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : C.oppositeTurnRow ∈ Grid.cIoo C.turnRow D.first.top) :
    ∃ D' ∈ G.sameSidePentagonPairs C x z, D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, -, -, h2l, -, -, -, h2b, h2t⟩ | ⟨hrow, h1l, -, h2l, -, h1b, h1t, h2b, h2t⟩
  · refine (hfalse _ hrecut (G.hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hlow
    · rw [h2t]
      exact hup
  by_cases hA : C.oppositeTurnRow ∈ Grid.cIco D.first.bottom D.second.top
  · obtain ⟨hA1, hA2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hA
    refine (hfalse _ hrecut (G.hasHexagonPiece_first_initial C _ (h1l.trans hl) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hA1
    · rw [h1t]
      exact hA2
  by_cases hB : C.turnRow ∈ Grid.cIco D.second.top D.first.top
  · refine (hfalse _ hrecut (G.hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hB
    · rw [h2t]
      exact hup
  have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
  obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
  obtain ⟨D', hD', hD'E⟩ := G.exists_initialInitial C _ hrecut.isEmpty_first
    hrecut.isEmpty_second (h1l.trans hl) (h2l.trans hl)
    (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hB)
    (by rw [h1b, h1t]; exact hA)
    (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hA)
    (by rw [h2b, h2t]; exact hB) hX1 hX2
  exact ⟨D', hD', by rw [hD'E]; exact hrecut.symm hone h1 h2⟩

/-- A rectangle followed by a terminal-side hexagon meeting it away from the replaced line is the
recut of a counted terminal--terminal pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_terminal_second
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.right = D.second.left)
    (hr : D.second.right = b) (hlow : C.oppositeTurnRow ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow D.second.top) :
    ∃ D' ∈ G.sameSidePentagonPairs C x z, D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rw [D.second_bottom_eq_first_bottom_of_right_eq_left hcommon] at hlow
  rcases (D.isRecutOfRightEqLeft_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, -, h1r, -, h2r, h1b, h1t, h2b, h2t⟩ | ⟨hrow, -, h1r, -, -, h1b, h1t, -, -⟩
  · by_cases hA : C.oppositeTurnRow ∈ Grid.cIco D.first.top D.second.top
    · refine (hfalse _ hrecut (G.hasHexagonPiece_first_terminal C _ (h1r.trans hr) ?_ ?_)).elim
      · rw [h1b, h1t]
        exact hA
      · rw [h1t]
        exact hup
    by_cases hB : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
    · obtain ⟨hB1, hB2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hB
      refine (hfalse _ hrecut (G.hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact hB1
      · rw [h2t]
        exact hB2
    have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
    obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
    obtain ⟨D', hD', hD'E⟩ := G.exists_terminalTerminal C _ hrecut.isEmpty_first
      hrecut.isEmpty_second (h1r.trans hr) (h2r.trans hr)
      (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hB)
      (by rw [h1b, h1t]; exact hA)
      (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hA)
      (by rw [h2b, h2t]; exact hB) hX1 hX2
    exact ⟨D', hD', by rw [hD'E]; exact hrecut.symm hone h1 h2⟩
  · refine (hfalse _ hrecut (G.hasHexagonPiece_first_terminal C _ (h1r.trans hr) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hlow
    · rw [h1t]
      exact hup

/-- A terminal-side hexagon followed by a rectangle meeting it away from the replaced line is the
recut of a counted terminal--terminal pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_terminal_first
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.left = D.second.right)
    (hr : D.first.right = b) (hlow : C.oppositeTurnRow ∈ Grid.cIco D.first.bottom D.first.top)
    (hup : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow D.first.top) :
    ∃ D' ∈ G.sameSidePentagonPairs C x z, D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rcases (D.isRecutOfLeftEqRight_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, -, -, -, h2r, -, -, h2b, h2t⟩ | ⟨hrow, -, h1r, -, h2r, h1b, h1t, h2b, h2t⟩
  · refine (hfalse _ hrecut (G.hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hlow
    · rw [h2t]
      exact hup
  by_cases hA : C.oppositeTurnRow ∈ Grid.cIco D.second.bottom D.first.top
  · refine (hfalse _ hrecut (G.hasHexagonPiece_first_terminal C _ (h1r.trans hr) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hA
    · rw [h1t]
      exact hup
  by_cases hB : C.turnRow ∈ Grid.cIco D.first.bottom D.second.bottom
  · obtain ⟨hB1, hB2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hB
    refine (hfalse _ hrecut (G.hasHexagonPiece_second_terminal C _ (h2r.trans hr) ?_ ?_)).elim
    · rw [h2b, h2t]
      exact hB1
    · rw [h2t]
      exact hB2
  have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
  obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
  obtain ⟨D', hD', hD'E⟩ := G.exists_terminalTerminal C _ hrecut.isEmpty_first
    hrecut.isEmpty_second (h1r.trans hr) (h2r.trans hr)
    (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hB)
    (by rw [h1b, h1t]; exact hA)
    (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hA)
    (by rw [h2b, h2t]; exact hB) hX1 hX2
  exact ⟨D', hD', by rw [hD'E]; exact hrecut.symm hone h1 h2⟩

/-- A rectangle followed by an initial-side hexagon meeting it away from the replaced line is the
recut of a counted initial--initial pentagon pair, provided its recut has no piece underlying a
commutation hexagon. -/
private theorem exists_sameSide_of_initial_second
    (hfalse : ∀ E, D.IsRecut E → ¬G.HasHexagonPiece C E)
    (hX : ∀ c, c ≠ a → c ≠ b → (c, G.X c) ∉ D.first.toGridRectangle.coveredSquares ∪
      D.second.toGridRectangle.coveredSquares) (hcommon : D.first.left = D.second.right)
    (hl : D.second.left = b) (hlow : C.turnRow ∈ Grid.cIco D.second.bottom D.second.top)
    (hup : C.oppositeTurnRow ∈ Grid.cIoo C.turnRow D.second.top) :
    ∃ D' ∈ G.sameSidePentagonPairs C x z, D'.toRectangleDecomposition.IsRecut D := by
  have hrecut := D.isRecut_recut hone h1 h2
  rw [D.second_top_eq_first_top_of_left_eq_right hcommon] at hlow hup
  rcases (D.isRecutOfLeftEqRight_recut hcommon hone h1 h2).recut_geometry hone with
    ⟨hrow, h1l, -, h2l, -, h1b, h1t, h2b, h2t⟩ | ⟨hrow, h1l, -, -, -, h1b, h1t, -, -⟩
  · by_cases hA : C.oppositeTurnRow ∈ Grid.cIco D.second.bottom D.first.bottom
    · obtain ⟨hA1, hA2⟩ := Grid.mem_cIco_and_mem_cIoo_of_mem_cIoo_of_mem_cIco hlow hup hA
      refine (hfalse _ hrecut (G.hasHexagonPiece_first_initial C _ (h1l.trans hl) ?_ ?_)).elim
      · rw [h1b, h1t]
        exact hA1
      · rw [h1t]
        exact hA2
    by_cases hB : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top
    · refine (hfalse _ hrecut (G.hasHexagonPiece_second_initial C _ (h2l.trans hl) ?_ ?_)).elim
      · rw [h2b, h2t]
        exact hB
      · rw [h2t]
        exact hup
    have hlow' := Grid.insert_cIco_subset_cIco hlow hup (Finset.mem_insert_self _ _)
    obtain ⟨hX1, hX2⟩ := G.notMem_of_isRecut C hrecut hX
    obtain ⟨D', hD', hD'E⟩ := G.exists_initialInitial C _ hrecut.isEmpty_first
      hrecut.isEmpty_second (h1l.trans hl) (h2l.trans hl)
      (by rw [h1b, h1t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_right hlow hrow hB)
      (by rw [h1b, h1t]; exact hA)
      (by rw [h2b, h2t]; exact Grid.mem_cIco_of_mem_cIco_of_notMem_cIco_left hlow' hrow hA)
      (by rw [h2b, h2t]; exact hB) hX1 hX2
    exact ⟨D', hD', by rw [hD'E]; exact hrecut.symm hone h1 h2⟩
  · refine (hfalse _ hrecut (G.hasHexagonPiece_first_initial C _ (h1l.trans hl) ?_ ?_)).elim
    · rw [h1b, h1t]
      exact hlow
    · rw [h1t]
      exact hup

end SameSide

/-! ### Exhausting the unpaired composites -/

/-- The rectangle of a terminal-side hexagon carrying no `X`-marking covers no `X`-marking outside
column `a`. -/
private theorem eq_of_mem_hexagon {u v : GridState n}
    {P : GridHexagonBetween a C.oppositeTurnRow C.turnRow u v}
    (hP : Disjoint P.coveredSquares G.XSet) {c : Fin n}
    (h : (c, G.X c) ∈ P.toGridRectangle.coveredSquares) : c = a := by
  have hmem : (c, G.X c) ∈ G.XSet ∩ P.toGridRectangle.coveredSquares :=
    Finset.mem_inter.mpr ⟨(G.mk_mem_XSet _ _).mpr rfl, h⟩
  rw [G.XSet_inter_toGridRectangle_coveredSquares_of_disjoint_hexagon hP] at hmem
  exact (Prod.mk.inj (Finset.mem_singleton.mp hmem)).1

/-- The rectangle of an initial-side hexagon carrying no `X`-marking covers no `X`-marking outside
column `b`. -/
private theorem eq_of_mem_initialHexagon {u v : GridState n}
    {P : GridInitialHexagonBetween a C.turnRow C.oppositeTurnRow u v}
    (hP : Disjoint P.coveredSquares G.XSet) {c : Fin n}
    (h : (c, G.X c) ∈ P.toGridRectangle.coveredSquares) : c = b := by
  have hmem : (c, G.X c) ∈ G.XSet ∩ P.toGridRectangle.coveredSquares :=
    Finset.mem_inter.mpr ⟨(G.mk_mem_XSet _ _).mpr rfl, h⟩
  rw [G.XSet_inter_toGridRectangle_coveredSquares_of_disjoint_initialHexagon hP] at hmem
  exact (Prod.mk.inj (Finset.mem_singleton.mp hmem)).1

/-- A counted rectangle covers no `X`-marking. -/
private theorem notMem_of_mem_unblockedRectangles {u v : GridState n}
    {S : GridRectangleBetween u v} (hS : S ∈ G.unblockedRectangles u v) (c : Fin n) :
    (c, G.X c) ∉ S.toGridRectangle.coveredSquares := fun h =>
  Finset.disjoint_left.mp ((G.mem_unblockedRectangles S).mp hS).2 h ((G.mk_mem_XSet _ _).mpr rfl)

/-- Off the diagonal, every unpaired hexagon composite is a pentagon partner: the recut of a
counted same-side pentagon pair, or the composite with the rectangles of a counted mixed-side
pentagon pair. -/
theorem mem_sameSidePentagonPartners_or_mem_mixedSidePentagonPartners {x z : GridState n}
    (hzx : z ≠ x) {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.unpairedHexagonComposites C x z) :
    F ∈ G.sameSidePentagonPartners C x z ∨ F ∈ G.mixedSidePentagonPartners C x z := by
  rw [mem_sameSidePentagonPartners, mem_mixedSidePentagonPartners]
  refine Or.imp (And.intro hF) (And.intro hF) ?_
  obtain ⟨hFc, -, hnot⟩ := (G.mem_unpairedHexagonComposites C F).mp hF
  obtain ⟨hone, hside⟩ := (GridRectangleDecomposition.hasMixedSideOverlap_iff _).mp
    (G.hasMixedSideOverlap_of_mem_unpairedHexagonComposites C hzx hF)
  obtain ⟨h1, h2⟩ := G.isEmpty_of_mem_hexagonCompositeDecompositions C hFc
  have hfalse : ∀ E, F.toRectangleDecomposition.IsRecut E → ¬G.HasHexagonPiece C E :=
    fun _ hE => G.not_hasHexagonPiece_of_isRecut C hFc hnot hE
  -- Split by the order of the hexagon and the rectangle and by the kind of hexagon; in each of
  -- the four cases, the orientation of the common side decides between the lemmas above.
  rcases F with ⟨m, H | H, S⟩ | ⟨m, S, H | H⟩
  · obtain ⟨hH, hS⟩ := (G.mem_hexagonRectangleDecompositions C _).mp
      ((G.inl_mem_hexagonCompositeDecompositions C _).mp hFc)
    simp only [GridHexagonRectangleDecomposition.hexagon, mem_commutationHexagons,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl,
      GridCommutationHexagonBetween.coveredSquares_inl] at hH
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hone hside h1 h2 hfalse ⊢
    simp only [GridHexagonRectangleDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ H.toGridRectangle.coveredSquares ∪
        S.toGridRectangle.coveredSquares → c = a := fun c hc =>
      (Finset.mem_union.mp hc).elim (G.eq_of_mem_hexagon C hH.2)
        fun h => (G.notMem_of_mem_unblockedRectangles hS c h).elim
    rcases hside with hcommon | hcommon
    · exact Or.inl (G.exists_sameSide_of_terminal_first C _ hone h1 h2 hfalse
        (fun c ha _ hc => ha (hX c hc)) hcommon H.right_eq H.lower_mem H.upper_mem)
    · exact Or.inr (G.exists_mixed_of_terminal_first C _ hone h1 h2 hfalse hcommon H.right_eq
        H.lower_mem H.upper_mem hX)
  · obtain ⟨hH, hS⟩ := (G.mem_hexagonRectangleDecompositions C _).mp
      ((G.inl_mem_hexagonCompositeDecompositions C _).mp hFc)
    simp only [GridHexagonRectangleDecomposition.hexagon, mem_commutationHexagons,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr,
      GridCommutationHexagonBetween.coveredSquares_inr] at hH
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hone hside h1 h2 hfalse ⊢
    simp only [GridHexagonRectangleDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ H.toGridRectangle.coveredSquares ∪
        S.toGridRectangle.coveredSquares → c = b := fun c hc =>
      (Finset.mem_union.mp hc).elim (G.eq_of_mem_initialHexagon C hH.2)
        fun h => (G.notMem_of_mem_unblockedRectangles hS c h).elim
    rcases hside with hcommon | hcommon
    · exact Or.inr (G.exists_mixed_of_initial_first C _ hone h1 h2 hfalse hcommon H.left_eq
        H.lower_mem H.upper_mem hX)
    · exact Or.inl (G.exists_sameSide_of_initial_first C _ hone h1 h2 hfalse
        (fun c _ hb hc => hb (hX c hc)) hcommon H.left_eq H.lower_mem H.upper_mem)
  · obtain ⟨hS, hH⟩ := (G.mem_rectangleHexagonDecompositions C _).mp
      ((G.inr_mem_hexagonCompositeDecompositions C _).mp hFc)
    simp only [GridRectangleHexagonDecomposition.hexagon, mem_commutationHexagons,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl,
      GridCommutationHexagonBetween.coveredSquares_inl] at hH
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hone hside h1 h2 hfalse ⊢
    simp only [GridRectangleHexagonDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ S.toGridRectangle.coveredSquares ∪
        H.toGridRectangle.coveredSquares → c = a := fun c hc =>
      (Finset.mem_union.mp hc).elim (fun h => (G.notMem_of_mem_unblockedRectangles hS c h).elim)
        (G.eq_of_mem_hexagon C hH.2)
    rcases hside with hcommon | hcommon
    · exact Or.inr (G.exists_mixed_of_terminal_second C _ hone h1 h2 hfalse hcommon H.right_eq
        H.lower_mem H.upper_mem hX)
    · exact Or.inl (G.exists_sameSide_of_terminal_second C _ hone h1 h2 hfalse
        (fun c ha _ hc => ha (hX c hc)) hcommon H.right_eq H.lower_mem H.upper_mem)
  · obtain ⟨hS, hH⟩ := (G.mem_rectangleHexagonDecompositions C _).mp
      ((G.inr_mem_hexagonCompositeDecompositions C _).mp hFc)
    simp only [GridRectangleHexagonDecomposition.hexagon, mem_commutationHexagons,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr,
      GridCommutationHexagonBetween.coveredSquares_inr] at hH
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hone hside h1 h2 hfalse ⊢
    simp only [GridRectangleHexagonDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hone hside h1 h2 hfalse ⊢
    have hX : ∀ c, (c, G.X c) ∈ S.toGridRectangle.coveredSquares ∪
        H.toGridRectangle.coveredSquares → c = b := fun c hc =>
      (Finset.mem_union.mp hc).elim (fun h => (G.notMem_of_mem_unblockedRectangles hS c h).elim)
        (G.eq_of_mem_initialHexagon C hH.2)
    rcases hside with hcommon | hcommon
    · exact Or.inl (G.exists_sameSide_of_initial_second C _ hone h1 h2 hfalse
        (fun c _ hb hc => hb (hX c hc)) hcommon H.left_eq H.lower_mem H.upper_mem)
    · exact Or.inr (G.exists_mixed_of_initial_second C _ hone h1 h2 hfalse hcommon H.left_eq
        H.lower_mem H.upper_mem hX)

/-- The homotopy equation `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ` of a column commutation, over any
commutative semiring of characteristic two: the hexagon-counting map `H` is a chain homotopy
between the identity of `GC⁻(G)` and the round trip through the commuted diagram. -/
theorem unblockedDifferential_commutationHomotopy_add_eq
    (R : Type*) [CommSemiring R] [CharP R 2] (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.commutationHomotopy R C c) +
        G.commutationHomotopy R C (G.unblockedDifferential R c) =
      c + (G.swapColumns a b).commutationMap R C.reverse (G.commutationMap R C c) :=
  (G.unblockedDifferential_commutationHomotopy_add_eq_iff_sum_residual_eq_zero C R).mpr
    (fun _ _ hzx => Finset.sum_eq_zero fun F hF => by
      simp only [Finset.mem_sdiff] at hF
      exact ((G.mem_sameSidePentagonPartners_or_mem_mixedSidePentagonPartners C hzx hF.1.1).elim
        hF.1.2 hF.2).elim) c

end TauCeti.GridDiagram
