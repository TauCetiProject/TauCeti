/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Decomposition
public import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty

/-!
# Diagonal hexagon--rectangle annuli

An empty hexagon and an empty rectangle returning to its source form a thin vertical
annulus. The horizontal alternative for returning rectangles is impossible: a hexagon
contains two ordered turn rows, whereas a thin horizontal annulus contains just one row.
The vertical annulus occupies the column cut away by the hexagon. Consequently the hexagon
carries no markings, and the returning rectangle carries neither marking of that column.
Every such domain is counted, with weight one.

The membership characterizations below apply in both composition orders and to both turn
sides. They remove the marking tests from the diagonal hexagon terms of the commutation
homotopy equation. The diagonal weighted sums are therefore the cardinalities of their
finite domain families, over any commutative semiring.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridHexagonBetween

variable {n : ℕ} {a s t : Fin n} {x y : GridState n}

/-- An empty returning hexagon--rectangle pair is precisely the thin vertical annulus
in the column removed by the terminal-side hexagon. -/
theorem isEmpty_and_isEmpty_iff (P : GridHexagonBetween a s t x y)
    (r : GridRectangleBetween y x) :
    P.IsEmpty ∧ r.IsEmpty ↔ r.left = P.left ∧ P.left = a := by
  rw [P.toGridRectangleBetween.isEmpty_and_isEmpty_iff r]
  have hnot : P.top ≠ finRotate n P.bottom := by
    intro h
    have hrows := Grid.cIco_eq_singleton_iff.mpr ⟨rfl, h, P.bottom_ne_top⟩
    have hs : s = P.bottom := by
      simpa only [← P.bottom_def, ← P.top_def, hrows, Finset.mem_singleton]
        using P.lower_mem
    have ht := P.upper_mem
    simp only [hs, ← P.top_def, h, Grid.cIoo_finRotate_eq_empty,
      Finset.notMem_empty] at ht
  constructor
  · rintro (⟨hl, hr⟩ | ⟨_, hr⟩)
    · exact ⟨hl, (finRotate n).injective (hr.symm.trans P.right_eq)⟩
    · exact False.elim (hnot hr)
  · rintro ⟨hl, ha⟩
    exact Or.inl ⟨hl, P.right_eq.trans (congrArg (finRotate n) ha.symm)⟩

/-- A terminal-side hexagon in an empty returning pair covers no marked squares. -/
theorem coveredSquares_eq_empty_of_isEmpty_and_isEmpty (P : GridHexagonBetween a s t x y)
    (r : GridRectangleBetween y x) (h : P.IsEmpty ∧ r.IsEmpty) :
    P.coveredSquares = ∅ := by
  have ha := ((P.isEmpty_and_isEmpty_iff r).mp h).2
  have hc := Grid.cIco_eq_singleton_iff.mpr
    ⟨ha, P.right_eq, by simpa only [ha] using P.left_ne_right⟩
  ext p
  simp only [Finset.notMem_empty, iff_false, mem_coveredSquares,
    GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    hc, Finset.mem_singleton]
  tauto

end GridHexagonBetween

namespace GridInitialHexagonBetween

variable {n : ℕ} {a s t : Fin n} {x y : GridState n}

/-- An empty returning pair with an initial-side hexagon is precisely the thin vertical
annulus in the column immediately after `a`. -/
theorem isEmpty_and_isEmpty_iff (P : GridInitialHexagonBetween a s t x y)
    (r : GridRectangleBetween y x) :
    P.IsEmpty ∧ r.IsEmpty ↔
      r.left = P.left ∧ P.right = finRotate n (finRotate n a) := by
  rw [P.toGridRectangleBetween.isEmpty_and_isEmpty_iff r]
  have hnot : P.top ≠ finRotate n P.bottom := by
    intro h
    have hrows := Grid.cIco_eq_singleton_iff.mpr ⟨rfl, h, P.bottom_ne_top⟩
    have hs : s = P.bottom := by
      simpa only [← P.bottom_def, ← P.top_def, hrows, Finset.mem_singleton]
        using P.lower_mem
    have ht := P.upper_mem
    simp only [hs, ← P.top_def, h, Grid.cIoo_finRotate_eq_empty,
      Finset.notMem_empty] at ht
  constructor
  · rintro (⟨hl, hr⟩ | ⟨_, hr⟩)
    · exact ⟨hl, P.left_eq ▸ hr⟩
    · exact False.elim (hnot hr)
  · rintro ⟨hl, hr⟩
    exact Or.inl ⟨hl, P.left_eq ▸ hr⟩

/-- An initial-side hexagon in an empty returning pair covers no marked squares. -/
theorem coveredSquares_eq_empty_of_isEmpty_and_isEmpty
    (P : GridInitialHexagonBetween a s t x y) (r : GridRectangleBetween y x)
    (h : P.IsEmpty ∧ r.IsEmpty) : P.coveredSquares = ∅ := by
  have hr := ((P.isEmpty_and_isEmpty_iff r).mp h).2
  have hc : Grid.cIco P.left P.right = {finRotate n a} :=
    Grid.cIco_eq_singleton_iff.mpr ⟨P.left_eq, hr, P.left_eq ▸ P.left_ne_right⟩
  ext p
  simp only [Finset.notMem_empty, iff_false, mem_coveredSquares,
    GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    hc, Finset.mem_singleton]
  tauto

end GridInitialHexagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- In a terminal-side hexagon annulus the returning rectangle avoids both marking states. -/
theorem disjoint_markings_returning_hexagon {x y : GridState n}
    (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y)
    (r : GridRectangleBetween y x) (h : P.IsEmpty ∧ r.IsEmpty) :
    Disjoint r.toGridRectangle.coveredSquares G.OSet ∧
      Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  have hg := (P.isEmpty_and_isEmpty_iff r).mp h
  have hc : Grid.cIco P.left P.right = {C.column} :=
    Grid.cIco_eq_singleton_iff.mpr
      ⟨hg.2, P.right_eq, by simpa only [hg.2] using P.left_ne_right⟩
  have hsquares := P.toGridRectangleBetween.coveredSquares_eq_product_of_left_eq_left r hg.1
  have hrows := Grid.disjoint_cIco_swap P.bottom P.top
  constructor
  · rw [hsquares, hc, Finset.disjoint_right]
    intro p hp hmem
    have hm := (G.mem_OSet p).mp hp
    have hcol := Finset.mem_singleton.mp (Finset.mem_product.mp hmem).1
    have hin := P.insert_cIco_subset_cIco_bottom_top C.O_column_below
    exact Finset.disjoint_left.mp hrows (by simpa [← hcol, hm] using hin)
      (Finset.mem_product.mp hmem).2
  · rw [hsquares, hc, Finset.disjoint_right]
    intro p hp hmem
    have hm := (G.mem_XSet p).mp hp
    have hcol := Finset.mem_singleton.mp (Finset.mem_product.mp hmem).1
    have hin := P.insert_cIco_subset_cIco_bottom_top C.X_column_below
    exact Finset.disjoint_left.mp hrows (by simpa [← hcol, hm] using hin)
      (Finset.mem_product.mp hmem).2

/-- In an initial-side hexagon annulus the returning rectangle avoids both marking states. -/
theorem disjoint_markings_returning_initialHexagon {x y : GridState n}
    (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y)
    (r : GridRectangleBetween y x) (h : P.IsEmpty ∧ r.IsEmpty) :
    Disjoint r.toGridRectangle.coveredSquares G.OSet ∧
      Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  have hg := (P.isEmpty_and_isEmpty_iff r).mp h
  have hc : Grid.cIco P.left P.right = {finRotate n C.column} :=
    Grid.cIco_eq_singleton_iff.mpr
      ⟨P.left_eq, hg.2, P.left_eq ▸ P.left_ne_right⟩
  have hsquares := P.toGridRectangleBetween.coveredSquares_eq_product_of_left_eq_left r hg.1
  have hrows := Grid.disjoint_cIco_swap P.bottom P.top
  constructor
  · rw [hsquares, hc, Finset.disjoint_right]
    intro p hp hmem
    have hm := (G.mem_OSet p).mp hp
    have hcol := Finset.mem_singleton.mp (Finset.mem_product.mp hmem).1
    have hin := P.insert_cIco_subset_cIco_bottom_top C.O_next_above
    exact Finset.disjoint_left.mp hrows (by simpa [← hcol, hm] using hin)
      (Finset.mem_product.mp hmem).2
  · rw [hsquares, hc, Finset.disjoint_right]
    intro p hp hmem
    have hm := (G.mem_XSet p).mp hp
    have hcol := Finset.mem_singleton.mp (Finset.mem_product.mp hmem).1
    have hin := P.insert_cIco_subset_cIco_bottom_top C.X_next_above
    exact Finset.disjoint_left.mp hrows (by simpa [← hcol, hm] using hin)
      (Finset.mem_product.mp hmem).2

private theorem returning_commutationHexagon_markings {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y)
    (r : GridRectangleBetween y x) (h : P.toGridRectangleBetween.IsEmpty ∧ r.IsEmpty) :
    P.coveredSquares = ∅ ∧ Disjoint r.toGridRectangle.coveredSquares G.OSet ∧
      Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  cases P with
  | inl P =>
    simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl,
      GridCommutationHexagonBetween.coveredSquares_inl] at h ⊢
    exact ⟨P.coveredSquares_eq_empty_of_isEmpty_and_isEmpty r h,
      G.disjoint_markings_returning_hexagon C P r h⟩
  | inr P =>
    simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr,
      GridCommutationHexagonBetween.coveredSquares_inr] at h ⊢
    exact ⟨P.coveredSquares_eq_empty_of_isEmpty_and_isEmpty r h,
      G.disjoint_markings_returning_initialHexagon C P r h⟩

/-- For a returning hexagon--rectangle pair, emptiness alone implies that both domains
are counted: marking avoidance is automatic. -/
theorem mem_commutationHexagons_and_mem_unblockedRectangles_iff {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y)
    (r : GridRectangleBetween y x) :
    P ∈ G.commutationHexagons C x y ∧ r ∈ G.unblockedRectangles y x ↔
      P.toGridRectangleBetween.IsEmpty ∧ r.IsEmpty := by
  constructor
  · rintro ⟨hP, hr⟩
    exact ⟨((G.mem_commutationHexagons C P).mp hP).1,
      ((G.mem_unblockedRectangles r).mp hr).1⟩
  · intro h
    obtain ⟨hs, _, hX⟩ := G.returning_commutationHexagon_markings C P r h
    exact ⟨(G.mem_commutationHexagons C P).mpr ⟨h.1, by simp [hs]⟩,
      (G.mem_unblockedRectangles r).mpr ⟨h.2, hX⟩⟩

/-- The diagonal hexagon--rectangle family consists exactly of empty returning pairs.
Use explicitly to remove marking tests; the general membership lemma is the simp normal form. -/
theorem mem_hexagonRectangleDecompositions_diagonal_iff {x : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x x) :
    D ∈ G.hexagonRectangleDecompositions C x x ↔
      D.hexagon.toGridRectangleBetween.IsEmpty ∧ D.rectangle.IsEmpty := by
  rw [G.mem_hexagonRectangleDecompositions C D,
    G.mem_commutationHexagons_and_mem_unblockedRectangles_iff C]

/-- The diagonal rectangle--hexagon family consists exactly of empty returning pairs.
Use explicitly to remove marking tests; the general membership lemma is the simp normal form. -/
theorem mem_rectangleHexagonDecompositions_diagonal_iff {x : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x x) :
    D ∈ G.rectangleHexagonDecompositions C x x ↔
      D.rectangle.IsEmpty ∧ D.hexagon.toGridRectangleBetween.IsEmpty := by
  rw [G.mem_rectangleHexagonDecompositions C D, and_comm,
    G.mem_commutationHexagons_and_mem_unblockedRectangles_iff C, and_comm]

variable (R : Type*) [CommSemiring R]

/-- Every empty returning hexagon--rectangle pair has weight one, since neither domain
contains an O-marking. This does not require characteristic two. -/
theorem commutationHexagonWeight_mul_OMonomial_eq_one_of_returning {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y)
    (r : GridRectangleBetween y x) (h : P.toGridRectangleBetween.IsEmpty ∧ r.IsEmpty) :
    G.commutationHexagonWeight C R P * G.OMonomial R r.toGridRectangle = 1 := by
  obtain ⟨hs, hO, _⟩ := G.returning_commutationHexagon_markings C P r h
  rw [G.commutationHexagonWeight_eq_prod_coveredSquares C R P, hs, Finset.prod_empty,
    G.OMonomial_eq_one_of_disjoint R hO, one_mul]

/-- Every counted diagonal hexagon--rectangle term has weight one. -/
@[simp]
theorem hexagonRectangleWeight_eq_one_of_diagonal {x : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x x)
    (hD : D ∈ G.hexagonRectangleDecompositions C x x) :
    G.hexagonRectangleWeight C R D = 1 := by
  rw [G.hexagonRectangleWeight_def C R D]
  exact G.commutationHexagonWeight_mul_OMonomial_eq_one_of_returning C R D.hexagon D.rectangle
    ((G.mem_hexagonRectangleDecompositions_diagonal_iff C D).mp hD)

/-- Every counted diagonal rectangle--hexagon term has weight one. -/
@[simp]
theorem rectangleHexagonWeight_eq_one_of_diagonal {x : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x x)
    (hD : D ∈ G.rectangleHexagonDecompositions C x x) :
    G.rectangleHexagonWeight C R D = 1 := by
  rw [G.rectangleHexagonWeight_def C R D, mul_comm]
  exact G.commutationHexagonWeight_mul_OMonomial_eq_one_of_returning C R D.hexagon D.rectangle
    ((G.mem_rectangleHexagonDecompositions_diagonal_iff C D).mp hD).symm

/-- The diagonal hexagon--rectangle weighted sum is the number of its counted annuli. -/
theorem sum_hexagonRectangleWeight_diagonal (x : GridState n) :
    ∑ D ∈ G.hexagonRectangleDecompositions C x x, G.hexagonRectangleWeight C R D =
      ((G.hexagonRectangleDecompositions C x x).card : MvPolynomial (Fin n) R) := by
  classical
  calc
    _ = ∑ _D ∈ G.hexagonRectangleDecompositions C x x, (1 : MvPolynomial (Fin n) R) :=
      Finset.sum_congr rfl fun D hD => G.hexagonRectangleWeight_eq_one_of_diagonal C R D hD
    _ = _ := by simp

/-- The diagonal rectangle--hexagon weighted sum is the number of its counted annuli. -/
theorem sum_rectangleHexagonWeight_diagonal (x : GridState n) :
    ∑ D ∈ G.rectangleHexagonDecompositions C x x, G.rectangleHexagonWeight C R D =
      ((G.rectangleHexagonDecompositions C x x).card : MvPolynomial (Fin n) R) := by
  classical
  calc
    _ = ∑ _D ∈ G.rectangleHexagonDecompositions C x x, (1 : MvPolynomial (Fin n) R) :=
      Finset.sum_congr rfl fun D hD => G.rectangleHexagonWeight_eq_one_of_diagonal C R D hD
    _ = _ := by simp

end GridDiagram

end TauCeti
