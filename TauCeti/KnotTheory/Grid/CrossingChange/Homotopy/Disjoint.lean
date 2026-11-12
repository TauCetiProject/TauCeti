/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Decomposition
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Disjoint

/-!
# Cancelling disjoint terms of the crossing change homotopy equation

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row. On the left-hand side `∂ ∘ H + H ∘ ∂` of the crossing
change homotopy equation, a counted hexagon followed by a counted rectangle and a counted
rectangle followed by a counted hexagon contribute to the same coefficient. If the two pairs of
vertical sides are disjoint, the underlying rectangles can be applied in the opposite order
(`TauCeti.GridHexagonRectangleDecomposition.commute`). The toroidal domains are unchanged, so the
hexagon keeps its shape, the squares it covers as a hexagon of a crossing change, and its weight.
In characteristic two the two disjoint-side sums cancel, so only composite domains whose
rectangles share a vertical side remain.

Together with the diagonal of the equation
(`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_single_apply_self`), this reduces
the crossing change homotopy equation

  `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ`,

with `w` the annulus weight `GridDiagram.crossingChangeAnnulusWeight`, to an identity between
the composite domains sharing a side and the products of pentagon coefficients, between distinct
grid states. For interleaving columns, with `s` and `t` the rows of the turn points of the
crossing change maps, `w` is the variable of one of the two columns.

## Main results

* `TauCeti.GridDiagram.crossingChangeHexagonRectangleWeight_commute` and
  `TauCeti.GridDiagram.crossingChangeRectangleHexagonWeight_commute`: reordering a disjoint
  composite domain gives a counted composite domain of the same weight.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_overlap`: in
  characteristic two, the equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ`, for any polynomial `w`, is its
  coefficient identity restricted to composite domains whose rectangles share a vertical side.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne`: if the turn
  rows differ and the annulus squares carry no `X`-marking, the equation with `w` the annulus
  weight is equivalent to its off-diagonal identity between composite domains sharing a side and
  pentagon coefficient products.
* `unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne_of_mem_columnArc` and
  `unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne_of_notMem_columnArc`, in the
  namespace `TauCeti.GridDiagram`: the same for the crossing change maps of interleaving columns,
  with `w` the variable `V_b`, respectively `V_a`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the juxtaposition argument for the hexagon
  homotopies of commutation and of a crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti

namespace GridRectangleHexagonDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Reordering a disjoint rectangle--hexagon domain preserves the squares its hexagon covers as a
hexagon of a crossing change. -/
@[simp]
theorem commute_hexagon_crossingCoveredSquares (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).first.crossingCoveredSquares = D.second.crossingCoveredSquares := by
  refine GridCommutationHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq _ _ ?_
  have he := congrArg (fun E : GridRectangleDecomposition x z => E.first.toGridRectangle)
    (D.commute_toRectangleDecomposition h)
  exact he.trans (D.toRectangleDecomposition.commute_first_toGridRectangle h)

end GridRectangleHexagonDecomposition

namespace GridHexagonRectangleDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Reordering a disjoint hexagon--rectangle domain preserves the squares its hexagon covers as a
hexagon of a crossing change. -/
@[simp]
theorem commute_hexagon_crossingCoveredSquares (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).second.crossingCoveredSquares = D.first.crossingCoveredSquares := by
  refine GridCommutationHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq _ _ ?_
  have he := congrArg (fun E : GridRectangleDecomposition x z => E.second.toGridRectangle)
    (D.commute_toRectangleDecomposition h)
  exact he.trans (D.toRectangleDecomposition.commute_second_toGridRectangle h)

end GridHexagonRectangleDecomposition

namespace GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-- Reordering a counted disjoint rectangle--hexagon domain of the crossing change homotopy gives
a counted hexagon--rectangle domain. -/
theorem commute_mem_crossingChangeHexagonRectangleDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z) :
    D.commute h ∈ G.crossingChangeHexagonRectangleDecompositions C t x z := by
  obtain ⟨hr, hP⟩ := (G.mem_crossingChangeRectangleHexagonDecompositions C t D).mp hD
  obtain ⟨hrEmpty, hrX⟩ := (G.mem_unblockedRectangles _).mp hr
  obtain ⟨hPEmpty, hPX⟩ := (G.mem_crossingChangeCommutationHexagons C t _).mp hP
  refine (G.mem_crossingChangeHexagonRectangleDecompositions C t _).mpr ⟨?_, ?_⟩
  · refine (G.mem_crossingChangeCommutationHexagons C t _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_first h hrEmpty hPEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · rw [D.commute_hexagon_crossingCoveredSquares h]
      exact hPX
  · refine (G.mem_unblockedRectangles _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_second h hrEmpty hPEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · rw [D.commute_rectangle_toGridRectangle h]
      exact hrX

/-- Reordering a counted disjoint hexagon--rectangle domain of the crossing change homotopy gives
a counted rectangle--hexagon domain. -/
theorem commute_mem_crossingChangeRectangleHexagonDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z) :
    D.commute h ∈ G.crossingChangeRectangleHexagonDecompositions C t x z := by
  obtain ⟨hP, hr⟩ := (G.mem_crossingChangeHexagonRectangleDecompositions C t D).mp hD
  obtain ⟨hPEmpty, hPX⟩ := (G.mem_crossingChangeCommutationHexagons C t _).mp hP
  obtain ⟨hrEmpty, hrX⟩ := (G.mem_unblockedRectangles _).mp hr
  refine (G.mem_crossingChangeRectangleHexagonDecompositions C t _).mpr ⟨?_, ?_⟩
  · refine (G.mem_unblockedRectangles _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_first h hPEmpty hrEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · rw [D.commute_rectangle_toGridRectangle h]
      exact hrX
  · refine (G.mem_crossingChangeCommutationHexagons C t _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_second h hPEmpty hrEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · rw [D.commute_hexagon_crossingCoveredSquares h]
      exact hPX

variable (R : Type*) [CommSemiring R]

/-- Reordering a disjoint rectangle--hexagon domain of the crossing change homotopy preserves its
weight. -/
theorem crossingChangeHexagonRectangleWeight_commute {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    G.crossingChangeHexagonRectangleWeight C t R (D.commute h) =
      G.crossingChangeRectangleHexagonWeight C t R D := by
  rw [crossingChangeHexagonRectangleWeight_def, crossingChangeRectangleHexagonWeight_def,
    crossingChangeCommutationHexagonWeight_eq_monomial,
    crossingChangeCommutationHexagonWeight_eq_monomial, D.commute_hexagon_crossingCoveredSquares h,
    D.commute_rectangle_toGridRectangle h, mul_comm]

/-- Reordering a disjoint hexagon--rectangle domain of the crossing change homotopy preserves its
weight. -/
theorem crossingChangeRectangleHexagonWeight_commute {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    G.crossingChangeRectangleHexagonWeight C t R (D.commute h) =
      G.crossingChangeHexagonRectangleWeight C t R D := by
  have hw := G.crossingChangeHexagonRectangleWeight_commute C t R (D.commute h)
    (D.hasDisjointSides_commute h)
  rw [D.commute_commute h] at hw
  exact hw.symm

open scoped Classical in
/-- The disjoint rectangle--hexagon and hexagon--rectangle contributions to the crossing change
homotopy equation have the same total weight. -/
private theorem sum_rectangleHexagon_disjoint_eq_sum_hexagonRectangle_disjoint
    (x z : GridState n) :
    ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
        (fun D => D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeRectangleHexagonWeight C t R D =
      ∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
        (fun D => D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeHexagonRectangleWeight C t R D := by
  refine Finset.sum_bij'
    (fun D hD => D.commute (Finset.mem_filter.mp hD).2)
    (fun E hE => E.commute (Finset.mem_filter.mp hE).2) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    obtain ⟨hD, h⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr
      ⟨G.commute_mem_crossingChangeHexagonRectangleDecompositions C t D h hD,
        D.hasDisjointSides_commute h⟩
  · intro E hE
    obtain ⟨hE, h⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr
      ⟨G.commute_mem_crossingChangeRectangleHexagonDecompositions C t E h hE,
        E.hasDisjointSides_commute h⟩
  · intro D hD
    exact D.commute_commute (Finset.mem_filter.mp hD).2
  · intro E hE
    exact E.commute_commute (Finset.mem_filter.mp hE).2
  · intro D hD
    exact (G.crossingChangeHexagonRectangleWeight_commute C t R D (Finset.mem_filter.mp hD).2).symm

variable [CharP R 2]

open scoped Classical in
/-- In characteristic two, only composite domains whose rectangles share a vertical side
contribute to the left-hand side of the crossing change homotopy equation. -/
private theorem sum_add_sum_eq_sum_add_sum_overlap
    (x z : GridState n) :
    (∑ D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z,
        G.crossingChangeHexagonRectangleWeight C t R D) +
        ∑ D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z,
          G.crossingChangeRectangleHexagonWeight C t R D =
      (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeHexagonRectangleWeight C t R D) +
      ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeRectangleHexagonWeight C t R D := by
  rw [← Finset.sum_filter_add_sum_filter_not
      (G.crossingChangeHexagonRectangleDecompositions C t x z)
      (fun D => D.toRectangleDecomposition.HasDisjointSides),
    ← Finset.sum_filter_add_sum_filter_not
      (G.crossingChangeRectangleHexagonDecompositions C t x z)
      (fun D => D.toRectangleDecomposition.HasDisjointSides),
    G.sum_rectangleHexagon_disjoint_eq_sum_hexagonRectangle_disjoint C t R x z,
    add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]

open scoped Classical in
/-- In characteristic two, the crossing change homotopy equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` is
equivalent to the coefficient identity restricted to composite domains whose rectangles share a
vertical side. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_overlap
    (w : MvPolynomial (Fin n) R) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        w • c + (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n,
        (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
            (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.crossingChangeHexagonRectangleWeight C t R D) +
          ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
              (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
            G.crossingChangeRectangleHexagonWeight C t R D =
          (if x = z then w else 0) +
            ∑ y : GridState n,
              rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
                (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [G.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_decompositions C t R w]
  simp_rw [G.sum_add_sum_eq_sum_add_sum_overlap C t R]

open scoped Classical in
/-- **Reduction of the crossing change homotopy equation to distinct states.** If the turn rows
`s` and `t` differ and the annulus squares carry no `X`-marking, then over a commutative semiring
of characteristic two the equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ`, with `w` the annulus weight,
holds on every chain exactly when, for all distinct grid states `x` and `z`, the counted
composite domains from `x` to `z` whose rectangles share a vertical side have the total weight of
the products of the coefficients of `Φ`, renamed by the column swap, and of `Ψ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        G.crossingChangeAnnulusWeight R C t • c +
          (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, x ≠ z →
        (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
            (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.crossingChangeHexagonRectangleWeight C t R D) +
          ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
              (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
            G.crossingChangeRectangleHexagonWeight C t R D =
          ∑ y : GridState n,
            rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
              (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [G.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_overlap C t R]
  refine ⟨fun h x z hxz => by simpa only [hxz, ite_false, zero_add] using h x z, fun h x z => ?_⟩
  rcases eq_or_ne x z with rfl | hxz
  · -- On the diagonal, the restricted sums are the full coefficient of `∂ ∘ H + H ∘ ∂`.
    rw [← G.sum_add_sum_eq_sum_add_sum_overlap,
      ← G.sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient,
      ← G.sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient,
      ← unblockedDifferential_crossingChangeHomotopy_single_apply,
      ← crossingChangeHomotopy_unblockedDifferential_single_apply,
      ← commutationMap_withTurnRow_commutationMap_single_apply, ← Finsupp.add_apply]
    simp only [↓reduceIte]
    exact G.unblockedDifferential_crossingChangeHomotopy_add_single_apply_self R C t hst hX x
  · simpa only [hxz, ↓reduceIte, zero_add] using h x z hxz

variable {G C t}

open scoped Classical in
/-- **Reduction of the crossing change homotopy equation to distinct states**, for markings in
the order `O_b, O_a, X_b, X_a`. If the segments of the columns `a` and `b = finRotate n a`
interleave with `O_a` on the arc of column `b`, the crossing change maps turn in the rows of
`O_a` and `X_b`, and `R` has characteristic two, then `∂ ∘ H + H ∘ ∂ = V_b + Ψ ∘ Φ` holds on every
chain exactly when its coefficients between distinct grid states agree on the composite domains
sharing a vertical side. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
          (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, x ≠ z →
        (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
            (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.crossingChangeHexagonRectangleWeight C t R D) +
          ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
              (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
            G.crossingChangeRectangleHexagonWeight C t R D =
          ∑ y : GridState n,
            rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
              (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [← crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc R h hO hs ht]
  exact G.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne C t R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht)

open scoped Classical in
/-- **Reduction of the crossing change homotopy equation to distinct states**, for markings in
the order `O_b, X_a, X_b, O_a`. If the segments of the columns `a` and `b = finRotate n a`
interleave with `O_a` off the arc of column `b`, the crossing change maps turn in the rows of
`X_a` and `O_b`, and `R` has characteristic two, then `∂ ∘ H + H ∘ ∂ = V_a + Ψ ∘ Φ` holds on every
chain exactly when its coefficients between distinct grid states agree on the composite domains
sharing a vertical side. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
          (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, x ≠ z →
        (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
            (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.crossingChangeHexagonRectangleWeight C t R D) +
          ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
              (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
            G.crossingChangeRectangleHexagonWeight C t R D =
          ∑ y : GridState n,
            rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
              (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [← crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc R h hO hs ht]
  exact G.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne C t R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht)

end GridDiagram

end TauCeti
