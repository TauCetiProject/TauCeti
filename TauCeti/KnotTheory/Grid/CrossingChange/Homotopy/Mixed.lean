/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Recut
import TauCeti.Data.Finset.Basic
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.MixedSideRecut
import TauCeti.KnotTheory.Grid.Unblocked.OColumns

/-!
# Mixed-side pentagon pairs of a crossing change

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t ≠ s` be a second row. The round trip `Ψ ∘ Φ` of the crossing change maps
counts a pentagon of `G` turning in row `s` (`GridDiagram.commutationMap` of `C`) followed by a
pentagon of `G' = G.swapColumns a b` turning in row `t` (the commutation map of `G'` at
`C.withTurnRow t`). This file treats the pairs whose two pentagons turn on opposite sides of the
replaced grid line `b`: a terminal-side pentagon followed by an initial-side one, or the other way
round. Off the diagonal, each of them is matched with exactly one unpaired composite of the
crossing change homotopy equation (`GridDiagram.crossingChangeUnpairedHexagonComposites`), with
the same two rectangles and the same weight.

The two rectangles of such a pair share the grid line `b` and a corner row on it: the bottom row
for a terminal--initial pair, the top row for an initial--terminal pair. The rectangle of the
pentagon whose turn row is farther from that corner row contains both turn rows on its side along
`b`. It is a hexagon of the crossing change, cutting away the rows between the two turn points,
and the other rectangle is an ordinary rectangle. The squares
these two domains carry, read through `GridHexagonBetween.crossingCoveredSquares` and its initial
side analogue, are those the two pentagons carry, with the same multiplicities: away from the
columns `a` and `b` this is immediate, and in those two columns it is a comparison of row
intervals. So the composite is counted and has the weight of the pair, without any assumption on
where the markings of the columns `a` and `b` lie. Its recut is not a composite
(`GridHexagonCompositeDecomposition.toRectangleDecomposition_ne_recut_of_right_eq_left` and its
counterpart), so it is unpaired; if the annulus squares carry no `X`-marking it is the only
counted composite with these rectangles.

## Main results

* `existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair`, in the
  namespace `TauCeti.GridDiagram`: a counted off-diagonal terminal--initial pentagon pair has the
  same rectangles and weight as exactly one unpaired composite.
* `existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair`, in the
  namespace `TauCeti.GridDiagram`: the same for initial--terminal pairs.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the juxtaposition argument for the hexagon
  homotopies of commutation and of a crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} {G : GridDiagram n} {C : ColumnTurn n} {t : Fin n}

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Comparing the squares of two pairs of domains -/

/-- Two pairs of sets of squares cover each square equally often, that is they have the same union
and the same intersection, when they agree away from the columns `a` and `b` and cover each square
of those two columns equally often. -/
private theorem squares_eq_of_columns {A B E F : Finset (Fin n × Fin n)}
    (hA : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ A ↔ p ∈ E))
    (hB : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ B ↔ p ∈ F))
    (hcol : ∀ c r, c = a ∨ c = b →
      (((c, r) ∈ A ∨ (c, r) ∈ B ↔ (c, r) ∈ E ∨ (c, r) ∈ F) ∧
        ((c, r) ∈ A ∧ (c, r) ∈ B ↔ (c, r) ∈ E ∧ (c, r) ∈ F))) :
    A ∪ B = E ∪ F ∧ A ∩ B = E ∩ F := by
  have key (p : Fin n × Fin n) :
      (p ∈ A ∨ p ∈ B ↔ p ∈ E ∨ p ∈ F) ∧ (p ∈ A ∧ p ∈ B ↔ p ∈ E ∧ p ∈ F) := by
    obtain ⟨c, r⟩ := p
    by_cases hc : c = a ∨ c = b
    · exact hcol c r hc
    · rw [hA (c, r) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h)),
        hB (c, r) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))]
      exact ⟨Iff.rfl, Iff.rfl⟩
  refine ⟨Finset.ext fun p => ?_, Finset.ext fun p => ?_⟩
  · rw [Finset.mem_union, Finset.mem_union]
    exact (key p).1
  · rw [Finset.mem_inter, Finset.mem_inter]
    exact (key p).2

variable (R : Type*) [CommSemiring R]

/-- The weight of a pentagon of `G` followed by an initial-side pentagon of the exchanged diagram
is the product of the variables of the `O`-markings of `G` that they carry, the second read in `G`
by exchanging the columns `a` and `b`. -/
private theorem rename_pentagonWeight_mul_initialPentagonWeight {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y) (Q : GridInitialPentagonBetween a t y z) :
    rename (Equiv.swap a b) (G.pentagonWeight R C P) *
        (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q =
      (∏ c ∈ G.OColumnsOfSquares P.coveredSquares, MvPolynomial.X c) *
        ∏ c ∈ G.OColumnsOfSquares
          (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding),
          MvPolynomial.X c := by
  rw [rename_pentagonWeight, prod_ite_OSet_eq_prod_OColumnsOfSquares,
    swapColumns_initialPentagonWeight_withTurnRow]

/-- The weight of an initial-side pentagon of `G` followed by a pentagon of the exchanged diagram
is the product of the variables of the `O`-markings of `G` that they carry, the second read in `G`
by exchanging the columns `a` and `b`. -/
private theorem rename_initialPentagonWeight_mul_pentagonWeight {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y) (Q : GridPentagonBetween a t y z) :
    rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
        (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q =
      (∏ c ∈ G.OColumnsOfSquares P.coveredSquares, MvPolynomial.X c) *
        ∏ c ∈ G.OColumnsOfSquares
          (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding),
          MvPolynomial.X c := by
  rw [rename_initialPentagonWeight, prod_ite_OSet_eq_prod_OColumnsOfSquares,
    swapColumns_pentagonWeight_withTurnRow]

/-- An empty crossing-change hexagon followed by an empty rectangle, covering each square as often
as two sets of squares carrying no `X`-marking, is a counted composite whose weight is the product
of the variables of the `O`-markings of those two sets. -/
private theorem exists_inl_of_squares {x y z : GridState n} {A B : Finset (Fin n × Fin n)}
    (H : GridCommutationHexagonBetween a C.turnRow t x y) (S : GridRectangleBetween y z)
    (hH : H.toGridRectangleBetween.IsEmpty) (hS : S.IsEmpty)
    (hkey : A ∪ B = H.crossingCoveredSquares ∪ S.toGridRectangle.coveredSquares ∧
      A ∩ B = H.crossingCoveredSquares ∩ S.toGridRectangle.coveredSquares)
    (hAX : Disjoint A G.XSet) (hBX : Disjoint B G.XSet) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, H.toGridRectangleBetween, S⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            (∏ c ∈ G.OColumnsOfSquares A, MvPolynomial.X c) *
              ∏ c ∈ G.OColumnsOfSquares B, MvPolynomial.X c := by
  obtain ⟨hunion, hinter⟩ := hkey
  have hX : Disjoint (H.crossingCoveredSquares ∪ S.toGridRectangle.coveredSquares) G.XSet := by
    rw [← hunion]
    exact Finset.disjoint_union_left.mpr ⟨hAX, hBX⟩
  obtain ⟨hHX, hSX⟩ := Finset.disjoint_union_left.mp hX
  refine ⟨.inl ⟨y, H, S⟩, (G.inl_mem_crossingChangeHexagonCompositeDecompositions C t _).mpr
      ((G.mem_crossingChangeHexagonRectangleDecompositions C t _).mpr
        ⟨(G.mem_crossingChangeCommutationHexagons C t _).mpr ⟨hH, hHX⟩,
          (G.mem_unblockedRectangles _).mpr ⟨hS, hSX⟩⟩),
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inl _, ?_⟩
  rw [crossingChangeHexagonCompositeWeight_inl, crossingChangeHexagonRectangleWeight_def,
    crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
    OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares,
    ← prod_OColumnsOfSquares_union_inter, ← prod_OColumnsOfSquares_union_inter (A := A), hunion,
    hinter]

/-- An empty rectangle followed by an empty crossing-change hexagon, covering each square as often
as two sets of squares carrying no `X`-marking, is a counted composite whose weight is the product
of the variables of the `O`-markings of those two sets. -/
private theorem exists_inr_of_squares {x y z : GridState n} {A B : Finset (Fin n × Fin n)}
    (S : GridRectangleBetween x y) (H : GridCommutationHexagonBetween a C.turnRow t y z)
    (hS : S.IsEmpty) (hH : H.toGridRectangleBetween.IsEmpty)
    (hkey : A ∪ B = S.toGridRectangle.coveredSquares ∪ H.crossingCoveredSquares ∧
      A ∩ B = S.toGridRectangle.coveredSquares ∩ H.crossingCoveredSquares)
    (hAX : Disjoint A G.XSet) (hBX : Disjoint B G.XSet) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, S, H.toGridRectangleBetween⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            (∏ c ∈ G.OColumnsOfSquares A, MvPolynomial.X c) *
              ∏ c ∈ G.OColumnsOfSquares B, MvPolynomial.X c := by
  obtain ⟨hunion, hinter⟩ := hkey
  have hX : Disjoint (S.toGridRectangle.coveredSquares ∪ H.crossingCoveredSquares) G.XSet := by
    rw [← hunion]
    exact Finset.disjoint_union_left.mpr ⟨hAX, hBX⟩
  obtain ⟨hSX, hHX⟩ := Finset.disjoint_union_left.mp hX
  refine ⟨.inr ⟨y, S, H⟩, (G.inr_mem_crossingChangeHexagonCompositeDecompositions C t _).mpr
      ((G.mem_crossingChangeRectangleHexagonDecompositions C t _).mpr
        ⟨(G.mem_unblockedRectangles _).mpr ⟨hS, hSX⟩,
          (G.mem_crossingChangeCommutationHexagons C t _).mpr ⟨hH, hHX⟩⟩),
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inr _, ?_⟩
  rw [crossingChangeHexagonCompositeWeight_inr, crossingChangeRectangleHexagonWeight_def,
    crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
    OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares,
    ← prod_OColumnsOfSquares_union_inter, ← prod_OColumnsOfSquares_union_inter (A := A), hunion,
    hinter]

/-! ### Row intervals in the columns `a` and `b` -/

/-- The rows of a terminal--initial pair whose second turn lies above the first, with common
bottom row `B`: in column `a` the pentagons cover the rows from `s` to `P_top` and from `B` to
`s'`, and the rectangle and the hexagon those from `B` to `P_top` and from `s` to `s'`; in column
`b` the pentagons cover the rows from `B` to `s` and from `s'` to `Q_top`, and the hexagon those
from `B` to `Q_top` outside the cut rows from `s` to `s'`. -/
private theorem terminalInitial_rows_of_lt {B Pt Qt s s' r : Fin n} (hs : s ∈ Grid.cIco B Pt)
    (hturn : s ∈ Grid.cIco B Qt ∧ s' ∈ Grid.cIoo s Qt) :
    ((r ∈ Grid.cIoo s Pt ∨ r ∈ Grid.cIco B s' ↔ r ∈ Grid.cIco B Pt ∨ r ∈ Grid.cIoo s s') ∧
        (r ∈ Grid.cIoo s Pt ∧ r ∈ Grid.cIco B s' ↔ r ∈ Grid.cIco B Pt ∧ r ∈ Grid.cIoo s s')) ∧
      (r ∈ Grid.cIco B s ∨ r ∈ Grid.cIoo s' Qt ↔
          r ∈ Grid.cIco B Qt ∧ r ∉ insert s' (Grid.cIco s s')) ∧
        ¬(r ∈ Grid.cIco B s ∧ r ∈ Grid.cIoo s' Qt) := by
  obtain ⟨hsQ, hs'Q⟩ := hturn
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-- The rows of a terminal--initial pair whose first turn lies above the second, with common
bottom row `B`: in column `a` the pentagons cover the rows from `s` to `P_top` and from `B` to
`s'`, and the hexagon those from `B` to `P_top` outside the cut rows from `s'` to `s`; in column
`b` the pentagons cover the rows from `B` to `s` and from `s'` to `Q_top`, and the hexagon and the
rectangle those from `s'` to `s` and from `B` to `Q_top`. -/
private theorem terminalInitial_rows_of_gt {B Pt Qt s s' r : Fin n} (hs' : s' ∈ Grid.cIco B Qt)
    (hturn : s' ∈ Grid.cIco B Pt ∧ s ∈ Grid.cIoo s' Pt) :
    ((r ∈ Grid.cIoo s Pt ∨ r ∈ Grid.cIco B s' ↔
          r ∈ Grid.cIco B Pt ∧ r ∉ insert s (Grid.cIco s' s)) ∧
        ¬(r ∈ Grid.cIoo s Pt ∧ r ∈ Grid.cIco B s')) ∧
      (r ∈ Grid.cIco B s ∨ r ∈ Grid.cIoo s' Qt ↔ r ∈ Grid.cIoo s' s ∨ r ∈ Grid.cIco B Qt) ∧
        (r ∈ Grid.cIco B s ∧ r ∈ Grid.cIoo s' Qt ↔ r ∈ Grid.cIoo s' s ∧ r ∈ Grid.cIco B Qt) := by
  obtain ⟨hs'P, hsP⟩ := hturn
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-- The rows of an initial--terminal pair whose second turn lies above the first, with common top
row `T`: in column `a` the pentagons cover the rows from `s` to `T` and from `Q_bottom` to `s'`,
and the hexagon and the rectangle those from `s` to `s'` and from `Q_bottom` to `T`; in column `b`
the pentagons cover the rows from `P_bottom` to `s` and from `s'` to `T`, and the hexagon those
from `P_bottom` to `T` outside the cut rows from `s` to `s'`. -/
private theorem initialTerminal_rows_of_lt {Pb Qb T s s' r : Fin n} (hs : s ∈ Grid.cIco Pb T)
    (hs' : s' ∈ Grid.cIco Qb T) (hturn : s' ∈ Grid.cIoo s T) :
    ((r ∈ Grid.cIoo s T ∨ r ∈ Grid.cIco Qb s' ↔ r ∈ Grid.cIoo s s' ∨ r ∈ Grid.cIco Qb T) ∧
        (r ∈ Grid.cIoo s T ∧ r ∈ Grid.cIco Qb s' ↔ r ∈ Grid.cIoo s s' ∧ r ∈ Grid.cIco Qb T)) ∧
      (r ∈ Grid.cIco Pb s ∨ r ∈ Grid.cIoo s' T ↔
          r ∈ Grid.cIco Pb T ∧ r ∉ insert s' (Grid.cIco s s')) ∧
        ¬(r ∈ Grid.cIco Pb s ∧ r ∈ Grid.cIoo s' T) := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-- The rows of an initial--terminal pair whose first turn lies above the second, with common top
row `T`: in column `a` the pentagons cover the rows from `s` to `T` and from `Q_bottom` to `s'`,
and the hexagon those from `Q_bottom` to `T` outside the cut rows from `s'` to `s`; in column `b`
the pentagons cover the rows from `P_bottom` to `s` and from `s'` to `T`, and the rectangle and
the hexagon those from `P_bottom` to `T` and from `s'` to `s`. -/
private theorem initialTerminal_rows_of_gt {Pb Qb T s s' r : Fin n} (hs : s ∈ Grid.cIco Pb T)
    (hs' : s' ∈ Grid.cIco Qb T) (hturn : s ∈ Grid.cIoo s' T) :
    ((r ∈ Grid.cIoo s T ∨ r ∈ Grid.cIco Qb s' ↔
          r ∈ Grid.cIco Qb T ∧ r ∉ insert s (Grid.cIco s' s)) ∧
        ¬(r ∈ Grid.cIoo s T ∧ r ∈ Grid.cIco Qb s')) ∧
      (r ∈ Grid.cIco Pb s ∨ r ∈ Grid.cIoo s' T ↔ r ∈ Grid.cIco Pb T ∨ r ∈ Grid.cIoo s' s) ∧
        (r ∈ Grid.cIco Pb s ∧ r ∈ Grid.cIoo s' T ↔ r ∈ Grid.cIco Pb T ∧ r ∈ Grid.cIoo s' s) := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-! ### Terminal-side followed by initial-side -/

section TerminalInitial

variable {x y z : GridState n} (P : GridPentagonBetween C.column C.turnRow x y)
  (Q : GridInitialPentagonBetween C.column t y z)

/-- A terminal-side pentagon and a following initial-side pentagon share the grid line `b`,
terminal for the first and initial for the second. -/
private theorem terminalInitial_right_eq_left : P.right = Q.left :=
  P.right_eq.trans Q.left_eq.symm

/-- When the turn of the second pentagon lies above that of the first, a counted terminal--initial
pair has the same rectangles as a counted rectangle--hexagon composite of the same weight, whose
hexagon is the rectangle of the second pentagon. -/
private theorem terminalInitial_rectangleHexagon (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z)
    (hturn : C.turnRow ∈ Grid.cIco P.bottom Q.top ∧ t ∈ Grid.cIoo C.turnRow Q.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.pentagonWeight R C P) *
              (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ
  have hbottom : Q.bottom = P.bottom :=
    GridRectangleDecomposition.second_bottom_eq_first_bottom_of_right_eq_left
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ (terminalInitial_right_eq_left P Q)
  have hturnQ : C.turnRow ∈ Grid.cIco Q.bottom Q.top := hbottom ▸ hturn.1
  -- The rectangle of `Q` has both turn rows on its side along `b`, so it underlies
  -- an initial-side hexagon of the crossing change, cutting away the rows between
  -- the turn points.
  let H₀ : GridInitialHexagonBetween a C.turnRow t y z :=
    ⟨Q.toGridRectangleBetween, Q.left_eq, hturnQ, hturn.2⟩
  have hH₀ : H₀.toGridRectangleBetween = Q.toGridRectangleBetween := rfl
  have hab := C.column_ne_next
  -- The hexagon carries the squares of its rectangle outside the cut rows of
  -- column `b`, together with the rows between the turn points in column `a`.
  have hHmem (p : Fin n × Fin n) :
      p ∈ GridCommutationHexagonBetween.crossingCoveredSquares
          (.inr H₀ : GridCommutationHexagonBetween a C.turnRow t y z) ↔
        p ∈ Q.toGridRectangle.coveredSquares ∧
            ¬(p.1 = b ∧ p.2 ∈ insert t (Grid.cIco C.turnRow t)) ∨
          p.1 = a ∧ p.2 ∈ Grid.cIoo C.turnRow t := by
    rw [GridCommutationHexagonBetween.crossingCoveredSquares_inr, H₀.mem_crossingCoveredSquares,
      hH₀]
  -- The two pentagons, the second read in `G`, cover each square as often as the
  -- rectangle of `P` and the hexagon. Away from the columns `a` and `b` this is
  -- immediate. In those two columns, `simp only` turns membership in each domain into a
  -- cyclic row interval, and the comparison of row intervals is `terminalInitial_rows_of_lt`.
  have hkey := squares_eq_of_columns (C := C) (A := P.coveredSquares)
    (B := Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    (E := P.toGridRectangle.coveredSquares)
    (F := GridCommutationHexagonBetween.crossingCoveredSquares
      (.inr H₀ : GridCommutationHexagonBetween a C.turnRow t y z))
    (fun p ha hb => P.mem_coveredSquares_iff_of_ne ha hb)
    (fun p ha hb => by
      rw [Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb,
        Q.mem_coveredSquares_iff_of_ne ha hb, hHmem]
      simp only [ha, hb, false_and, not_false_eq_true, and_true, or_false])
    (fun c r hc => by
      obtain ⟨hrowa, hrowb⟩ := terminalInitial_rows_of_lt (r := r) P.turn_mem_cIco_bottom_top hturn
      rcases hc with rfl | rfl
      · simp only [P.mk_mem_coveredSquares_left_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_left, Q.mk_mem_coveredSquares_right_column, hbottom,
          P.mk_mem_toGridRectangle_coveredSquares_left_column, hHmem,
          Q.mk_notMem_toGridRectangle_coveredSquares_left_column, hab, false_and, true_and,
          false_or]
        exact hrowa
      · simp only [P.mk_mem_coveredSquares_right_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_right, Q.mk_mem_coveredSquares_left_column,
          P.mk_notMem_toGridRectangle_coveredSquares_right_column, hHmem,
          Q.mk_mem_toGridRectangle_coveredSquares_right_column, hbottom, hab.symm, true_and,
          false_and, or_false, false_or, iff_false]
        exact hrowb)
  -- Hence the composite is counted and carries the markings, so the weight, of the pair.
  obtain ⟨F, hF, hFD, hFw⟩ := exists_inr_of_squares R P.toGridRectangleBetween (.inr H₀) hp
    (by rw [GridCommutationHexagonBetween.toGridRectangleBetween_inr, hH₀]; exact hq) hkey hpX
    ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  exact ⟨F, hF, by rw [hFD, GridCommutationHexagonBetween.toGridRectangleBetween_inr, hH₀],
    by rw [hFw, rename_pentagonWeight_mul_initialPentagonWeight]⟩

/-- When the turn of the first pentagon lies above that of the second, a counted terminal--initial
pair has the same rectangles as a counted hexagon--rectangle composite of the same weight, whose
hexagon is the rectangle of the first pentagon. -/
private theorem terminalInitial_hexagonRectangle (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z)
    (hturn : t ∈ Grid.cIco P.bottom P.top ∧ C.turnRow ∈ Grid.cIoo t P.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.pentagonWeight R C P) *
              (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ
  have hbottom : Q.bottom = P.bottom :=
    GridRectangleDecomposition.second_bottom_eq_first_bottom_of_right_eq_left
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ (terminalInitial_right_eq_left P Q)
  have ht : t ∈ Grid.cIco P.bottom Q.top := hbottom ▸ Q.turn_mem_cIco_bottom_top
  -- The rectangle of `P` has both turn rows on its side along `b`, so it underlies
  -- a terminal-side hexagon of the crossing change, cutting away the rows between
  -- the turn points.
  let H₀ : GridHexagonBetween a t C.turnRow x y :=
    ⟨P.toGridRectangleBetween, P.right_eq, hturn.1, hturn.2⟩
  have hH₀ : H₀.toGridRectangleBetween = P.toGridRectangleBetween := rfl
  have hab := C.column_ne_next
  -- The hexagon carries the squares of its rectangle outside the cut rows of
  -- column `a`, together with the rows between the turn points in column `b`.
  have hHmem (p : Fin n × Fin n) :
      p ∈ GridCommutationHexagonBetween.crossingCoveredSquares
          (.inl H₀ : GridCommutationHexagonBetween a C.turnRow t x y) ↔
        p ∈ P.toGridRectangle.coveredSquares ∧
            ¬(p.1 = a ∧ p.2 ∈ insert C.turnRow (Grid.cIco t C.turnRow)) ∨
          p.1 = b ∧ p.2 ∈ Grid.cIoo t C.turnRow := by
    rw [GridCommutationHexagonBetween.crossingCoveredSquares_inl, H₀.mem_crossingCoveredSquares,
      hH₀]
  -- The two pentagons, the second read in `G`, cover each square as often as the
  -- hexagon and the rectangle of `Q`. Away from the columns `a` and `b` this is
  -- immediate. In those two columns, `simp only` turns membership in each domain into a
  -- cyclic row interval, and the comparison of row intervals is `terminalInitial_rows_of_gt`.
  have hkey := squares_eq_of_columns (C := C) (A := P.coveredSquares)
    (B := Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    (E := GridCommutationHexagonBetween.crossingCoveredSquares
      (.inl H₀ : GridCommutationHexagonBetween a C.turnRow t x y))
    (F := Q.toGridRectangle.coveredSquares)
    (fun p ha hb => by
      rw [P.mem_coveredSquares_iff_of_ne ha hb, hHmem]
      simp only [ha, hb, false_and, not_false_eq_true, and_true, or_false])
    (fun p ha hb => (Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb).trans
      (Q.mem_coveredSquares_iff_of_ne ha hb))
    (fun c r hc => by
      obtain ⟨hrowa, hrowb⟩ := terminalInitial_rows_of_gt (r := r) ht hturn
      rcases hc with rfl | rfl
      · simp only [P.mk_mem_coveredSquares_left_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_left, Q.mk_mem_coveredSquares_right_column, hbottom, hHmem,
          P.mk_mem_toGridRectangle_coveredSquares_left_column,
          Q.mk_notMem_toGridRectangle_coveredSquares_left_column, hab, true_and, false_and,
          or_false, and_false, iff_false]
        exact hrowa
      · simp only [P.mk_mem_coveredSquares_right_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_right, Q.mk_mem_coveredSquares_left_column, hHmem,
          P.mk_notMem_toGridRectangle_coveredSquares_right_column,
          Q.mk_mem_toGridRectangle_coveredSquares_right_column, hbottom, hab.symm, true_and,
          false_and, false_or]
        exact hrowb)
  -- Hence the composite is counted and carries the markings, so the weight, of the pair.
  obtain ⟨F, hF, hFD, hFw⟩ := exists_inl_of_squares R (.inl H₀) Q.toGridRectangleBetween
    (by rw [GridCommutationHexagonBetween.toGridRectangleBetween_inl, hH₀]; exact hp) hq hkey hpX
    ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  exact ⟨F, hF, by rw [hFD, GridCommutationHexagonBetween.toGridRectangleBetween_inl, hH₀],
    by rw [hFw, rename_pentagonWeight_mul_initialPentagonWeight]⟩

end TerminalInitial

/-! ### Initial-side followed by terminal-side -/

section InitialTerminal

variable {x y z : GridState n} (P : GridInitialPentagonBetween C.column C.turnRow x y)
  (Q : GridPentagonBetween C.column t y z)

/-- An initial-side pentagon and a following terminal-side pentagon share the grid line `b`,
initial for the first and terminal for the second. -/
private theorem initialTerminal_left_eq_right : P.left = Q.right :=
  P.left_eq.trans Q.right_eq.symm

/-- When the turn of the second pentagon lies above that of the first, a counted initial--terminal
pair has the same rectangles as a counted hexagon--rectangle composite of the same weight, whose
hexagon is the rectangle of the first pentagon. -/
private theorem initialTerminal_hexagonRectangle (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z)
    (hturn : t ∈ Grid.cIoo C.turnRow P.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
              (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ
  have htop : Q.top = P.top :=
    GridRectangleDecomposition.second_top_eq_first_top_of_left_eq_right
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ (initialTerminal_left_eq_right P Q)
  have ht : t ∈ Grid.cIco Q.bottom P.top := htop ▸ Q.turn_mem_cIco_bottom_top
  -- The rectangle of `P` has both turn rows on its side along `b`, so it underlies
  -- an initial-side hexagon of the crossing change, cutting away the rows between
  -- the turn points.
  let H₀ : GridInitialHexagonBetween a C.turnRow t x y :=
    ⟨P.toGridRectangleBetween, P.left_eq, P.turn_mem_cIco_bottom_top, hturn⟩
  have hH₀ : H₀.toGridRectangleBetween = P.toGridRectangleBetween := rfl
  have hab := C.column_ne_next
  -- The hexagon carries the squares of its rectangle outside the cut rows of
  -- column `b`, together with the rows between the turn points in column `a`.
  have hHmem (p : Fin n × Fin n) :
      p ∈ GridCommutationHexagonBetween.crossingCoveredSquares
          (.inr H₀ : GridCommutationHexagonBetween a C.turnRow t x y) ↔
        p ∈ P.toGridRectangle.coveredSquares ∧
            ¬(p.1 = b ∧ p.2 ∈ insert t (Grid.cIco C.turnRow t)) ∨
          p.1 = a ∧ p.2 ∈ Grid.cIoo C.turnRow t := by
    rw [GridCommutationHexagonBetween.crossingCoveredSquares_inr, H₀.mem_crossingCoveredSquares,
      hH₀]
  -- The two pentagons, the second read in `G`, cover each square as often as the
  -- hexagon and the rectangle of `Q`. Away from the columns `a` and `b` this is
  -- immediate. In those two columns, `simp only` turns membership in each domain into a
  -- cyclic row interval, and the comparison of row intervals is `initialTerminal_rows_of_lt`.
  have hkey := squares_eq_of_columns (C := C) (A := P.coveredSquares)
    (B := Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    (E := GridCommutationHexagonBetween.crossingCoveredSquares
      (.inr H₀ : GridCommutationHexagonBetween a C.turnRow t x y))
    (F := Q.toGridRectangle.coveredSquares)
    (fun p ha hb => by
      rw [P.mem_coveredSquares_iff_of_ne ha hb, hHmem]
      simp only [ha, hb, false_and, not_false_eq_true, and_true, or_false])
    (fun p ha hb => (Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb).trans
      (Q.mem_coveredSquares_iff_of_ne ha hb))
    (fun c r hc => by
      obtain ⟨hrowa, hrowb⟩ := initialTerminal_rows_of_lt (r := r) P.turn_mem_cIco_bottom_top ht
        hturn
      rcases hc with rfl | rfl
      · simp only [P.mk_mem_coveredSquares_left_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_left, Q.mk_mem_coveredSquares_right_column, hHmem,
          P.mk_notMem_toGridRectangle_coveredSquares_left_column,
          Q.mk_mem_toGridRectangle_coveredSquares_left_column, htop, hab, true_and, false_and,
          false_or]
        exact hrowa
      · simp only [P.mk_mem_coveredSquares_right_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_right, Q.mk_mem_coveredSquares_left_column, htop, hHmem,
          P.mk_mem_toGridRectangle_coveredSquares_right_column,
          Q.mk_notMem_toGridRectangle_coveredSquares_right_column, hab.symm, true_and,
          false_and, or_false, and_false, iff_false]
        exact hrowb)
  -- Hence the composite is counted and carries the markings, so the weight, of the pair.
  obtain ⟨F, hF, hFD, hFw⟩ := exists_inl_of_squares R (.inr H₀) Q.toGridRectangleBetween
    (by rw [GridCommutationHexagonBetween.toGridRectangleBetween_inr, hH₀]; exact hp) hq hkey hpX
    ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  exact ⟨F, hF, by rw [hFD, GridCommutationHexagonBetween.toGridRectangleBetween_inr, hH₀],
    by rw [hFw, rename_initialPentagonWeight_mul_pentagonWeight]⟩

/-- When the turn of the first pentagon lies above that of the second, a counted initial--terminal
pair has the same rectangles as a counted rectangle--hexagon composite of the same weight, whose
hexagon is the rectangle of the second pentagon. -/
private theorem initialTerminal_rectangleHexagon (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z)
    (hturn : C.turnRow ∈ Grid.cIoo t P.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
              (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ
  have htop : Q.top = P.top :=
    GridRectangleDecomposition.second_top_eq_first_top_of_left_eq_right
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ (initialTerminal_left_eq_right P Q)
  have ht : t ∈ Grid.cIco Q.bottom P.top := htop ▸ Q.turn_mem_cIco_bottom_top
  have hturnQ : C.turnRow ∈ Grid.cIoo t Q.top := htop ▸ hturn
  -- The rectangle of `Q` has both turn rows on its side along `b`, so it underlies
  -- a terminal-side hexagon of the crossing change, cutting away the rows between
  -- the turn points.
  let H₀ : GridHexagonBetween a t C.turnRow y z :=
    ⟨Q.toGridRectangleBetween, Q.right_eq, Q.turn_mem_cIco_bottom_top, hturnQ⟩
  have hH₀ : H₀.toGridRectangleBetween = Q.toGridRectangleBetween := rfl
  have hab := C.column_ne_next
  -- The hexagon carries the squares of its rectangle outside the cut rows of
  -- column `a`, together with the rows between the turn points in column `b`.
  have hHmem (p : Fin n × Fin n) :
      p ∈ GridCommutationHexagonBetween.crossingCoveredSquares
          (.inl H₀ : GridCommutationHexagonBetween a C.turnRow t y z) ↔
        p ∈ Q.toGridRectangle.coveredSquares ∧
            ¬(p.1 = a ∧ p.2 ∈ insert C.turnRow (Grid.cIco t C.turnRow)) ∨
          p.1 = b ∧ p.2 ∈ Grid.cIoo t C.turnRow := by
    rw [GridCommutationHexagonBetween.crossingCoveredSquares_inl, H₀.mem_crossingCoveredSquares,
      hH₀]
  -- The two pentagons, the second read in `G`, cover each square as often as the
  -- rectangle of `P` and the hexagon. Away from the columns `a` and `b` this is
  -- immediate. In those two columns, `simp only` turns membership in each domain into a
  -- cyclic row interval, and the comparison of row intervals is `initialTerminal_rows_of_gt`.
  have hkey := squares_eq_of_columns (C := C) (A := P.coveredSquares)
    (B := Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    (E := P.toGridRectangle.coveredSquares)
    (F := GridCommutationHexagonBetween.crossingCoveredSquares
      (.inl H₀ : GridCommutationHexagonBetween a C.turnRow t y z))
    (fun p ha hb => P.mem_coveredSquares_iff_of_ne ha hb)
    (fun p ha hb => by
      rw [Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb,
        Q.mem_coveredSquares_iff_of_ne ha hb, hHmem]
      simp only [ha, hb, false_and, not_false_eq_true, and_true, or_false])
    (fun c r hc => by
      obtain ⟨hrowa, hrowb⟩ := initialTerminal_rows_of_gt (r := r) P.turn_mem_cIco_bottom_top ht
        hturn
      rcases hc with rfl | rfl
      · simp only [P.mk_mem_coveredSquares_left_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_left, Q.mk_mem_coveredSquares_right_column, hHmem,
          P.mk_notMem_toGridRectangle_coveredSquares_left_column,
          Q.mk_mem_toGridRectangle_coveredSquares_left_column, htop, hab, true_and, false_and,
          false_or, or_false, iff_false]
        exact hrowa
      · simp only [P.mk_mem_coveredSquares_right_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
          Equiv.swap_apply_right, Q.mk_mem_coveredSquares_left_column, htop, hHmem,
          P.mk_mem_toGridRectangle_coveredSquares_right_column,
          Q.mk_notMem_toGridRectangle_coveredSquares_right_column, hab.symm, true_and,
          false_and, false_or]
        exact hrowb)
  -- Hence the composite is counted and carries the markings, so the weight, of the pair.
  obtain ⟨F, hF, hFD, hFw⟩ := exists_inr_of_squares R P.toGridRectangleBetween (.inl H₀) hp
    (by rw [GridCommutationHexagonBetween.toGridRectangleBetween_inl, hH₀]; exact hq) hkey hpX
    ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  exact ⟨F, hF, by rw [hFD, GridCommutationHexagonBetween.toGridRectangleBetween_inl, hH₀],
    by rw [hFw, rename_initialPentagonWeight_mul_pentagonWeight]⟩

end InitialTerminal

/-! ### The matching -/

/-- **Terminal--initial pentagon pairs of a crossing change.** Let the turn rows `s` of `C` and
`t` differ, and let the annulus squares carry no `X`-marking. A counted pentagon of `G` turning on
its terminal side in row `s`, followed by a counted initial-side pentagon of
`G' = G.swapColumns a b` turning in row `t`, from `x` to `z ≠ x`, has the same rectangles as
exactly one unpaired composite of the crossing change homotopy equation, and their weights agree.
Its hexagon is the rectangle of the pentagon whose turn row is farther from the common bottom
row. -/
theorem existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x y z : GridState n} (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a t y z) (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z) (hzx : z ≠ x) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.pentagonWeight R C P) *
              (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  have hp := ((G.mem_pentagons P).mp hP).1
  have hq := (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ).1
  have hbottom : Q.bottom = P.bottom :=
    GridRectangleDecomposition.second_bottom_eq_first_bottom_of_right_eq_left
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ (terminalInitial_right_eq_left P Q)
  have ht : t ∈ Grid.cIco P.bottom Q.top := hbottom ▸ Q.turn_mem_cIco_bottom_top
  obtain ⟨F, hF, hFD, hFw⟩ :
      ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
        F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
          F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
            G.crossingChangeHexagonCompositeWeight C t R F =
              rename (Equiv.swap a b) (G.pentagonWeight R C P) *
                (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
    rcases Grid.mem_cIco_and_mem_cIoo_or_mem_cIco_and_mem_cIoo_of_ne P.turn_mem_cIco_bottom_top
        ht hst with hturn | hturn
    · exact terminalInitial_rectangleHexagon R P Q hP hQ hturn
    · exact terminalInitial_hexagonRectangle R P Q hP hQ hturn
  rw [← hFw]
  exact existsUnique_crossingChangeUnpairedHexagonComposite_of_toRectangleDecomposition_eq R hX
    (GridRectangleDecomposition.hasOneCommonSide_of_right_eq_left_of_ne
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
      (terminalInitial_right_eq_left P Q) hzx) hp hq
    (fun E _ =>
      GridHexagonCompositeDecomposition.toRectangleDecomposition_ne_recut_of_right_eq_left
        (D := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩) P.right_eq Q.left_eq _ hp
        hq P.turn_mem_cIco_bottom_top ht E) hF hFD

/-- **Initial--terminal pentagon pairs of a crossing change.** Let the turn rows `s` of `C` and
`t` differ, and let the annulus squares carry no `X`-marking. A counted pentagon of `G` turning on
its initial side in row `s`, followed by a counted terminal-side pentagon of
`G' = G.swapColumns a b` turning in row `t`, from `x` to `z ≠ x`, has the same rectangles as
exactly one unpaired composite of the crossing change homotopy equation, and their weights agree.
Its hexagon is the rectangle of the pentagon whose turn row is farther from the common top row. -/
theorem existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x y z : GridState n} (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween a t y z) (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z) (hzx : z ≠ x) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
              (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  have hp := ((G.mem_initialPentagons P).mp hP).1
  have hq := (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ).1
  have htop : Q.top = P.top :=
    GridRectangleDecomposition.second_top_eq_first_top_of_left_eq_right
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ (initialTerminal_left_eq_right P Q)
  have ht : t ∈ Grid.cIco Q.bottom P.top := htop ▸ Q.turn_mem_cIco_bottom_top
  obtain ⟨F, hF, hFD, hFw⟩ :
      ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
        F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
          F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
            G.crossingChangeHexagonCompositeWeight C t R F =
              rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
                (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
    rcases Grid.mem_cIoo_or_mem_cIoo_of_ne P.turn_mem_cIco_bottom_top ht hst with hturn | hturn
    · exact initialTerminal_hexagonRectangle R P Q hP hQ hturn
    · exact initialTerminal_rectangleHexagon R P Q hP hQ hturn
  rw [← hFw]
  exact existsUnique_crossingChangeUnpairedHexagonComposite_of_toRectangleDecomposition_eq R hX
    (GridRectangleDecomposition.hasOneCommonSide_of_left_eq_right_of_ne
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
      (initialTerminal_left_eq_right P Q) hzx) hp hq
    (fun E _ =>
      GridHexagonCompositeDecomposition.toRectangleDecomposition_ne_recut_of_left_eq_right
        (D := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩) P.left_eq Q.right_eq _ hp
        hq P.turn_mem_cIco_bottom_top ht E) hF hFD

end TauCeti.GridDiagram
