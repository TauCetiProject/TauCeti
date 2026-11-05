/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Recut
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.InitialPair.Basic
import TauCeti.Data.Finset.Basic

/-!
# Same-side pentagon pairs for a crossing change

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row. The round trip `Ψ ∘ Φ` of the crossing change maps counts
pairs of empty pentagons: one of `G` turning in row `s` (`GridDiagram.commutationMap` of `C`),
followed by one of `G' = G.swapColumns a b` turning in row `t` (the commutation map of `G'` at
`C.withTurnRow t`). This file treats the pairs in which both pentagons turn on the same side of
the replaced grid line `b`: both on their terminal side, or both on their initial side.

Off the diagonal the rectangles of the two pentagons share exactly the side `b`, and their union
is an L-shaped domain. Recutting it along its other internal edge gives a piece with side `b`
spanning the rows of both pentagons, which is a crossing-change hexagon with corners in the rows
`s` and `t`, together with an ordinary rectangle away from the columns `a` and `b`.

* For two terminal-side pentagons the second lies directly below the first, so `t` lies below `s`
  and the piece is a hexagon turning on its terminal side and cutting from `t` up to `s`. The
  recut is a rectangle followed by the hexagon when the first initial side lies inside the second
  column interval, and the hexagon followed by a rectangle otherwise.
* For two initial-side pentagons the second lies directly above the first, so `s` lies below `t`
  and the piece is a hexagon turning on its initial side and cutting from `s` up to `t`. The
  recuts are `GridInitialPentagonBetween.recutRectangleHexagon` and
  `GridInitialPentagonBetween.recutHexagonRectangle`.

In each case the recut covers every square with the same multiplicity as the pentagon pair, the
second pentagon read in `G` by exchanging the two columns. In the column the hexagon cuts away,
the two pentagon arcs are the rows of the hexagon outside its closed cut; in the other column of
the pair they make up the open interval between the two turn rows that the hexagon adds. So the
recut is a counted composite of the crossing change homotopy equation, with the weight of the
pentagon pair, for any placement of the markings. Each pentagon contains only one of the two turn
rows, so the pentagon pair underlies no counted composite, and the recut is unpaired in the sense
of `GridDiagram.crossingChangeUnpairedHexagonComposites`.

## Main results

* `TauCeti.GridDiagram.exists_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair` and
  `TauCeti.GridDiagram.exists_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair`:
  a counted off-diagonal pair of same-side pentagons recuts to an unpaired composite of the same
  weight.
* `TauCeti.GridDiagram.existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair`
  and
  `TauCeti.GridDiagram.existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair`:
  if the annulus squares carry no `X`-marking, as for the crossing change maps of interleaving
  columns, this unpaired composite is unique.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1: the crossing change maps and the hexagon homotopy
  comparing their composite with multiplication by a variable.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.

The recuts follow the same-side cases of the commutation homotopy in
`TauCeti.KnotTheory.Grid.Commutation.Homotopy.TerminalPair` and
`TauCeti.KnotTheory.Grid.Commutation.Homotopy.InitialPair.Basic`; here the crossing-change
hexagons retain the bigons, so square multiplicities replace the commutation marking estimates,
as in `TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Mixed`.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "σ" => Equiv.toEmbedding
  (Equiv.prodCongr (Equiv.swap C.column (finRotate n C.column)) (Equiv.refl (Fin n)))

/-- Matching union and intersection with those of a pentagon pair, the second pentagon read in
`G` by exchanging the two columns, transports countedness and the total `O`-weight to two other
square sets. -/
private theorem pair_disjoint_and_weight (R : Type*) [CommSemiring R]
    (A B S T : Finset (Fin n × Fin n)) (hu : A ∪ B.map σ = S ∪ T) (hi : A ∩ B.map σ = S ∩ T)
    (hA : Disjoint A G.XSet) (hB : Disjoint B (G.swapColumns a b).XSet) :
    Disjoint S G.XSet ∧ Disjoint T G.XSet ∧
      (∏ c ∈ G.OColumnsOfSquares A, (MvPolynomial.X c : MvPolynomial (Fin n) R)) *
          ∏ c ∈ G.OColumnsOfSquares (B.map σ), MvPolynomial.X c =
        (∏ c ∈ G.OColumnsOfSquares S, MvPolynomial.X c) *
          ∏ c ∈ G.OColumnsOfSquares T, MvPolynomial.X c := by
  obtain ⟨hSX, hTX, hw⟩ := G.disjoint_and_prod_OSet_eq_of_union_inter_eq
    (MvPolynomial.X (R := R)) _ _ S T hu hi hA ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hB)
  refine ⟨hSX, hTX, ?_⟩
  simpa only [G.prod_ite_OSet_eq_prod_OColumnsOfSquares] using hw

/-! ### Two terminal-side pentagons -/

section Terminal

variable {x y z : GridState n} (P : GridPentagonBetween C.column C.turnRow x y)
  (Q : GridPentagonBetween C.column t y z)

/-- The underlying rectangles of the two pentagons have the replaced grid line as common
terminal side. -/
private theorem terminalPair_right_eq : P.right = Q.right :=
  P.right_eq.trans Q.right_eq.symm

/-- Off the diagonal, the second pentagon lies directly below the first. -/
private theorem terminalPair_rows (hne : P.left ≠ Q.left) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    P.bottom ∈ Grid.cIoo Q.bottom P.top ∧ Q.top = P.bottom := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  refine ⟨(D.cyclicOrder_of_isEmpty_of_right_eq_right (terminalPair_right_eq C t P Q)
    hne hp hq).2, ?_⟩
  rw [GridRectangleBetween.top_def, ← terminalPair_right_eq C t P Q, P.map_right,
    GridRectangleBetween.bottom_def]

variable {P Q}

/-- Both turn rows lie on the common terminal side of the union, `t` below `s`. -/
private theorem terminalPair_turns (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top)
    (htop : Q.top = P.bottom) :
    t ∈ Grid.cIco Q.bottom P.top ∧ C.turnRow ∈ Grid.cIoo t P.top := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  rw [htop] at ht
  refine ⟨Grid.mem_cIco_of_mem_cIco_of_mem_cIoo ht hrow, ?_⟩
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hs ht hrow ⊢
  split_ifs at * <;> omega

/-- In column `b`, the arc of the first pentagon and that of the second, read in `G`, partition
the open interval from `t` to `s`. -/
private theorem terminalPair_next_column (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top)
    (htop : Q.top = P.bottom) (r : Fin n) :
    (r ∈ Grid.cIco P.bottom C.turnRow ∨ r ∈ Grid.cIoo t Q.top ↔
        r ∈ Grid.cIoo t C.turnRow) ∧
      ¬(r ∈ Grid.cIco P.bottom C.turnRow ∧ r ∈ Grid.cIoo t Q.top) := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  rw [htop] at ht ⊢
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hs ht hrow ⊢
  split_ifs at * <;> omega

/-- A hexagon with terminal side `b` spanning the rows of both pentagons, together with a
rectangle with which it repartitions the union of the two pentagon rectangles, covers every
square with the multiplicity of the pentagon pair, the second pentagon read in `G` by exchanging
the two columns. -/
private theorem terminalPair_union_inter_eq {u v u' v' : GridState n}
    (H : GridHexagonBetween a t C.turnRow u v) (S : GridRectangleBetween u' v')
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom)
    (hHb : H.bottom = Q.bottom) (hHt : H.top = P.top)
    (hu : H.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
      P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares)
    (hPQ : Disjoint P.toGridRectangle.coveredSquares Q.toGridRectangle.coveredSquares)
    (hHS : Disjoint H.toGridRectangle.coveredSquares S.toGridRectangle.coveredSquares) :
    P.coveredSquares ∪ Q.coveredSquares.map σ =
        H.crossingCoveredSquares ∪ S.toGridRectangle.coveredSquares ∧
      P.coveredSquares ∩ Q.coveredSquares.map σ =
        H.crossingCoveredSquares ∩ S.toGridRectangle.coveredSquares := by
  have hHa (r : Fin n) :
      (a, r) ∈ H.toGridRectangle.coveredSquares ↔ r ∈ Grid.cIco Q.bottom P.top := by
    simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, H.right_eq, Grid.self_mem_cIco_finRotate H.left_ne,
      true_and, hHb, hHt]
  have hHb' (r : Fin n) : (b, r) ∉ H.toGridRectangle.coveredSquares := by
    simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
      H.right_eq, Grid.right_notMem_cIco, false_and, not_false_eq_true]
  -- The rectangle lies in the union of the pentagon rectangles, so it misses column `b`, and it
  -- misses column `a`, all of whose squares in that union lie under the hexagon.
  have hmem {p : Fin n × Fin n} (h : p ∈ S.toGridRectangle.coveredSquares) :
      p ∈ P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares :=
    hu ▸ Finset.mem_union_right _ h
  have hSa (r : Fin n) : (a, r) ∉ S.toGridRectangle.coveredSquares := fun h => by
    refine Finset.disjoint_left.mp hHS ((hHa r).mpr ?_) h
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow, Finset.mem_union]
    rcases Finset.mem_union.mp (hmem h) with h' | h'
    · exact Or.inr ((P.mk_mem_toGridRectangle_coveredSquares_left_column r).mp h')
    · exact Or.inl (htop ▸ (Q.mk_mem_toGridRectangle_coveredSquares_left_column r).mp h')
  have hSb (r : Fin n) : (b, r) ∉ S.toGridRectangle.coveredSquares := fun h => by
    rcases Finset.mem_union.mp (hmem h) with h' | h'
    · exact P.mk_notMem_toGridRectangle_coveredSquares_right_column r h'
    · exact Q.mk_notMem_toGridRectangle_coveredSquares_right_column r h'
  obtain ⟨ht, hst⟩ := terminalPair_turns C t hrow htop
  constructor <;> ext ⟨c, r⟩
  all_goals
    simp only [Finset.mem_union, Finset.mem_inter, H.mem_crossingCoveredSquares]
    by_cases hca : c = a
    · subst c
      -- In column `a` the pentagon arcs are the rows of the hexagon outside its closed cut.
      have hU := Finset.ext_iff.mp (Grid.cIco_union_cIoo_eq_sdiff_of_mem_cIoo ht hst) r
      have hD : r ∈ Grid.cIco Q.bottom t → r ∉ Grid.cIoo C.turnRow P.top :=
        fun h => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIoo_of_mem_cIoo ht hst) h
      have hS := hSa r
      simp only [Finset.mem_union, Finset.mem_sdiff] at hU
      simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_left,
        Q.mk_mem_coveredSquares_right_column, P.mk_mem_coveredSquares_left_column, hHa,
        C.column_ne_next, hS, true_and, false_and, or_false]
      tauto
    · by_cases hcb : c = b
      · subst c
        -- In column `b` the pentagon arcs make up the open interval the hexagon adds.
        have hc := terminalPair_next_column C t hrow htop r
        have hS := hSb r
        simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_right,
          Q.mk_mem_coveredSquares_left_column, P.mk_mem_coveredSquares_right_column, hHb', hS,
          true_and, false_and, false_or, or_false]
        tauto
      · have hU := Finset.ext_iff.mp hu (c, r)
        have hD₁ : (c, r) ∈ P.toGridRectangle.coveredSquares →
            (c, r) ∉ Q.toGridRectangle.coveredSquares := fun h => Finset.disjoint_left.mp hPQ h
        have hD₂ : (c, r) ∈ H.toGridRectangle.coveredSquares →
            (c, r) ∉ S.toGridRectangle.coveredSquares := fun h => Finset.disjoint_left.mp hHS h
        simp only [Finset.mem_union] at hU
        rw [P.mem_coveredSquares_iff_of_ne hca hcb,
          Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ hca hcb,
          Q.mem_coveredSquares_iff_of_ne hca hcb]
        simp only [hca, hcb, false_and, or_false, not_false_eq_true, and_true]
        tauto

/-- The pentagon pair itself underlies no counted composite: the rectangle under a hexagon of
either shape contains both turn rows or has initial side `b`, while the rectangle of each
pentagon contains only one turn row and has terminal side `b`. -/
private theorem terminalPair_ne_composite (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top)
    (htop : Q.top = P.bottom) (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F.toRectangleDecomposition ≠
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht : t ∈ Grid.cIco Q.bottom P.bottom := htop ▸ Q.turn_mem_cIco_bottom_top
  have hdisj := Grid.disjoint_cIco_cIco_of_mem_cIoo hrow
  have hnotP : t ∉ Grid.cIco P.bottom P.top := fun h => Finset.disjoint_left.mp hdisj ht h
  have hnotQ : C.turnRow ∉ Grid.cIco Q.bottom Q.top :=
    htop ▸ fun h => Finset.disjoint_left.mp hdisj h hs
  have key {u v : GridState n} (H : GridCommutationHexagonBetween a C.turnRow t u v) :
      H.toGridRectangleBetween.toGridRectangle ≠ P.toGridRectangle ∧
        H.toGridRectangleBetween.toGridRectangle ≠ Q.toGridRectangle := by
    cases H with
    | inl H =>
      have hlow : t ∈ Grid.cIco H.bottom H.top := H.lower_mem
      have hup : C.turnRow ∈ Grid.cIco H.bottom H.top :=
        H.insert_cIco_subset_cIco_bottom_top (Finset.mem_insert_self _ _)
      constructor <;> intro h <;>
      · have hb := congrArg GridRectangle.bottom h
        have ht' := congrArg GridRectangle.top h
        simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl,
          GridRectangleBetween.toGridRectangle_bottom,
          GridRectangleBetween.toGridRectangle_top] at hb ht'
        rw [hb, ht'] at hlow hup
        first | exact hnotP hlow | exact hnotQ hup
    | inr H =>
      constructor <;> intro h <;>
      · have hl := congrArg GridRectangle.left h
        simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr,
          GridRectangleBetween.toGridRectangle_left, H.left_eq] at hl
        first | exact P.left_ne hl.symm | exact Q.left_ne hl.symm
  intro hFD
  cases F with
  | inl F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hFD
    exact (key F.hexagon).1 (by
      simpa only [GridHexagonRectangleDecomposition.toRectangleDecomposition] using
        congrArg (fun E : GridRectangleDecomposition x z => E.first.toGridRectangle) hFD)
  | inr F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hFD
    exact (key F.hexagon).2 (by
      simpa only [GridRectangleHexagonDecomposition.toRectangleDecomposition] using
        congrArg (fun E : GridRectangleDecomposition x z => E.second.toGridRectangle) hFD)

end Terminal

/-! ### Two initial-side pentagons -/

section Initial

variable {x y z : GridState n} (P : GridInitialPentagonBetween C.column C.turnRow x y)
  (Q : GridInitialPentagonBetween C.column t y z)

/-- The underlying rectangles of the two pentagons have the replaced grid line as common initial
side. -/
private theorem initialPair_left_eq : P.left = Q.left :=
  P.left_eq.trans Q.left_eq.symm

/-- Off the diagonal, the second pentagon lies directly above the first. -/
private theorem initialPair_rows (hne : P.right ≠ Q.right) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    P.top ∈ Grid.cIoo P.bottom Q.top ∧ Q.bottom = P.top := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  exact ⟨(D.cyclicOrder_of_isEmpty_of_left_eq_left (initialPair_left_eq C t P Q) hne hp hq).2,
    D.second_bottom_eq_first_top_of_left_eq_left (initialPair_left_eq C t P Q)⟩

variable {P Q}

/-- Both turn rows lie on the common initial side of the union, `s` below `t`. -/
private theorem initialPair_turns (hrow : P.top ∈ Grid.cIoo P.bottom Q.top)
    (hbot : Q.bottom = P.top) :
    C.turnRow ∈ Grid.cIco P.bottom Q.top ∧ t ∈ Grid.cIoo C.turnRow Q.top := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  rw [hbot] at ht
  refine ⟨Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow ▸ Finset.mem_union_left _ hs, ?_⟩
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hs ht hrow ⊢
  split_ifs at * <;> omega

/-- In column `a`, the arc of the first pentagon and that of the second, read in `G`, partition
the open interval from `s` to `t`. -/
private theorem initialPair_column (hrow : P.top ∈ Grid.cIoo P.bottom Q.top)
    (hbot : Q.bottom = P.top) (r : Fin n) :
    (r ∈ Grid.cIoo C.turnRow P.top ∨ r ∈ Grid.cIco Q.bottom t ↔
        r ∈ Grid.cIoo C.turnRow t) ∧
      ¬(r ∈ Grid.cIoo C.turnRow P.top ∧ r ∈ Grid.cIco Q.bottom t) := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  rw [hbot] at ht ⊢
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hs ht hrow ⊢
  split_ifs at * <;> omega

/-- A hexagon with initial side `b` spanning the rows of both pentagons, together with a
rectangle with which it repartitions the union of the two pentagon rectangles, covers every
square with the multiplicity of the pentagon pair, the second pentagon read in `G` by exchanging
the two columns. -/
private theorem initialPair_union_inter_eq {u v u' v' : GridState n}
    (H : GridInitialHexagonBetween a C.turnRow t u v) (S : GridRectangleBetween u' v')
    (hrow : P.top ∈ Grid.cIoo P.bottom Q.top) (hbot : Q.bottom = P.top)
    (hHb : H.bottom = P.bottom) (hHt : H.top = Q.top)
    (hu : H.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
      P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares)
    (hPQ : Disjoint P.toGridRectangle.coveredSquares Q.toGridRectangle.coveredSquares)
    (hHS : Disjoint H.toGridRectangle.coveredSquares S.toGridRectangle.coveredSquares) :
    P.coveredSquares ∪ Q.coveredSquares.map σ =
        H.crossingCoveredSquares ∪ S.toGridRectangle.coveredSquares ∧
      P.coveredSquares ∩ Q.coveredSquares.map σ =
        H.crossingCoveredSquares ∩ S.toGridRectangle.coveredSquares := by
  have hHnext (r : Fin n) :
      (b, r) ∈ H.toGridRectangle.coveredSquares ↔ r ∈ Grid.cIco P.bottom Q.top := by
    simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, H.left_eq, Grid.left_mem_cIco H.right_ne.symm,
      true_and, hHb, hHt]
  have hHa (r : Fin n) : (a, r) ∉ H.toGridRectangle.coveredSquares := by
    have ha : a ∉ Grid.cIco b H.right := by simp
    simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
      H.left_eq, ha, false_and, not_false_eq_true]
  -- The rectangle lies in the union of the pentagon rectangles, so it misses column `a`, and it
  -- misses column `b`, all of whose squares in that union lie under the hexagon.
  have hmem {p : Fin n × Fin n} (h : p ∈ S.toGridRectangle.coveredSquares) :
      p ∈ P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares :=
    hu ▸ Finset.mem_union_right _ h
  have hSa (r : Fin n) : (a, r) ∉ S.toGridRectangle.coveredSquares := fun h => by
    rcases Finset.mem_union.mp (hmem h) with h' | h'
    · exact P.mk_notMem_toGridRectangle_coveredSquares_left_column r h'
    · exact Q.mk_notMem_toGridRectangle_coveredSquares_left_column r h'
  have hSb (r : Fin n) : (b, r) ∉ S.toGridRectangle.coveredSquares := fun h => by
    refine Finset.disjoint_left.mp hHS ((hHnext r).mpr ?_) h
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow, Finset.mem_union]
    rcases Finset.mem_union.mp (hmem h) with h' | h'
    · exact Or.inl ((P.mk_mem_toGridRectangle_coveredSquares_right_column r).mp h')
    · exact Or.inr (hbot ▸ (Q.mk_mem_toGridRectangle_coveredSquares_right_column r).mp h')
  obtain ⟨hs, hst⟩ := initialPair_turns C t hrow hbot
  constructor <;> ext ⟨c, r⟩
  all_goals
    simp only [Finset.mem_union, Finset.mem_inter, H.mem_crossingCoveredSquares]
    by_cases hca : c = a
    · subst c
      -- In column `a` the pentagon arcs make up the open interval the hexagon adds.
      have hc := initialPair_column C t hrow hbot r
      have hS := hSa r
      simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_left,
        Q.mk_mem_coveredSquares_right_column, P.mk_mem_coveredSquares_left_column, hHa, hS,
        C.column_ne_next, true_and, false_and, false_or, or_false]
      tauto
    · by_cases hcb : c = b
      · subst c
        -- In column `b` the pentagon arcs are the rows of the hexagon outside its closed cut.
        have hU := Finset.ext_iff.mp (Grid.cIco_union_cIoo_eq_sdiff_of_mem_cIoo hs hst) r
        have hD : r ∈ Grid.cIco P.bottom C.turnRow → r ∉ Grid.cIoo t Q.top :=
          fun h => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIoo_of_mem_cIoo hs hst) h
        have hS := hSb r
        simp only [Finset.mem_union, Finset.mem_sdiff] at hU
        simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_right,
          Q.mk_mem_coveredSquares_left_column, P.mk_mem_coveredSquares_right_column, hHnext, hS,
          C.column_ne_next.symm, true_and, false_and, or_false]
        tauto
      · have hU := Finset.ext_iff.mp hu (c, r)
        have hD₁ : (c, r) ∈ P.toGridRectangle.coveredSquares →
            (c, r) ∉ Q.toGridRectangle.coveredSquares := fun h => Finset.disjoint_left.mp hPQ h
        have hD₂ : (c, r) ∈ H.toGridRectangle.coveredSquares →
            (c, r) ∉ S.toGridRectangle.coveredSquares := fun h => Finset.disjoint_left.mp hHS h
        simp only [Finset.mem_union] at hU
        rw [P.mem_coveredSquares_iff_of_ne hca hcb,
          Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ hca hcb,
          Q.mem_coveredSquares_iff_of_ne hca hcb]
        simp only [hca, hcb, false_and, or_false, not_false_eq_true, and_true]
        tauto

/-- The pentagon pair itself underlies no counted composite: the rectangle under a hexagon of
either shape has terminal side `b` or contains both turn rows, while the rectangle of each
pentagon has initial side `b` and contains only one turn row. -/
private theorem initialPair_ne_composite (hrow : P.top ∈ Grid.cIoo P.bottom Q.top)
    (hbot : Q.bottom = P.top) (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F.toRectangleDecomposition ≠
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht : t ∈ Grid.cIco P.top Q.top := hbot ▸ Q.turn_mem_cIco_bottom_top
  have hdisj := Grid.disjoint_cIco_cIco_of_mem_cIoo hrow
  have hnotP : t ∉ Grid.cIco P.bottom P.top := fun h => Finset.disjoint_left.mp hdisj h ht
  have hnotQ : C.turnRow ∉ Grid.cIco Q.bottom Q.top :=
    hbot ▸ fun h => Finset.disjoint_left.mp hdisj hs h
  have key {u v : GridState n} (H : GridCommutationHexagonBetween a C.turnRow t u v) :
      H.toGridRectangleBetween.toGridRectangle ≠ P.toGridRectangle ∧
        H.toGridRectangleBetween.toGridRectangle ≠ Q.toGridRectangle := by
    cases H with
    | inl H =>
      constructor <;> intro h <;>
      · have hr := congrArg GridRectangle.right h
        simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl,
          GridRectangleBetween.toGridRectangle_right, H.right_eq] at hr
        first | exact P.right_ne hr.symm | exact Q.right_ne hr.symm
    | inr H =>
      have hlow : C.turnRow ∈ Grid.cIco H.bottom H.top := H.lower_mem
      have hup : t ∈ Grid.cIco H.bottom H.top :=
        H.insert_cIco_subset_cIco_bottom_top (Finset.mem_insert_self _ _)
      constructor <;> intro h <;>
      · have hb := congrArg GridRectangle.bottom h
        have ht' := congrArg GridRectangle.top h
        simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr,
          GridRectangleBetween.toGridRectangle_bottom,
          GridRectangleBetween.toGridRectangle_top] at hb ht'
        rw [hb, ht'] at hlow hup
        first | exact hnotP hup | exact hnotQ hlow
  intro hFD
  cases F with
  | inl F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hFD
    exact (key F.hexagon).1 (by
      simpa only [GridHexagonRectangleDecomposition.toRectangleDecomposition] using
        congrArg (fun E : GridRectangleDecomposition x z => E.first.toGridRectangle) hFD)
  | inr F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hFD
    exact (key F.hexagon).2 (by
      simpa only [GridRectangleHexagonDecomposition.toRectangleDecomposition] using
        congrArg (fun E : GridRectangleDecomposition x z => E.second.toGridRectangle) hFD)

end Initial

/-! ### Counted and unpaired recuts -/

/-- A crossing-change hexagon followed by a rectangle, both empty, which covers every square with
the multiplicity of a pentagon pair, is a counted composite with the weight of the pair. -/
private theorem inl_mem_and_weight_of_union_inter_eq (R : Type*) [CommSemiring R]
    {x z : GridState n} (T : GridHexagonRectangleDecomposition a C.turnRow t x z)
    (A B : Finset (Fin n × Fin n))
    (hu : A ∪ B.map σ =
      T.hexagon.crossingCoveredSquares ∪ T.rectangle.toGridRectangle.coveredSquares)
    (hi : A ∩ B.map σ =
      T.hexagon.crossingCoveredSquares ∩ T.rectangle.toGridRectangle.coveredSquares)
    (hA : Disjoint A G.XSet) (hB : Disjoint B (G.swapColumns a b).XSet)
    (hh : T.hexagon.toGridRectangleBetween.IsEmpty) (hr : T.rectangle.IsEmpty) :
    Sum.inl T ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
      G.crossingChangeHexagonCompositeWeight C t R (.inl T) =
        (∏ c ∈ G.OColumnsOfSquares A, (MvPolynomial.X c : MvPolynomial (Fin n) R)) *
          ∏ c ∈ G.OColumnsOfSquares (B.map σ), MvPolynomial.X c := by
  obtain ⟨hHX, hSX, hw⟩ := pair_disjoint_and_weight G C R A B _ _ hu hi hA hB
  refine ⟨?_, ?_⟩
  · simp only [inl_mem_crossingChangeHexagonCompositeDecompositions,
      mem_crossingChangeHexagonRectangleDecompositions, mem_unblockedRectangles,
      mem_crossingChangeCommutationHexagons]
    exact ⟨⟨hh, hHX⟩, hr, hSX⟩
  · simp only [hw, crossingChangeHexagonCompositeWeight_inl,
      crossingChangeHexagonRectangleWeight_def,
      crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
      OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares]

/-- A rectangle followed by a crossing-change hexagon, both empty, which covers every square with
the multiplicity of a pentagon pair, is a counted composite with the weight of the pair. -/
private theorem inr_mem_and_weight_of_union_inter_eq (R : Type*) [CommSemiring R]
    {x z : GridState n} (T : GridRectangleHexagonDecomposition a C.turnRow t x z)
    (A B : Finset (Fin n × Fin n))
    (hu : A ∪ B.map σ =
      T.rectangle.toGridRectangle.coveredSquares ∪ T.hexagon.crossingCoveredSquares)
    (hi : A ∩ B.map σ =
      T.rectangle.toGridRectangle.coveredSquares ∩ T.hexagon.crossingCoveredSquares)
    (hA : Disjoint A G.XSet) (hB : Disjoint B (G.swapColumns a b).XSet)
    (hr : T.rectangle.IsEmpty) (hh : T.hexagon.toGridRectangleBetween.IsEmpty) :
    Sum.inr T ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
      G.crossingChangeHexagonCompositeWeight C t R (.inr T) =
        (∏ c ∈ G.OColumnsOfSquares A, (MvPolynomial.X c : MvPolynomial (Fin n) R)) *
          ∏ c ∈ G.OColumnsOfSquares (B.map σ), MvPolynomial.X c := by
  obtain ⟨hSX, hHX, hw⟩ := pair_disjoint_and_weight G C R A B _ _ hu hi hA hB
  refine ⟨?_, ?_⟩
  · simp only [inr_mem_crossingChangeHexagonCompositeDecompositions,
      mem_crossingChangeRectangleHexagonDecompositions, mem_unblockedRectangles,
      mem_crossingChangeCommutationHexagons]
    exact ⟨⟨hr, hSX⟩, hh, hHX⟩
  · simp only [hw, crossingChangeHexagonCompositeWeight_inr,
      crossingChangeRectangleHexagonWeight_def,
      crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
      OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares]

/-! ### The matchings -/

/-- A counted pair of terminal-side pentagons, the first of `G` turning in row `s` and the second
of `G.swapColumns a b` turning in row `t`, with distinct initial sides, recuts to an unpaired
composite of the crossing change homotopy equation with the weight of the pair: the product of
the weight of the first pentagon, renamed by the column swap, and of the second. No assumption on
the placement of the markings is needed. -/
theorem exists_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y) (Q : GridPentagonBetween a t y z)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z)
    (hne : P.left ≠ Q.left) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.pentagonWeight R C P) *
            (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right := terminalPair_right_eq C t P Q
  have hone := D.hasOneCommonSide_of_right_eq_right hcommon hne
  obtain ⟨hrow, htop⟩ := terminalPair_rows C t P Q hne hp hq
  rw [G.rename_pentagonWeight, G.prod_ite_OSet_eq_prod_OColumnsOfSquares,
    swapColumns_pentagonWeight_withTurnRow R]
  -- It suffices to find a counted recut with the weight of the pair.
  suffices h : ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        D.IsRecut F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          (∏ c ∈ G.OColumnsOfSquares P.coveredSquares,
              (MvPolynomial.X c : MvPolynomial (Fin n) R)) *
            ∏ c ∈ G.OColumnsOfSquares (Q.coveredSquares.map σ), MvPolynomial.X c by
    obtain ⟨F, hF, hFD, hw⟩ := h
    exact ⟨F, mem_crossingChangeUnpairedHexagonComposites_of_isRecut hone hp hq
      (fun E _ => terminalPair_ne_composite C t hrow htop E) hF hFD, hFD, hw⟩
  let E := D.recut hone hp hq
  have hrecut : D.IsRecut E := D.isRecut_recut hone hp hq
  have hrep := hrecut.isRepartition
  obtain ⟨hlower, hupper⟩ := terminalPair_turns C t hrow htop
  rcases (D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hne hp hq).1 with hcol | hcol
  · -- The first initial side lies inside the second column interval: rectangle, then hexagon.
    obtain ⟨-, -, -, -, hsb, hst⟩ :=
      D.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol hp hq
    have hsb' : E.second.bottom = Q.bottom := hsb
    have hst' : E.second.top = P.top := hst
    have hsr : E.second.right = b := by
      rcases (D.isRecutOfRightEqRight_recut hcommon hone hp hq).recut_branch with h | h
      · exact h.2.2.2.trans P.right_eq
      · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap D.second.left D.first.right)
          hcol (Grid.mem_cIoo_cyclic_right h.1)).elim
    let H : GridHexagonBetween a t C.turnRow E.middle z :=
      ⟨E.second, hsr, by rw [← E.second.bottom_def, ← E.second.top_def, hsb', hst']; exact hlower,
        by rw [← E.second.top_def, hst']; exact hupper⟩
    obtain ⟨hu, hi⟩ := terminalPair_union_inter_eq C t H E.first hrow htop hsb' hst'
      ((Finset.union_comm _ _).trans hrep.coveredSquares_union_eq)
      hrep.disjoint_coveredSquares_left hrep.disjoint_coveredSquares_right.symm
    obtain ⟨hF, hw⟩ := inr_mem_and_weight_of_union_inter_eq G C t R ⟨E.middle, E.first, .inl H⟩
      _ _ (by simpa only [GridRectangleHexagonDecomposition.hexagon,
          GridCommutationHexagonBetween.crossingCoveredSquares_inl] using
            hu.trans (Finset.union_comm _ _))
      (by simpa only [GridRectangleHexagonDecomposition.hexagon,
          GridCommutationHexagonBetween.crossingCoveredSquares_inl] using
            hi.trans (Finset.inter_comm _ _))
      hpX hqX hrecut.isEmpty_first
      (by simpa only [GridRectangleHexagonDecomposition.hexagon,
          GridCommutationHexagonBetween.toGridRectangleBetween_inl] using hrecut.isEmpty_second)
    refine ⟨_, hF, ?_, hw⟩
    simpa only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
      GridRectangleHexagonDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] using hrecut
  · -- The second initial side lies inside the first column interval: hexagon, then rectangle.
    obtain ⟨hfr, -, hfb, hft, -, -⟩ :=
      D.recut_geometry_of_right_eq_right_of_second_left_mem_cIoo hcommon hcol hp hq
    have hfr' : E.first.right = b := hfr.trans P.right_eq
    have hfb' : E.first.bottom = Q.bottom := hfb
    have hft' : E.first.top = P.top := hft
    let H : GridHexagonBetween a t C.turnRow x E.middle :=
      ⟨E.first, hfr', by rw [← E.first.bottom_def, ← E.first.top_def, hfb', hft']; exact hlower,
        by rw [← E.first.top_def, hft']; exact hupper⟩
    obtain ⟨hu, hi⟩ := terminalPair_union_inter_eq C t H E.second hrow htop hfb' hft'
      hrep.coveredSquares_union_eq hrep.disjoint_coveredSquares_left
      hrep.disjoint_coveredSquares_right
    obtain ⟨hF, hw⟩ := inl_mem_and_weight_of_union_inter_eq G C t R ⟨E.middle, .inl H, E.second⟩
      _ _ (by simpa only [GridHexagonRectangleDecomposition.hexagon,
          GridCommutationHexagonBetween.crossingCoveredSquares_inl] using hu)
      (by simpa only [GridHexagonRectangleDecomposition.hexagon,
          GridCommutationHexagonBetween.crossingCoveredSquares_inl] using hi) hpX hqX
      (by simpa only [GridHexagonRectangleDecomposition.hexagon,
          GridCommutationHexagonBetween.toGridRectangleBetween_inl] using hrecut.isEmpty_first)
      hrecut.isEmpty_second
    refine ⟨_, hF, ?_, hw⟩
    simpa only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
      GridHexagonRectangleDecomposition.toRectangleDecomposition,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] using hrecut

/-- A counted pair of initial-side pentagons, the first of `G` turning in row `s` and the second
of `G.swapColumns a b` turning in row `t`, with distinct terminal sides, recuts to an unpaired
composite of the crossing change homotopy equation with the weight of the pair: the product of
the weight of the first pentagon, renamed by the column swap, and of the second. No assumption on
the placement of the markings is needed. -/
theorem exists_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y) (Q : GridInitialPentagonBetween a t y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z)
    (hne : P.right ≠ Q.right) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
            (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ :=
    ((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := initialPair_left_eq C t P Q
  have hone := D.hasOneCommonSide_of_left_eq_left hcommon hne
  obtain ⟨hrow, hbot⟩ := initialPair_rows C t P Q hne hp hq
  rw [G.rename_initialPentagonWeight, G.prod_ite_OSet_eq_prod_OColumnsOfSquares,
    swapColumns_initialPentagonWeight_withTurnRow R]
  -- It suffices to find a counted recut with the weight of the pair.
  suffices h : ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        D.IsRecut F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          (∏ c ∈ G.OColumnsOfSquares P.coveredSquares,
              (MvPolynomial.X c : MvPolynomial (Fin n) R)) *
            ∏ c ∈ G.OColumnsOfSquares (Q.coveredSquares.map σ), MvPolynomial.X c by
    obtain ⟨F, hF, hFD, hw⟩ := h
    exact ⟨F, mem_crossingChangeUnpairedHexagonComposites_of_isRecut hone hp hq
      (fun E _ => initialPair_ne_composite C t hrow hbot E) hF hFD, hFD, hw⟩
  rcases (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hne hp hq).1 with hcol | hcol
  · -- The first terminal side lies inside the second column interval: rectangle, then hexagon.
    have hcol' : P.right ∈ Grid.cIoo b Q.right := P.left_eq ▸ hcol
    have hrecut := P.isRecut_recutRectangleHexagon Q hcol' hp hq
    have hrows : (P.recutRectangleHexagon Q hcol' hp hq).toRectangleDecomposition.second.bottom =
          P.bottom ∧
        (P.recutRectangleHexagon Q hcol' hp hq).toRectangleDecomposition.second.top = Q.top := by
      rw [P.recutRectangleHexagon_toRectangleDecomposition Q hcol' hp hq]
      exact D.recut_second_bottom_top_of_left_eq_left_of_first_right_mem_cIoo hcommon hcol hp hq
    have hleft := P.recutRectangleHexagon_hexagon_isLeft Q hcol' hp hq
    have hempty := hrecut.isEmpty_second
    set T := P.recutRectangleHexagon Q hcol' hp hq
    -- The recut hexagon turns on its initial side.
    obtain ⟨H, hH⟩ : ∃ H, T.second = Sum.inr H := by
      rcases hT : T.second with H | H
      · simp only [GridRectangleHexagonDecomposition.hexagon, hT, Sum.isLeft_inl,
          Bool.true_eq_false] at hleft
      · exact ⟨H, rfl⟩
    have hrep := hrecut.isRepartition
    simp only [GridRectangleHexagonDecomposition.toRectangleDecomposition, hH,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hrep hrows
    obtain ⟨hu, hi⟩ := initialPair_union_inter_eq C t H T.rectangle hrow hbot hrows.1 hrows.2
      ((Finset.union_comm _ _).trans hrep.coveredSquares_union_eq)
      hrep.disjoint_coveredSquares_left hrep.disjoint_coveredSquares_right.symm
    obtain ⟨hF, hw⟩ := inr_mem_and_weight_of_union_inter_eq G C t R T _ _
      (by simpa only [GridRectangleHexagonDecomposition.hexagon, hH,
          GridCommutationHexagonBetween.crossingCoveredSquares_inr] using
            hu.trans (Finset.union_comm _ _))
      (by simpa only [GridRectangleHexagonDecomposition.hexagon, hH,
          GridCommutationHexagonBetween.crossingCoveredSquares_inr] using
            hi.trans (Finset.inter_comm _ _))
      hpX hqX hrecut.isEmpty_first hempty
    refine ⟨_, hF, ?_, hw⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    exact hrecut
  · -- The second terminal side lies inside the first column interval: hexagon, then rectangle.
    have hcol' : Q.right ∈ Grid.cIoo b P.right := P.left_eq ▸ hcol
    have hrecut := P.isRecut_recutHexagonRectangle Q hcol' hp hq
    have hrows : (P.recutHexagonRectangle Q hcol' hp hq).toRectangleDecomposition.first.bottom =
          P.bottom ∧
        (P.recutHexagonRectangle Q hcol' hp hq).toRectangleDecomposition.first.top = Q.top := by
      rw [P.recutHexagonRectangle_toRectangleDecomposition Q hcol' hp hq]
      exact D.recut_first_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hcol hp hq
    have hleft := P.recutHexagonRectangle_hexagon_isLeft Q hcol' hp hq
    have hempty := hrecut.isEmpty_first
    set T := P.recutHexagonRectangle Q hcol' hp hq
    -- The recut hexagon turns on its initial side.
    obtain ⟨H, hH⟩ : ∃ H, T.first = Sum.inr H := by
      rcases hT : T.first with H | H
      · simp only [GridHexagonRectangleDecomposition.hexagon, hT, Sum.isLeft_inl,
          Bool.true_eq_false] at hleft
      · exact ⟨H, rfl⟩
    have hrep := hrecut.isRepartition
    simp only [GridHexagonRectangleDecomposition.toRectangleDecomposition, hH,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hrep hrows
    obtain ⟨hu, hi⟩ := initialPair_union_inter_eq C t H T.rectangle hrow hbot hrows.1 hrows.2
      hrep.coveredSquares_union_eq hrep.disjoint_coveredSquares_left
      hrep.disjoint_coveredSquares_right
    obtain ⟨hF, hw⟩ := inl_mem_and_weight_of_union_inter_eq G C t R T _ _
      (by simpa only [GridHexagonRectangleDecomposition.hexagon, hH,
          GridCommutationHexagonBetween.crossingCoveredSquares_inr] using hu)
      (by simpa only [GridHexagonRectangleDecomposition.hexagon, hH,
          GridCommutationHexagonBetween.crossingCoveredSquares_inr] using hi)
      hpX hqX hempty hrecut.isEmpty_second
    refine ⟨_, hF, ?_, hw⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    exact hrecut

/-- If the annulus squares carry no `X`-marking, as for the crossing change maps of interleaving
columns, a counted pair of terminal-side pentagons with distinct initial sides has exactly one
unpaired recut composite, and its weight is that of the pair. -/
theorem existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x y z : GridState n} (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween a t y z) (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z)
    (hne : P.left ≠ Q.left) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.pentagonWeight R C P) *
            (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, -⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, -⟩ := ((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hone := D.hasOneCommonSide_of_right_eq_right (terminalPair_right_eq C t P Q) hne
  obtain ⟨F, hF, hFrecut, hFweight⟩ :=
    exists_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair G C t R P Q hP hQ hne
  refine ⟨F, ⟨hF, hFrecut, hFweight⟩, fun F' hF' => ?_⟩
  exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F').mp hF'.1).1
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp hF).1
    ((D.existsUnique_isRecut hone hp hq).unique hF'.2.1 hFrecut)

/-- If the annulus squares carry no `X`-marking, as for the crossing change maps of interleaving
columns, a counted pair of initial-side pentagons with distinct terminal sides has exactly one
unpaired recut composite, and its weight is that of the pair. -/
theorem existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x y z : GridState n} (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a t y z) (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z)
    (hne : P.right ≠ Q.right) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
            (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, -⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, -⟩ :=
    ((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hone := D.hasOneCommonSide_of_left_eq_left (initialPair_left_eq C t P Q) hne
  obtain ⟨F, hF, hFrecut, hFweight⟩ :=
    exists_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair G C t R P Q hP hQ hne
  refine ⟨F, ⟨hF, hFrecut, hFweight⟩, fun F' hF' => ?_⟩
  exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F').mp hF'.1).1
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp hF).1
    ((D.existsUnique_isRecut hone hp hq).unique hF'.2.1 hFrecut)

end TauCeti.GridDiagram
