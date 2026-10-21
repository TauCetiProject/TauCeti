/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Recut

/-!
# Recutting two terminal-side commutation pentagons

Consider a counted forward pentagon and a counted reverse pentagon, both turning on their terminal
side, with distinct initial sides. Their union is an L-shaped domain, which can also be cut along
its other internal edge.

* When the first initial side lies strictly between the second initial side and the common
  terminal side, the recut is a rectangle followed by a terminal-side hexagon.
* When the second initial side lies strictly between the first initial side and the common
  terminal side, the recut is a terminal-side hexagon followed by a rectangle.

In both cases the two turn points lie in order on the hexagon, the resulting composite is counted,
has the same weight as the pentagon pair, and has no hexagon--rectangle recut partner. Hence every
counted off-diagonal pair of terminal-side pentagons is matched with exactly one unpaired hexagon
composite of the same weight.

## Main results

* `GridDiagram.recutTerminalPentagonPair` and
  `GridDiagram.recutTerminalPentagonPairHexagonRectangle`: the recuts in the two branches.
* `GridDiagram.recutTerminalPentagonPair_toRectangleDecomposition` and
  `GridDiagram.recutTerminalPentagonPairHexagonRectangle_toRectangleDecomposition`: their
  underlying rectangle decompositions are the canonical recut.
* `GridDiagram.recutTerminalPentagonPair_mem_rectangleHexagonDecompositions` and
  `GridDiagram.recutTerminalPentagonPairHexagonRectangle_mem_hexagonRectangleDecompositions`:
  countedness.
* `GridDiagram.rectangleHexagonWeight_recutTerminalPentagonPair` and
  `GridDiagram.hexagonRectangleWeight_recutTerminalPentagonPairHexagonRectangle`: weight
  preservation.
* `GridDiagram.recutTerminalPentagonPair_mem_unpairedHexagonComposites` and
  `GridDiagram.recutTerminalPentagonPairHexagonRectangle_mem_unpairedHexagonComposites`: the
  resulting composites have no counted hexagon recut partner.
* `GridDiagram.existsUnique_unpairedHexagonComposite_of_terminalPentagonPair`: a counted pair of
  terminal-side pentagons with distinct initial sides has a unique unpaired hexagon-composite
  recut, of the same weight.

## References

Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559), and Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Section 5.1. The underlying rectangle recuts are
`GridRectangleDecomposition.recut_geometry_of_right_eq_right_of_mem_cIoo` and
`GridRectangleDecomposition.recut_geometry_of_right_eq_right_of_second_left_mem_cIoo`.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

private theorem terminal_pair_right_eq {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z) :
    P.right = Q.right :=
  P.right_eq.trans (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm

private theorem terminal_pair_markings {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top)
    (htop : Q.top = P.bottom) (M : GridState n)
    (ha : M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow))
    (hb : M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow))
    (c : Fin n) :
    ((c, M c) ∈ P.coveredSquares ↔
      c ≠ a ∧ (c, M c) ∈ P.toGridRectangle.coveredSquares) ∧
    ((Equiv.swap a b c, M c) ∈ Q.coveredSquares ↔
      c ≠ a ∧ (c, M c) ∈ Q.toGridRectangle.coveredSquares) := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht : C.oppositeTurnRow ∈ Grid.cIco Q.bottom Q.top := by
    simpa only [C.reverse_turnRow] using Q.turn_mem_cIco_bottom_top
  rw [htop] at ht
  rcases eq_or_ne c a with rfl | hca
  · have hQ := Q.mk_mem_coveredSquares_right_column (M a)
    simp only [C.reverse_column, C.reverse_turnRow] at hQ
    simp only [Equiv.swap_apply_left, P.mk_mem_coveredSquares_left_column,
      hQ, ne_eq, not_true_eq_false, false_and]
    simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq,
      ← Fin.val_inj] at hs ht ha hrow ⊢
    constructor <;> constructor <;> intro h <;> split_ifs at * <;> grind
  · rcases eq_or_ne c b with rfl | hcb
    · have hQ := Q.mk_mem_coveredSquares_left_column (M b)
      have hQrect := Q.mk_notMem_toGridRectangle_coveredSquares_right_column (M b)
      simp only [C.reverse_column, C.reverse_turnRow] at hQ hQrect
      simp only [Equiv.swap_apply_right, P.mk_mem_coveredSquares_right_column,
        P.mk_notMem_toGridRectangle_coveredSquares_right_column, hQ, hQrect,
        htop]
      simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq,
        ← Fin.val_inj] at hs ht hb hrow ⊢
      constructor <;> constructor <;> intro h <;> split_ifs at * <;> grind
    · have hQ := Q.mem_coveredSquares_iff_of_ne (p := (c, M c))
        (by simpa only [C.reverse_column] using hca)
        (by simpa only [C.reverse_column] using hcb)
      simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
        P.mem_coveredSquares_iff_of_ne (p := (c, M c)) hca hcb, hQ]
      tauto

private theorem terminal_pair_rows {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hne : P.left ≠ Q.left) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    P.bottom ∈ Grid.cIoo Q.bottom P.top ∧ Q.top = P.bottom := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  refine ⟨(D.cyclicOrder_of_isEmpty_of_right_eq_right (G.terminal_pair_right_eq C P Q)
    hne hp hq).2, ?_⟩
  rw [GridRectangleBetween.top_def, ← G.terminal_pair_right_eq C P Q, P.map_right,
    GridRectangleBetween.bottom_def]

/-- Both turn rows lie on the common terminal side of the union, the reverse turn row below the
forward one. -/
private theorem terminal_pair_turns {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom) :
    C.oppositeTurnRow ∈ Grid.cIco Q.bottom P.top ∧
      C.turnRow ∈ Grid.cIoo C.oppositeTurnRow P.top := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht : C.oppositeTurnRow ∈ Grid.cIco Q.bottom Q.top := by
    simpa only [C.reverse_turnRow] using Q.turn_mem_cIco_bottom_top
  rw [htop] at ht
  refine ⟨Grid.mem_cIco_of_mem_cIco_of_mem_cIoo ht hrow, ?_⟩
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hs ht hrow ⊢
  split_ifs at * <;> omega

/-- Away from column `a`, a square covered by the union of the two pentagons carries no
`X`-marking. -/
private theorem terminal_pair_notMem_XSet {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom)
    (hpX : Disjoint P.coveredSquares G.XSet)
    (hqX : Disjoint Q.coveredSquares (G.swapColumns a b).XSet)
    {p : Fin n × Fin n} (hpa : p.1 ≠ a)
    (hmem : p ∈ P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares) :
    p ∉ G.XSet := by
  rcases p with ⟨c, r⟩
  intro hX
  have hr : r = G.X c := ((G.mem_XSet _).mp hX).symm
  subst r
  have hmarks := G.terminal_pair_markings C P Q hrow htop G.X
    C.X_column_below C.X_next_above c
  rcases Finset.mem_union.mp hmem with h | h
  · exact Finset.disjoint_left.mp hpX (hmarks.1.mpr ⟨hpa, h⟩) hX
  · have hQX : (Equiv.swap a b c, G.X c) ∈ (G.swapColumns a b).XSet := by
      simp only [G.mem_XSet_swapColumns, Equiv.swap_apply_self]
      exact hX
    exact Finset.disjoint_left.mp hqX (hmarks.2.mpr ⟨hpa, h⟩) hQX

private theorem terminal_pair_hexagon {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    let D : GridRectangleDecomposition x z :=
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
    let hone := D.hasOneCommonSide_of_right_eq_right
      (P.right_eq.trans
        (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm)
      (Grid.ne_left_of_mem_cIoo hcol)
    let E := D.recut hone hp hq
    ∃ H : GridHexagonBetween a C.oppositeTurnRow C.turnRow E.middle z,
      H.toGridRectangleBetween = E.second := by
  intro D hone E
  have hcommon : D.first.right = D.second.right := G.terminal_pair_right_eq C P Q
  have hcol' : D.first.left ∈ Grid.cIoo D.second.left D.first.right := by
    dsimp only [D]
    rw [P.right_eq]
    exact hcol
  obtain ⟨hfr, hsl, hfb, hft, hsb, hst⟩ :=
    D.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol' hp hq
  have hsb' : E.second.bottom = Q.bottom := hsb
  have hst' : E.second.top = P.top := hst
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hp hq
  have hsr : E.second.right = b := by
    rcases hdata.recut_branch with h | h
    · exact h.2.2.2.trans P.right_eq
    · have hbad : Q.left ∈ Grid.cIoo P.left b := by
        simpa only [D, P.right_eq] using h.1
      exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap Q.left b) hcol
        (Grid.mem_cIoo_cyclic_right hbad)).elim
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol) hp hq
  obtain ⟨hlower, hupper⟩ := G.terminal_pair_turns C P Q hrow htop
  have hlower' : C.oppositeTurnRow ∈ Grid.cIco E.second.bottom E.second.top := by
    rw [hsb', hst']
    exact hlower
  have hupper' : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow E.second.top := by
    rw [hst']
    exact hupper
  exact ⟨{ toGridRectangleBetween := E.second
           right_eq := hsr
           lower_mem := hlower'
           upper_mem := hupper' }, rfl⟩

/-- Recut two terminal-side pentagons when the first initial side lies strictly inside the
second column interval. The second piece is a terminal-side hexagon containing both turns. -/
noncomputable def recutTerminalPentagonPair {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    GridRectangleHexagonDecomposition a C.turnRow C.oppositeTurnRow x z :=
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  let hone := D.hasOneCommonSide_of_right_eq_right
    (P.right_eq.trans
      (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm)
    (Grid.ne_left_of_mem_cIoo hcol)
  let E := D.recut hone hp hq
  ⟨E.middle, E.first, .inl (G.terminal_pair_hexagon C P Q hcol hp hq).choose⟩

/-- Forgetting the two turns in the promoted composite gives the canonical rectangle recut. -/
@[simp]
theorem recutTerminalPentagonPair_toRectangleDecomposition {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    let D : GridRectangleDecomposition x z :=
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
    let hone := D.hasOneCommonSide_of_right_eq_right
      (P.right_eq.trans
        (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm)
      (Grid.ne_left_of_mem_cIoo hcol)
    (G.recutTerminalPentagonPair C P Q hcol hp hq).toRectangleDecomposition =
      D.recut hone hp hq := by
  intro D hone
  have h := (G.terminal_pair_hexagon C P Q hcol hp hq).choose_spec
  simp only [recutTerminalPentagonPair,
    GridRectangleHexagonDecomposition.toRectangleDecomposition,
    GridCommutationHexagonBetween.toGridRectangleBetween_inl, h]
  rfl

/-- The promoted composite and the pentagon pair are the two cuts of the same domain. -/
theorem isRecut_recutTerminalPentagonPair {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecut
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z)
      (G.recutTerminalPentagonPair C P Q hcol hp hq).toRectangleDecomposition := by
  rw [G.recutTerminalPentagonPair_toRectangleDecomposition C]
  exact GridRectangleDecomposition.isRecut_recut _ _ _ _

private theorem terminal_pair_marking_filters {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top)
    (htop : Q.top = P.bottom) (M : GridState n)
    (ha : M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow))
    (hb : M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow)) :
    P.coveredSquares.filter (· ∈ M.pointSet) =
        P.toGridRectangle.coveredSquares.filter (fun p => p.1 ≠ a ∧ p ∈ M.pointSet) ∧
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding).filter
          (· ∈ M.pointSet) =
        Q.toGridRectangle.coveredSquares.filter (fun p => p.1 ≠ a ∧ p ∈ M.pointSet) := by
  classical
  constructor
  · ext ⟨c, r⟩
    simp only [Finset.mem_filter, M.mem_pointSet]
    have h := (G.terminal_pair_markings C P Q hrow htop M ha hb c).1
    by_cases hr : r = M c
    · subst r
      tauto
    · tauto
  · ext ⟨c, r⟩
    simp only [Finset.mem_filter, Finset.mem_map_equiv, Equiv.prodCongr_symm,
      Equiv.symm_swap, Equiv.prodCongr_apply, Equiv.refl_symm,
      M.mem_pointSet]
    have h := (G.terminal_pair_markings C P Q hrow htop M ha hb c).2
    by_cases hr : r = M c
    · subst r
      tauto
    · tauto

/-- The weight of a square of the original diagram shared by both cuts of a terminal-side
pentagon pair: the variable of an `O`-marking outside column `a`, and `1` elsewhere. -/
private noncomputable def terminalPairSquareWeight (R : Type*) [CommSemiring R]
    (p : Fin n × Fin n) : MvPolynomial (Fin n) R :=
  if p.1 ≠ a ∧ p ∈ G.OSet then MvPolynomial.X p.1 else 1

private theorem pentagonPairWeight_terminal_pair (R : Type*) [CommSemiring R]
    {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom) :
    G.pentagonPairWeight C R ⟨y, .inl P, .inl Q⟩ =
      (∏ p ∈ P.toGridRectangle.coveredSquares, G.terminalPairSquareWeight C R p) *
        ∏ p ∈ Q.toGridRectangle.coveredSquares, G.terminalPairSquareWeight C R p := by
  classical
  have hfilters := G.terminal_pair_marking_filters C P Q hrow htop G.O
    C.O_column_below C.O_next_above
  rw [← G.OSet_def] at hfilters
  simp only [terminalPairSquareWeight]
  rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inl,
    (G.swapColumns a b).commutationPentagonWeight_inl, G.rename_pentagonWeight,
    G.pentagonWeight_reverse, ← Finset.prod_filter, ← Finset.prod_filter, hfilters.1,
    hfilters.2, Finset.prod_filter, Finset.prod_filter]

private theorem hexagonWeight_eq_prod_terminalPairSquareWeight (R : Type*) [CommSemiring R]
    {s s' : Fin n} {u v : GridState n} (H : GridHexagonBetween a s s' u v) :
    G.hexagonWeight R H =
      ∏ p ∈ H.toGridRectangle.coveredSquares, G.terminalPairSquareWeight C R p := by
  classical
  simp only [terminalPairSquareWeight]
  rw [G.hexagonWeight_eq_prod_coveredSquares, ← Finset.prod_filter, ← Finset.prod_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, H.mem_coveredSquares]
  tauto

private theorem OMonomial_eq_prod_terminalPairSquareWeight (R : Type*) [CommSemiring R]
    (r : GridRectangle n) (hr : ∀ p ∈ r.coveredSquares, p.1 ≠ a) :
    G.OMonomial R r = ∏ p ∈ r.coveredSquares, G.terminalPairSquareWeight C R p := by
  rw [G.OMonomial_eq_prod_coveredSquares]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hc := hr p hp
  simp only [terminalPairSquareWeight]
  split_ifs <;> tauto

/-- The hexagon in this recut turns on its terminal side. -/
theorem recutTerminalPentagonPair_hexagon {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    ∃ H : GridHexagonBetween a C.oppositeTurnRow C.turnRow
        (G.recutTerminalPentagonPair C P Q hcol hp hq).middle z,
      (G.recutTerminalPentagonPair C P Q hcol hp hq).hexagon = .inl H := by
  exact ⟨_, rfl⟩

private theorem recutTerminalPentagonPair_rectangle_not_column {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty)
    {p : Fin n × Fin n}
    (hmem : p ∈
      (G.recutTerminalPentagonPair C P Q hcol hp hq).rectangle.toGridRectangle.coveredSquares) :
    p.1 ≠ a := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  let hone := D.hasOneCommonSide_of_right_eq_right
    (P.right_eq.trans
      (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm)
    (Grid.ne_left_of_mem_cIoo hcol)
  have hcommon : D.first.right = D.second.right :=
    P.right_eq.trans (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hp hq
  have hcol' : D.first.left ∈ Grid.cIoo D.second.left D.first.right := by
    dsimp only [D]
    rwa [P.right_eq]
  have hfr := (D.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol' hp hq).1
  have heq := G.recutTerminalPentagonPair_toRectangleDecomposition C P Q hcol hp hq
  have hleft := congrArg (fun E : GridRectangleDecomposition x z => E.first.left) heq
  have hright := congrArg (fun E : GridRectangleDecomposition x z => E.first.right) heq
  have hc := ((GridRectangle.mem_coveredSquares _ _).mp hmem).1
  rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, hleft, hright,
    hdata.recut_sides.1, hfr] at hc
  have htail := (Grid.self_mem_cIco_finRotate P.left_ne : a ∈ Grid.cIco P.left b)
  have hc' : p.1 ∈ Grid.cIco Q.left P.left := hc
  intro h
  rw [h] at hc'
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol) hc' htail

/-- The recut of a counted terminal-side pentagon pair is a counted rectangle--hexagon
composite for this order of the initial columns. -/
theorem recutTerminalPentagonPair_mem_rectangleHexagonDecompositions {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z) :
    G.recutTerminalPentagonPair C P Q hcol
        ((G.mem_pentagons P).mp hP).1
        (((G.swapColumns a b).mem_pentagons Q).mp hQ).1 ∈
      G.rectangleHexagonDecompositions C x z := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons Q).mp hQ
  let T := G.recutTerminalPentagonPair C P Q hcol hp hq
  have hrecut := G.isRecut_recutTerminalPentagonPair C P Q hcol hp hq
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol) hp hq
  have havoid : ∀ p : Fin n × Fin n, p.1 ≠ a →
      p ∈ T.rectangle.toGridRectangle.coveredSquares ∪
        T.hexagon.toGridRectangleBetween.toGridRectangle.coveredSquares → p ∉ G.XSet := by
    intro p hpa hmem
    rw [hrecut.isRepartition.coveredSquares_union_eq] at hmem
    exact G.terminal_pair_notMem_XSet C P Q hrow htop hpX hqX hpa hmem
  obtain ⟨H, hH⟩ := G.recutTerminalPentagonPair_hexagon C P Q hcol hp hq
  have hHX : Disjoint H.coveredSquares G.XSet := by
    refine Finset.disjoint_left.mpr fun p hpH => havoid p ((H.mem_coveredSquares p).mp hpH).1 ?_
    rw [hH, GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact Finset.mem_union.mpr (Or.inr ((H.mem_coveredSquares p).mp hpH).2)
  refine (G.mem_rectangleHexagonDecompositions C T).mpr ⟨?_, ?_⟩
  · exact (G.mem_unblockedRectangles T.rectangle).mpr ⟨hrecut.isEmpty_first,
      Finset.disjoint_left.mpr fun p hpT => havoid p
        (G.recutTerminalPentagonPair_rectangle_not_column C P Q hcol hp hq hpT)
        (Finset.mem_union.mpr (Or.inl hpT))⟩
  · rw [hH, mem_commutationHexagons, GridCommutationHexagonBetween.toGridRectangleBetween_inl,
      GridCommutationHexagonBetween.coveredSquares_inl]
    exact ⟨by simpa only [hH,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] using hrecut.isEmpty_second, hHX⟩

/-- Recutting this terminal-side pentagon pair preserves its polynomial weight, over any
commutative semiring. -/
@[simp]
theorem rectangleHexagonWeight_recutTerminalPentagonPair
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    G.rectangleHexagonWeight C R (G.recutTerminalPentagonPair C P Q hcol hp hq) =
      G.pentagonPairWeight C R ⟨y, .inl P, .inl Q⟩ := by
  have hrecut := G.isRecut_recutTerminalPentagonPair C P Q hcol hp hq
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol) hp hq
  obtain ⟨H, hH⟩ := G.recutTerminalPentagonPair_hexagon C P Q hcol hp hq
  have hweight := hrecut.isRepartition.prod_coveredSquares_mul_prod_coveredSquares
    (G.terminalPairSquareWeight C R)
  simp only [hH, GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hweight
  rw [G.rectangleHexagonWeight_def, hH, G.commutationHexagonWeight_inl,
    G.OMonomial_eq_prod_terminalPairSquareWeight C R _ fun p hpT =>
      G.recutTerminalPentagonPair_rectangle_not_column C P Q hcol hp hq hpT,
    G.hexagonWeight_eq_prod_terminalPairSquareWeight C R H, hweight,
    G.pentagonPairWeight_terminal_pair C R P Q hrow htop]

private theorem terminal_pair_no_hexagon {x y z u v : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom)
    (H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow u v) :
    H.toGridRectangleBetween.toGridRectangle ≠ P.toGridRectangle ∧
      H.toGridRectangleBetween.toGridRectangle ≠ Q.toGridRectangle := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht : C.oppositeTurnRow ∈ Grid.cIco Q.bottom P.bottom := by
    simpa only [C.reverse_turnRow, htop] using Q.turn_mem_cIco_bottom_top
  have hdisj := Grid.disjoint_cIco_cIco_of_mem_cIoo hrow
  have hnotP : C.oppositeTurnRow ∉ Grid.cIco P.bottom P.top :=
    fun h => Finset.disjoint_left.mp hdisj ht h
  have hnotQ : C.turnRow ∉ Grid.cIco Q.bottom Q.top := by
    rw [htop]
    exact fun h => Finset.disjoint_left.mp hdisj h hs
  cases H with
  | inl H =>
    constructor <;> intro h
    · have hb := congrArg GridRectangle.bottom h
      have ht' := congrArg GridRectangle.top h
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl,
        GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top] at hb ht'
      have hmem : C.oppositeTurnRow ∈ Grid.cIco H.bottom H.top := H.lower_mem
      exact hnotP (by simpa only [hb, ht'] using hmem)
    · have hb := congrArg GridRectangle.bottom h
      have ht' := congrArg GridRectangle.top h
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl,
        GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top] at hb ht'
      have hturn := H.insert_cIco_subset_cIco_bottom_top (Finset.mem_insert_self _ _)
      exact hnotQ (by simpa only [hb, ht'] using hturn)
  | inr H =>
    constructor <;> intro h
    · have hl := congrArg GridRectangle.left h
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr,
        GridRectangleBetween.toGridRectangle_left, H.left_eq] at hl
      exact P.left_ne hl.symm
    · have hl := congrArg GridRectangle.left h
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr,
        GridRectangleBetween.toGridRectangle_left, H.left_eq] at hl
      exact Q.left_ne (hl.symm.trans (congrArg (finRotate n) C.reverse_column).symm)

/-- No counted composite has the pentagon pair as its underlying rectangle decomposition: each
pentagon contains only one of the two turn points. -/
private theorem terminal_pair_ne_composite {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom)
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    F.toRectangleDecomposition ≠
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) := by
  intro hFD
  cases F with
  | inl F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hFD
    exact (G.terminal_pair_no_hexagon C P Q hrow htop F.hexagon).1
      (by
        simpa only [GridHexagonRectangleDecomposition.toRectangleDecomposition] using
          congrArg (fun E : GridRectangleDecomposition x z => E.first.toGridRectangle) hFD)
  | inr F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hFD
    exact (G.terminal_pair_no_hexagon C P Q hrow htop F.hexagon).2
      (by
        simpa only [GridRectangleHexagonDecomposition.toRectangleDecomposition] using
          congrArg (fun E : GridRectangleDecomposition x z => E.second.toGridRectangle) hFD)

/-- The resulting counted composite is unpaired: its only rectangle recut consists of
the two pentagons, each of which contains only one of the two turn points. -/
theorem recutTerminalPentagonPair_mem_unpairedHexagonComposites {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : P.left ∈ Grid.cIoo Q.left b)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z) :
    Sum.inr (G.recutTerminalPentagonPair C P Q hcol
        ((G.mem_pentagons P).mp hP).1
        (((G.swapColumns a b).mem_pentagons Q).mp hQ).1) ∈
      G.unpairedHexagonComposites C x z := by
  obtain ⟨hp, -⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, -⟩ := ((G.swapColumns a b).mem_pentagons Q).mp hQ
  let T := G.recutTerminalPentagonPair C P Q hcol hp hq
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hone := D.hasOneCommonSide_of_right_eq_right (G.terminal_pair_right_eq C P Q)
    (Grid.ne_left_of_mem_cIoo hcol)
  have hrecut := G.isRecut_recutTerminalPentagonPair C P Q hcol hp hq
  have hTone : T.toRectangleDecomposition.HasOneCommonSide := by
    rw [G.recutTerminalPentagonPair_toRectangleDecomposition C]
    exact D.hasOneCommonSide_recut hone hp hq
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol) hp hq
  refine (G.mem_unpairedHexagonComposites C (.inr T)).mpr ⟨?_, ?_, ?_⟩
  · exact (G.inr_mem_hexagonCompositeDecompositions C T).mpr
      (G.recutTerminalPentagonPair_mem_rectangleHexagonDecompositions C P Q hcol hP hQ)
  · simpa only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] using
      T.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide hTone
  · intro F _ hF
    simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hF
    exact G.terminal_pair_ne_composite C P Q hrow htop F
      ((T.toRectangleDecomposition.existsUnique_isRecut hTone
        hrecut.isEmpty_first hrecut.isEmpty_second).unique hF (hrecut.symm hone hp hq))

/-! ### The complementary branch -/

/-- Recut two empty terminal-side pentagons when the second initial side lies strictly inside the
first column interval. The first piece is a terminal-side hexagon containing both turns. -/
noncomputable def recutTerminalPentagonPairHexagonRectangle {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    GridHexagonRectangleDecomposition a C.turnRow C.oppositeTurnRow x z := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right := G.terminal_pair_right_eq C P Q
  have hc : D.second.left ∈ Grid.cIoo D.first.left D.first.right := P.right_eq ▸ hcol
  let E := D.recut (D.hasOneCommonSide_of_right_eq_right hcommon
    (Grid.ne_left_of_mem_cIoo hc).symm) hp hq
  have hgeom := D.recut_geometry_of_right_eq_right_of_second_left_mem_cIoo hcommon hc hp hq
  have hbottom : E.first.bottom = Q.bottom := hgeom.2.2.1
  have htop : E.first.top = P.top := hgeom.2.2.2.1
  have hrows := G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol).symm hp hq
  have hturns := G.terminal_pair_turns C P Q hrows.1 hrows.2
  exact ⟨E.middle, Sum.inl ⟨E.first, hgeom.1.trans P.right_eq,
    by simpa only [← E.first.bottom_def, ← E.first.top_def, hbottom, htop] using hturns.1,
    by simpa only [← E.first.top_def, htop] using hturns.2⟩, E.second⟩

/-- Forgetting the two turns in this composite gives the canonical rectangle recut. -/
@[simp]
theorem recutTerminalPentagonPairHexagonRectangle_toRectangleDecomposition {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq).toRectangleDecomposition =
      GridRectangleDecomposition.recut
        (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
          GridRectangleDecomposition x z)
        (GridRectangleDecomposition.hasOneCommonSide_of_right_eq_right _
          (P.right_eq.trans (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm)
          (Grid.ne_left_of_mem_cIoo hcol).symm) hp hq := by
  simp only [recutTerminalPentagonPairHexagonRectangle,
    GridHexagonRectangleDecomposition.toRectangleDecomposition,
    GridCommutationHexagonBetween.toGridRectangleBetween_inl]

/-- This composite and the pentagon pair are the two cuts of the same domain. -/
theorem isRecut_recutTerminalPentagonPairHexagonRectangle {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecut
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z)
      (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq).toRectangleDecomposition := by
  rw [G.recutTerminalPentagonPairHexagonRectangle_toRectangleDecomposition C]
  exact GridRectangleDecomposition.isRecut_recut _ _ _ _

/-- The hexagon in this recut turns on its terminal side. -/
theorem recutTerminalPentagonPairHexagonRectangle_hexagon {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    ∃ H : GridHexagonBetween a C.oppositeTurnRow C.turnRow x
        (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq).middle,
      (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq).hexagon = .inl H :=
  ⟨_, rfl⟩

private theorem recutTerminalPentagonPairHexagonRectangle_rectangle_not_column
    {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty)
    {p : Fin n × Fin n}
    (hmem : p ∈ GridRectangle.coveredSquares
      (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq).rectangle.toGridRectangle) :
    p.1 ≠ a := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right := G.terminal_pair_right_eq C P Q
  have hc : D.second.left ∈ Grid.cIoo D.first.left D.first.right := P.right_eq ▸ hcol
  have hone := D.hasOneCommonSide_of_right_eq_right hcommon (Grid.ne_left_of_mem_cIoo hc).symm
  have hleft := (D.isRecutOfRightEqRight_recut hcommon hone hp hq).recut_sides.2
  obtain ⟨-, hright, -⟩ :=
    D.recut_geometry_of_right_eq_right_of_second_left_mem_cIoo hcommon hc hp hq
  rw [← G.recutTerminalPentagonPairHexagonRectangle_toRectangleDecomposition C P Q hcol hp hq]
    at hleft hright
  have hleft' :
      (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq).rectangle.left = P.left :=
    hleft
  have hright' :
      (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq).rectangle.right = Q.left :=
    hright
  have hcolumn := ((GridRectangle.mem_coveredSquares _ _).mp hmem).1
  simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, hleft', hright'] at hcolumn
  intro h
  rw [h] at hcolumn
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol) hcolumn
    (Grid.self_mem_cIco_finRotate (Grid.ne_right_of_mem_cIoo hcol))

/-- The recut of a counted terminal-side pentagon pair is a counted hexagon--rectangle
composite for this order of the initial columns. -/
theorem recutTerminalPentagonPairHexagonRectangle_mem_hexagonRectangleDecompositions
    {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z) :
    G.recutTerminalPentagonPairHexagonRectangle C P Q hcol
        ((G.mem_pentagons P).mp hP).1
        (((G.swapColumns a b).mem_pentagons Q).mp hQ).1 ∈
      G.hexagonRectangleDecompositions C x z := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons Q).mp hQ
  let T := G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq
  have hrecut := G.isRecut_recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq
  obtain ⟨hrow, htop⟩ :=
    G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol).symm hp hq
  have havoid : ∀ p : Fin n × Fin n, p.1 ≠ a →
      p ∈ T.hexagon.toGridRectangleBetween.toGridRectangle.coveredSquares ∪
        T.rectangle.toGridRectangle.coveredSquares → p ∉ G.XSet := by
    intro p hpa hmem
    rw [hrecut.isRepartition.coveredSquares_union_eq] at hmem
    exact G.terminal_pair_notMem_XSet C P Q hrow htop hpX hqX hpa hmem
  obtain ⟨H, hH⟩ := G.recutTerminalPentagonPairHexagonRectangle_hexagon C P Q hcol hp hq
  have hHX : Disjoint H.coveredSquares G.XSet := by
    refine Finset.disjoint_left.mpr fun p hpH => havoid p ((H.mem_coveredSquares p).mp hpH).1 ?_
    rw [hH, GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact Finset.mem_union.mpr (Or.inl ((H.mem_coveredSquares p).mp hpH).2)
  refine (G.mem_hexagonRectangleDecompositions C T).mpr ⟨?_, ?_⟩
  · rw [hH, mem_commutationHexagons, GridCommutationHexagonBetween.toGridRectangleBetween_inl,
      GridCommutationHexagonBetween.coveredSquares_inl]
    exact ⟨by simpa only [hH,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl] using hrecut.isEmpty_first, hHX⟩
  · exact (G.mem_unblockedRectangles T.rectangle).mpr ⟨hrecut.isEmpty_second,
      Finset.disjoint_left.mpr fun p hpT => havoid p
        (G.recutTerminalPentagonPairHexagonRectangle_rectangle_not_column C P Q hcol hp hq hpT)
        (Finset.mem_union.mpr (Or.inr hpT))⟩

/-- Recutting this terminal-side pentagon pair preserves its polynomial weight, over any
commutative semiring. -/
@[simp]
theorem hexagonRectangleWeight_recutTerminalPentagonPairHexagonRectangle
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    G.hexagonRectangleWeight C R (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq) =
      G.pentagonPairWeight C R ⟨y, .inl P, .inl Q⟩ := by
  have hrecut := G.isRecut_recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq
  obtain ⟨hrow, htop⟩ :=
    G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol).symm hp hq
  obtain ⟨H, hH⟩ := G.recutTerminalPentagonPairHexagonRectangle_hexagon C P Q hcol hp hq
  have hweight := hrecut.isRepartition.prod_coveredSquares_mul_prod_coveredSquares
    (G.terminalPairSquareWeight C R)
  simp only [hH, GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hweight
  rw [G.hexagonRectangleWeight_def, hH, G.commutationHexagonWeight_inl,
    G.hexagonWeight_eq_prod_terminalPairSquareWeight C R H,
    G.OMonomial_eq_prod_terminalPairSquareWeight C R _ fun p hpT =>
      G.recutTerminalPentagonPairHexagonRectangle_rectangle_not_column C P Q hcol hp hq hpT,
    hweight, G.pentagonPairWeight_terminal_pair C R P Q hrow htop]

/-- This counted composite is unpaired: its only rectangle recut consists of the two pentagons,
each of which contains only one of the two turn points. -/
theorem recutTerminalPentagonPairHexagonRectangle_mem_unpairedHexagonComposites
    {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hcol : Q.left ∈ Grid.cIoo P.left b)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z) :
    Sum.inl (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol
        ((G.mem_pentagons P).mp hP).1
        (((G.swapColumns a b).mem_pentagons Q).mp hQ).1) ∈
      G.unpairedHexagonComposites C x z := by
  obtain ⟨hp, -⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, -⟩ := ((G.swapColumns a b).mem_pentagons Q).mp hQ
  let T := G.recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hone := D.hasOneCommonSide_of_right_eq_right (G.terminal_pair_right_eq C P Q)
    (Grid.ne_left_of_mem_cIoo hcol).symm
  have hrecut := G.isRecut_recutTerminalPentagonPairHexagonRectangle C P Q hcol hp hq
  have hTone : T.toRectangleDecomposition.HasOneCommonSide := by
    rw [G.recutTerminalPentagonPairHexagonRectangle_toRectangleDecomposition C]
    exact D.hasOneCommonSide_recut hone hp hq
  obtain ⟨hrow, htop⟩ :=
    G.terminal_pair_rows C P Q (Grid.ne_left_of_mem_cIoo hcol).symm hp hq
  refine (G.mem_unpairedHexagonComposites C (.inl T)).mpr ⟨?_, ?_, ?_⟩
  · exact (G.inl_mem_hexagonCompositeDecompositions C T).mpr
      (G.recutTerminalPentagonPairHexagonRectangle_mem_hexagonRectangleDecompositions
        C P Q hcol hP hQ)
  · simpa only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] using
      T.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide hTone
  · intro F _ hF
    simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hF
    exact G.terminal_pair_ne_composite C P Q hrow htop F
      ((T.toRectangleDecomposition.existsUnique_isRecut hTone
        hrecut.isEmpty_first hrecut.isEmpty_second).unique hF (hrecut.symm hone hp hq))

/-! ### The matching -/

/-- A counted pair of terminal-side pentagons, for an actual commutation and its reverse, with
distinct initial sides has a unique unpaired hexagon-composite recut, and their polynomial
weights agree. -/
theorem existsUnique_unpairedHexagonComposite_of_terminalPentagonPair
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z)
    (hne : P.left ≠ Q.left) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inl P, .inl Q⟩ := by
  obtain ⟨hp, -⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, -⟩ := ((G.swapColumns a b).mem_pentagons Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hone := D.hasOneCommonSide_of_right_eq_right (G.terminal_pair_right_eq C P Q) hne
  -- Emptiness of both pentagons leaves exactly the two orders of the initial sides.
  have hexists : ∃ F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧ D.IsRecut F.toRectangleDecomposition ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inl P, .inl Q⟩ := by
    rcases (D.cyclicOrder_of_isEmpty_of_right_eq_right (G.terminal_pair_right_eq C P Q)
        hne hp hq).1 with hcol | hcol
    · have hcol' : P.left ∈ Grid.cIoo Q.left b := by
        simpa only [D, P.right_eq] using hcol
      refine ⟨.inr (G.recutTerminalPentagonPair C P Q hcol' hp hq),
        G.recutTerminalPentagonPair_mem_unpairedHexagonComposites C P Q hcol' hP hQ, ?_, ?_⟩
      · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
        exact G.isRecut_recutTerminalPentagonPair C P Q hcol' hp hq
      · rw [G.hexagonCompositeWeight_inr]
        exact G.rectangleHexagonWeight_recutTerminalPentagonPair C R P Q hcol' hp hq
    · have hcol' : Q.left ∈ Grid.cIoo P.left b := by
        simpa only [D, P.right_eq] using hcol
      refine ⟨.inl (G.recutTerminalPentagonPairHexagonRectangle C P Q hcol' hp hq),
        G.recutTerminalPentagonPairHexagonRectangle_mem_unpairedHexagonComposites
          C P Q hcol' hP hQ, ?_, ?_⟩
      · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
        exact G.isRecut_recutTerminalPentagonPairHexagonRectangle C P Q hcol' hp hq
      · rw [G.hexagonCompositeWeight_inl]
        exact G.hexagonRectangleWeight_recutTerminalPentagonPairHexagonRectangle C R P Q hcol' hp hq
  obtain ⟨F, hF, hFrecut, hFweight⟩ := hexists
  refine ⟨F, ⟨hF, hFrecut, hFweight⟩, fun F' hF' => ?_⟩
  exact G.injOn_toRectangleDecomposition_hexagonCompositeDecompositions C x z
    ((G.mem_unpairedHexagonComposites C F').mp hF'.1).1
    ((G.mem_unpairedHexagonComposites C F).mp hF).1
    ((D.existsUnique_isRecut hone hp hq).unique hF'.2.1 hFrecut)

end TauCeti.GridDiagram
