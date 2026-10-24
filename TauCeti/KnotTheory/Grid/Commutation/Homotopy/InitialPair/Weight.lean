/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.InitialPair.Basic

/-!
# Weights of initial-side pentagon-pair recuts

When two initial-side commutation pentagons recut to a hexagon--rectangle composite in either
order, the recut preserves the polynomial weight. In the two columns adjacent to the replaced
line, the bigon conditions remove precisely the markings in the column cut away by the hexagon.
Away from that column the assertion follows from the rectangle repartition.

For a counted forward pentagon and a counted reverse pentagon in this branch, there is
exactly one unpaired hexagon composite recutting their domain. Its weight is the weight of the
pentagon pair, including the renaming of the forward coefficient. The two cyclic column orders
exhaust the initial--initial pairs with distinct terminal sides. This is their part of the
weighted matching needed to compare the two sides of the commutation homotopy equation; the
converse assertion that every unpaired composite arises this way is not made here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559). The weight argument follows the terminal-side
counterpart in `TauCeti.KnotTheory.Grid.Commutation.Homotopy.TerminalPair`.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

private theorem initial_pair_rows {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y z)
    (hright : P.right ≠ Q.right) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    P.top ∈ Grid.cIoo P.bottom Q.top ∧ Q.bottom = P.top := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  exact ⟨(D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    hright hp hq).2,
    D.second_bottom_eq_first_top_of_left_eq_left hcommon⟩

private theorem initial_pair_markings {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y z)
    (hrow : P.top ∈ Grid.cIoo P.bottom Q.top) (hbottom : Q.bottom = P.top)
    (M : GridState n)
    (ha : M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow))
    (hb : M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow))
    (c : Fin n) :
    ((c, M c) ∈ P.coveredSquares ↔
      c ≠ b ∧ (c, M c) ∈ P.toGridRectangle.coveredSquares) ∧
    ((Equiv.swap a b c, M c) ∈ Q.coveredSquares ↔
      c ≠ b ∧ (c, M c) ∈ Q.toGridRectangle.coveredSquares) := by
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  rw [hbottom] at ht
  rcases eq_or_ne c a with rfl | hca
  · have hPrect : (a, M a) ∉ P.toGridRectangle.coveredSquares := by
      simp [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns, P.left_eq]
    have hQrect : (a, M a) ∉ Q.toGridRectangle.coveredSquares := by
      simp [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns, Q.left_eq]
    simp only [Equiv.swap_apply_left, P.mk_mem_coveredSquares_left_column,
      Q.mk_mem_coveredSquares_right_column, hPrect, hQrect, and_false]
    simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq,
      ← Fin.val_inj] at hs ht ha hrow ⊢
    rw [hbottom]
    constructor <;> constructor <;> intro h <;> split_ifs at * <;> omega
  · rcases eq_or_ne c b with rfl | hcb
    · simp only [Equiv.swap_apply_right, P.mk_mem_coveredSquares_right_column,
        Q.mk_mem_coveredSquares_left_column, ne_eq, not_true_eq_false, false_and]
      simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq,
        ← Fin.val_inj] at hs ht hb hrow ⊢
      constructor <;> constructor <;> intro h <;> split_ifs at * <;> omega
    · simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
        P.mem_coveredSquares_iff_of_ne (p := (c, M c)) hca hcb,
        Q.mem_coveredSquares_iff_of_ne (p := (c, M c)) hca hcb]
      tauto

private theorem initial_pair_marking_filters {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y z)
    (hrow : P.top ∈ Grid.cIoo P.bottom Q.top) (hbottom : Q.bottom = P.top)
    (M : GridState n)
    (ha : M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow))
    (hb : M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow)) :
    P.coveredSquares.filter (· ∈ M.pointSet) =
        P.toGridRectangle.coveredSquares.filter (fun p => p.1 ≠ b ∧ p ∈ M.pointSet) ∧
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding).filter
          (· ∈ M.pointSet) =
        Q.toGridRectangle.coveredSquares.filter (fun p => p.1 ≠ b ∧ p ∈ M.pointSet) := by
  classical
  constructor
  · ext ⟨c, r⟩
    simp only [Finset.mem_filter, M.mem_pointSet]
    have h := (G.initial_pair_markings C P Q hrow hbottom M ha hb c).1
    by_cases hr : r = M c
    · subst r
      tauto
    · tauto
  · ext ⟨c, r⟩
    simp only [Finset.mem_filter, Finset.mem_map_equiv, Equiv.prodCongr_symm,
      Equiv.symm_swap, Equiv.prodCongr_apply, Equiv.refl_symm, M.mem_pointSet]
    have h := (G.initial_pair_markings C P Q hrow hbottom M ha hb c).2
    by_cases hr : r = M c
    · subst r
      tauto
    · tauto

private theorem recutHexagonRectangle_rectangle_not_column {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y z)
    (hcol : Q.right ∈ Grid.cIoo b P.right) (hp : P.IsEmpty) (hq : Q.IsEmpty)
    {p : Fin n × Fin n}
    (hmem : p ∈ (P.recutHexagonRectangle Q hcol hp hq).rectangle.toGridRectangle.coveredSquares) :
    p.1 ≠ b := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.second.right ∈ Grid.cIoo D.first.left D.first.right := P.left_eq ▸ hcol
  have hsides := D.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hc hp hq
  rw [← P.recutHexagonRectangle_toRectangleDecomposition Q hcol hp hq] at hsides
  have hleft : (P.recutHexagonRectangle Q hcol hp hq).rectangle.left = Q.right := hsides.2.2.1
  have hright : (P.recutHexagonRectangle Q hcol hp hq).rectangle.right = P.right := hsides.2.2.2
  have hcolumn := ((GridRectangle.mem_coveredSquares _ _).mp hmem).1
  simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, hleft, hright] at hcolumn
  intro h
  rw [h] at hcolumn
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)
    (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol).symm) hcolumn

/-- Recutting two initial-side pentagons preserves their weight. The reverse pentagon's
squares are read in the original diagram by exchanging the two commuted columns. -/
@[simp]
theorem hexagonRectangleWeight_recutHexagonRectangle
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y z)
    (hcol : Q.right ∈ Grid.cIoo b P.right) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    G.hexagonRectangleWeight C R (P.recutHexagonRectangle Q hcol hp hq) =
      MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
        ∏ p ∈ Q.coveredSquares.map
          ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding,
          if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
  classical
  let T := P.recutHexagonRectangle Q hcol hp hq
  have hrecut := P.isRecut_recutHexagonRectangle Q hcol hp hq
  obtain ⟨hrow, hbottom⟩ := G.initial_pair_rows C P Q
    (Grid.ne_right_of_mem_cIoo hcol).symm hp hq
  have hfilters := G.initial_pair_marking_filters C P Q hrow hbottom G.O
    C.O_column_below C.O_next_above
  rw [← G.OSet_def] at hfilters
  let f : Fin n × Fin n → MvPolynomial (Fin n) R := fun p =>
    if p.1 ≠ b ∧ p ∈ G.OSet then MvPolynomial.X p.1 else 1
  rw [G.rename_initialPentagonWeight, ← Finset.prod_filter, ← Finset.prod_filter,
    hfilters.1, hfilters.2, Finset.prod_filter, Finset.prod_filter]
  have hrweight : G.OMonomial R T.rectangle.toGridRectangle =
      ∏ p ∈ T.rectangle.toGridRectangle.coveredSquares, f p := by
    rw [G.OMonomial_eq_prod_coveredSquares]
    refine Finset.prod_congr rfl fun p hpT => ?_
    dsimp only [f]
    have hc := G.recutHexagonRectangle_rectangle_not_column C P Q hcol hp hq hpT
    split_ifs <;> tauto
  cases hhex : T.hexagon with
  | inl H =>
    have hside := P.recutHexagonRectangle_hexagon_isLeft Q hcol hp hq
    simp only [T, hhex, Sum.isLeft_inl, Bool.true_eq_false] at hside
  | inr H =>
    have hHweight : G.initialHexagonWeight R H =
        ∏ p ∈ H.toGridRectangle.coveredSquares, f p := by
      rw [G.initialHexagonWeight_eq_prod_coveredSquares, ← Finset.prod_filter,
        ← Finset.prod_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter, H.mem_coveredSquares]
      tauto
    rw [G.hexagonRectangleWeight_def, hhex, G.commutationHexagonWeight_inr, hHweight, hrweight]
    have hweight :
        (∏ p ∈ T.hexagon.toGridRectangleBetween.toGridRectangle.coveredSquares, f p) *
          (∏ p ∈ T.rectangle.toGridRectangle.coveredSquares, f p) =
        (∏ p ∈ P.toGridRectangle.coveredSquares, f p) *
          (∏ p ∈ Q.toGridRectangle.coveredSquares, f p) :=
      hrecut.isRepartition.prod_coveredSquares_mul_prod_coveredSquares f
    simpa only [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inr] using hweight

private theorem recutRectangleHexagon_rectangle_not_column {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y z)
    (hcol : P.right ∈ Grid.cIoo b Q.right) (hp : P.IsEmpty) (hq : Q.IsEmpty)
    {p : Fin n × Fin n}
    (hmem : p ∈ (P.recutRectangleHexagon Q hcol hp hq).rectangle.toGridRectangle.coveredSquares) :
    p.1 ≠ b := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.first.right ∈ Grid.cIoo D.first.left D.second.right := P.left_eq ▸ hcol
  have hsides := D.recut_sides_of_left_eq_left_of_first_right_mem_cIoo
    hcommon hc hp hq
  rw [← P.recutRectangleHexagon_toRectangleDecomposition Q hcol hp hq] at hsides
  have hleft : (P.recutRectangleHexagon Q hcol hp hq).rectangle.left = P.right := hsides.1
  have hright : (P.recutRectangleHexagon Q hcol hp hq).rectangle.right = Q.right := hsides.2.1
  have hcolumn := ((GridRectangle.mem_coveredSquares _ _).mp hmem).1
  simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, hleft, hright] at hcolumn
  intro h
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)
    (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol).symm) (h ▸ hcolumn)

/-- Recutting two initial-side pentagons in the complementary column order preserves their
weight. The reverse pentagon's squares are read in the original diagram by exchanging the two
commuted columns. -/
@[simp]
theorem rectangleHexagonWeight_recutRectangleHexagon
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y z)
    (hcol : P.right ∈ Grid.cIoo b Q.right) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    G.rectangleHexagonWeight C R (P.recutRectangleHexagon Q hcol hp hq) =
      MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
        ∏ p ∈ Q.coveredSquares.map
          ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding,
          if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
  classical
  let T := P.recutRectangleHexagon Q hcol hp hq
  have hrecut := P.isRecut_recutRectangleHexagon Q hcol hp hq
  obtain ⟨hrow, hbottom⟩ := G.initial_pair_rows C P Q
    (Grid.ne_right_of_mem_cIoo hcol) hp hq
  have hfilters := G.initial_pair_marking_filters C P Q hrow hbottom G.O
    C.O_column_below C.O_next_above
  rw [← G.OSet_def] at hfilters
  let f : Fin n × Fin n → MvPolynomial (Fin n) R := fun p =>
    if p.1 ≠ b ∧ p ∈ G.OSet then MvPolynomial.X p.1 else 1
  rw [G.rename_initialPentagonWeight, ← Finset.prod_filter, ← Finset.prod_filter,
    hfilters.1, hfilters.2, Finset.prod_filter, Finset.prod_filter]
  have hrweight : G.OMonomial R T.rectangle.toGridRectangle =
      ∏ p ∈ T.rectangle.toGridRectangle.coveredSquares, f p := by
    rw [G.OMonomial_eq_prod_coveredSquares]
    refine Finset.prod_congr rfl fun p hpT => ?_
    dsimp only [f]
    have hc := G.recutRectangleHexagon_rectangle_not_column C P Q hcol hp hq hpT
    split_ifs <;> tauto
  cases hhex : T.hexagon with
  | inl H =>
    have hside := P.recutRectangleHexagon_hexagon_isLeft Q hcol hp hq
    simp only [T, hhex, Sum.isLeft_inl, Bool.true_eq_false] at hside
  | inr H =>
    have hHweight : G.initialHexagonWeight R H =
        ∏ p ∈ H.toGridRectangle.coveredSquares, f p := by
      rw [G.initialHexagonWeight_eq_prod_coveredSquares, ← Finset.prod_filter,
        ← Finset.prod_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter, H.mem_coveredSquares]
      tauto
    rw [G.rectangleHexagonWeight_def, hhex, G.commutationHexagonWeight_inr,
      hrweight, hHweight]
    have hweight :
        (∏ p ∈ T.rectangle.toGridRectangle.coveredSquares, f p) *
          (∏ p ∈ T.hexagon.toGridRectangleBetween.toGridRectangle.coveredSquares, f p) =
        (∏ p ∈ P.toGridRectangle.coveredSquares, f p) *
          ∏ p ∈ Q.toGridRectangle.coveredSquares, f p :=
      hrecut.isRepartition.prod_coveredSquares_mul_prod_coveredSquares f
    simpa only [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inr] using hweight

/-- A counted initial-side pentagon pair in the strict interior-terminal-side branch
has a unique unpaired hexagon-composite recut, and their polynomial weights agree.
The second pentagon is indexed by the actual reverse commutation. -/
private theorem
    existsUnique_unpairedHexagonComposite_of_initialPentagonPair_of_second_right_mem_cIoo
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons C.reverse y z)
    (hcol : Q.right ∈ Grid.cIoo b P.right) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inr P, .inr Q⟩ := by
  -- Express the reverse weight in the original variables before identifying its dependent
  -- polygon indices. Its marking constraints remain available in hQ.
  simp only [G.pentagonPairWeight_def, G.commutationPentagonWeight_inr,
    (G.swapColumns a b).commutationPentagonWeight_inr, G.initialPentagonWeight_reverse]
  generalize hCr : C.reverse = Cr at *
  have hcolumn : Cr.column = a := hCr ▸ C.reverse_column
  have hturn : Cr.turnRow = C.oppositeTurnRow := hCr ▸ C.reverse_turnRow
  rcases Cr with ⟨⟨column, turn, hne⟩, opposite, hnon, hOa, hXa, hOb, hXb⟩
  simp only at hcolumn hturn
  subst column turn
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_initialPentagons Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  let T := P.recutHexagonRectangle Q hcol hp hq
  have hone : D.HasOneCommonSide :=
    D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo
      (P.left_eq.trans Q.left_eq.symm) (P.left_eq ▸ hcol)
  have hrecut : D.IsRecut (GridHexagonCompositeDecomposition.toRectangleDecomposition
      (.inl T : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z)) := by
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    exact P.isRecut_recutHexagonRectangle Q hcol hp hq
  have hmem := G.recutHexagonRectangle_mem_unpairedHexagonComposites C P Q hcol hp hq hpX hqX
  refine ⟨.inl T, ⟨hmem, hrecut, ?_⟩, ?_⟩
  · rw [G.hexagonCompositeWeight_inl]
    exact G.hexagonRectangleWeight_recutHexagonRectangle C R P Q hcol hp hq
  · intro F hF
    exact G.injOn_toRectangleDecomposition_hexagonCompositeDecompositions C x z
      ((G.mem_unpairedHexagonComposites C F).mp hF.1).1
      ((G.mem_unpairedHexagonComposites C (.inl T)).mp hmem).1
      ((D.existsUnique_isRecut hone hp hq).unique hF.2.1 hrecut)

/-- A counted initial-side pentagon pair in the complementary column order has a unique
unpaired hexagon-composite recut, and their polynomial weights agree. -/
private theorem
    existsUnique_unpairedHexagonComposite_of_initialPentagonPair_of_first_right_mem_cIoo
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons C.reverse y z)
    (hcol : P.right ∈ Grid.cIoo b Q.right) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inr P, .inr Q⟩ := by
  simp only [G.pentagonPairWeight_def, G.commutationPentagonWeight_inr,
    (G.swapColumns a b).commutationPentagonWeight_inr, G.initialPentagonWeight_reverse]
  generalize hCr : C.reverse = Cr at *
  have hcolumn : Cr.column = a := hCr ▸ C.reverse_column
  have hturn : Cr.turnRow = C.oppositeTurnRow := hCr ▸ C.reverse_turnRow
  rcases Cr with ⟨⟨column, turn, hne⟩, opposite, hnon, hOa, hXa, hOb, hXb⟩
  simp only at hcolumn hturn
  subst column turn
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_initialPentagons Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  let T := P.recutRectangleHexagon Q hcol hp hq
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.first.right ∈ Grid.cIoo D.first.left D.second.right := by
    dsimp only [D]
    rwa [P.left_eq]
  have hone : D.HasOneCommonSide :=
    D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hc)
  have hrecut : D.IsRecut (GridHexagonCompositeDecomposition.toRectangleDecomposition
      (.inr T : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z)) := by
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    exact P.isRecut_recutRectangleHexagon Q hcol hp hq
  have hmem := G.recutRectangleHexagon_mem_unpairedHexagonComposites
    C P Q hcol hp hq hpX hqX
  refine ⟨.inr T, ⟨hmem, hrecut, ?_⟩, ?_⟩
  · rw [G.hexagonCompositeWeight_inr]
    exact G.rectangleHexagonWeight_recutRectangleHexagon C R P Q hcol hp hq
  · intro F hF
    exact G.injOn_toRectangleDecomposition_hexagonCompositeDecompositions C x z
      ((G.mem_unpairedHexagonComposites C F).mp hF.1).1
      ((G.mem_unpairedHexagonComposites C (.inr T)).mp hmem).1
      ((D.existsUnique_isRecut hone hp hq).unique hF.2.1 hrecut)

/-- Every counted pair of initial-side pentagons with distinct terminal sides has a unique
unpaired hexagon-composite recut of the same polynomial weight. -/
theorem existsUnique_unpairedHexagonComposite_of_initialPentagonPair
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons C.reverse y z)
    (hne : P.right ≠ Q.right) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inr P, .inr Q⟩ := by
  obtain ⟨hp, -⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, -⟩ := ((G.swapColumns a b).mem_initialPentagons Q).mp hQ
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := by
    dsimp only [D]
    rw [P.left_eq, Q.left_eq, C.reverse_column]
  rcases (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hne hp hq).1 with hcol | hcol
  · apply G.existsUnique_unpairedHexagonComposite_of_initialPentagonPair_of_first_right_mem_cIoo
      C R P Q hP hQ
    simpa only [D, P.left_eq] using hcol
  · apply G.existsUnique_unpairedHexagonComposite_of_initialPentagonPair_of_second_right_mem_cIoo
      C R P Q hP hQ
    simpa only [D, P.left_eq] using hcol

end TauCeti.GridDiagram
