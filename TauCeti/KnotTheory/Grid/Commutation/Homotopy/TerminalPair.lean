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
side.
When the first initial side lies strictly between the second initial side and the common
terminal side, recutting their union gives a rectangle followed by a terminal-side hexagon.
The two turn points lie in order on that hexagon. The resulting composite is counted, has
the same weight as the pentagon pair, and has no hexagon--rectangle recut partner.

## Main results

* `GridDiagram.recutTerminalPentagonPair`: the rectangle--hexagon recut.
* `GridDiagram.recutTerminalPentagonPair_toRectangleDecomposition`: its underlying
  rectangle decomposition is the canonical recut.
* `GridDiagram.recutTerminalPentagonPair_mem_rectangleHexagonDecompositions`: countedness.
* `GridDiagram.rectangleHexagonWeight_recutTerminalPentagonPair`: weight preservation.
* `GridDiagram.recutTerminalPentagonPair_mem_unpairedHexagonComposites`: the resulting
  composite has no counted hexagon recut partner.

## References

Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559), and Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Section 5.1. The underlying rectangle recut is
`GridRectangleDecomposition.recut_geometry_of_right_eq_right_of_mem_cIoo`.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

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
    (hcol : P.left ∈ Grid.cIoo Q.left b) (hp : P.IsEmpty) (hq : Q.IsEmpty) :
    P.bottom ∈ Grid.cIoo Q.bottom P.top ∧ Q.top = P.bottom := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right :=
    P.right_eq.trans (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm
  refine ⟨(D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon
    (Grid.ne_left_of_mem_cIoo hcol) hp hq).2, ?_⟩
  rw [GridRectangleBetween.top_def,
    (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)), ← P.right_eq, P.map_right,
    GridRectangleBetween.bottom_def]

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
  have hcommon : D.first.right = D.second.right :=
    P.right_eq.trans (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm
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
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q hcol hp hq
  have hs := P.turn_mem_cIco_bottom_top
  have ht : C.oppositeTurnRow ∈ Grid.cIco Q.bottom Q.top := by
    simpa only [C.reverse_turnRow] using Q.turn_mem_cIco_bottom_top
  rw [htop] at ht
  have hlower : C.oppositeTurnRow ∈ Grid.cIco E.second.bottom E.second.top := by
    rw [hsb', hst']
    exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo ht hrow
  have hupper : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow E.second.top := by
    rw [hst']
    simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hs ht hrow ⊢
    split_ifs at * <;> omega
  exact ⟨{ toGridRectangleBetween := E.second
           right_eq := hsr
           lower_mem := hlower
           upper_mem := hupper }, rfl⟩

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
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q hcol hp hq
  have havoid : ∀ p : Fin n × Fin n, p.1 ≠ a →
      p ∈ T.rectangle.toGridRectangle.coveredSquares ∪
        T.hexagon.toGridRectangleBetween.toGridRectangle.coveredSquares → p ∉ G.XSet := by
    rintro ⟨c, r⟩ hca hmem hX
    have hr : r = G.X c := ((G.mem_XSet _).mp hX).symm
    subst r
    rw [hrecut.isRepartition.coveredSquares_union_eq] at hmem
    have hmarks := G.terminal_pair_markings C P Q hrow htop G.X
      C.X_column_below C.X_next_above c
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.disjoint_left.mp hpX (hmarks.1.mpr ⟨hca, h⟩) hX
    · have hQmem := hmarks.2.mpr ⟨hca, h⟩
      have hQX : (Equiv.swap a b c, G.X c) ∈ (G.swapColumns a b).XSet := by
        simp only [G.mem_XSet_swapColumns, Equiv.swap_apply_self]
        exact hX
      exact Finset.disjoint_left.mp hqX hQmem hQX
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
  classical
  let T := G.recutTerminalPentagonPair C P Q hcol hp hq
  have hrecut := G.isRecut_recutTerminalPentagonPair C P Q hcol hp hq
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q hcol hp hq
  have hfilters := G.terminal_pair_marking_filters C P Q hrow htop G.O
    C.O_column_below C.O_next_above
  rw [← G.OSet_def] at hfilters
  let f : Fin n × Fin n → MvPolynomial (Fin n) R := fun p =>
    if p.1 ≠ a ∧ p ∈ G.OSet then MvPolynomial.X p.1 else 1
  have hPweight : MvPolynomial.rename (Equiv.swap a b) (G.pentagonWeight R C P) =
      ∏ p ∈ P.toGridRectangle.coveredSquares, f p := by
    rw [G.rename_pentagonWeight, ← Finset.prod_filter, ← Finset.prod_filter, hfilters.1]
  have hQweight : (G.swapColumns a b).pentagonWeight R C.reverse Q =
      ∏ p ∈ Q.toGridRectangle.coveredSquares, f p := by
    rw [G.pentagonWeight_reverse, ← Finset.prod_filter, ← Finset.prod_filter, hfilters.2]
  obtain ⟨H, hH⟩ := G.recutTerminalPentagonPair_hexagon C P Q hcol hp hq
  have hrweight : G.OMonomial R T.rectangle.toGridRectangle =
      ∏ p ∈ T.rectangle.toGridRectangle.coveredSquares, f p := by
    rw [G.OMonomial_eq_prod_coveredSquares]
    refine Finset.prod_congr rfl fun p hpT => ?_
    dsimp only [f]
    have hc := G.recutTerminalPentagonPair_rectangle_not_column C P Q hcol hp hq hpT
    by_cases hO : p ∈ G.OSet
    · rw [ite_eq_left hO, ite_eq_left ⟨hc, hO⟩]
    · rw [ite_eq_right hO, ite_eq_right (fun h => hO h.2)]
  have hHweight : G.hexagonWeight R H =
      ∏ p ∈ H.toGridRectangle.coveredSquares, f p := by
    rw [G.hexagonWeight_eq_prod_coveredSquares, ← Finset.prod_filter,
      ← Finset.prod_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, H.mem_coveredSquares]
    tauto
  rw [G.rectangleHexagonWeight_def, hH, G.commutationHexagonWeight_inl, hrweight, hHweight]
  have hweight := hrecut.isRepartition.prod_coveredSquares_mul_prod_coveredSquares f
  simp only [hH, GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hweight
  rw [hweight, G.pentagonPairWeight_def, G.commutationPentagonWeight_inl,
    (G.swapColumns a b).commutationPentagonWeight_inl, hPweight, hQweight]

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
  have hone := D.hasOneCommonSide_of_right_eq_right
    (P.right_eq.trans (Q.right_eq.trans (congrArg (finRotate n) C.reverse_column)).symm)
    (Grid.ne_left_of_mem_cIoo hcol)
  have hrecut := G.isRecut_recutTerminalPentagonPair C P Q hcol hp hq
  have hTone : T.toRectangleDecomposition.HasOneCommonSide := by
    rw [G.recutTerminalPentagonPair_toRectangleDecomposition C]
    exact D.hasOneCommonSide_recut hone hp hq
  obtain ⟨hrow, htop⟩ := G.terminal_pair_rows C P Q hcol hp hq
  refine (G.mem_unpairedHexagonComposites C (.inr T)).mpr ⟨?_, ?_, ?_⟩
  · exact (G.inr_mem_hexagonCompositeDecompositions C T).mpr
      (G.recutTerminalPentagonPair_mem_rectangleHexagonDecompositions C P Q hcol hP hQ)
  · simpa only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] using
      T.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide hTone
  · intro F _ hF
    simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hF
    have hFD : F.toRectangleDecomposition = D :=
      (T.toRectangleDecomposition.existsUnique_isRecut hTone
        hrecut.isEmpty_first hrecut.isEmpty_second).unique hF (hrecut.symm hone hp hq)
    cases F with
    | inl F =>
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hFD
      exact (G.terminal_pair_no_hexagon C P Q hrow htop F.hexagon).1
        (by
          simpa only [GridHexagonRectangleDecomposition.toRectangleDecomposition, D] using
            congrArg (fun E : GridRectangleDecomposition x z => E.first.toGridRectangle) hFD)
    | inr F =>
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hFD
      exact (G.terminal_pair_no_hexagon C P Q hrow htop F.hexagon).2
        (by
          simpa only [GridRectangleHexagonDecomposition.toRectangleDecomposition, D] using
            congrArg (fun E : GridRectangleDecomposition x z => E.second.toGridRectangle) hFD)

end TauCeti.GridDiagram
