/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.SideOverlap
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Diagonal
import Mathlib.Algebra.CharP.Two

/-!
# Returning pentagon pairs

The diagonal terms of the forward--reverse commutation map are pairs of empty pentagons
returning to their source state. Pentagons turning on opposite sides would form a thin
horizontal annulus and therefore have the same turn row. The two commutations use distinct
turn rows, so this case cannot occur. Pairs turning on the same side form thin vertical
annuli in one of the two columns adjacent to the replaced grid line. Their uniqueness and
existence are stated for a returning pentagon turning in an arbitrary row, so that they serve the
crossing change homotopy as well.

The placement of the markings in the two bigons makes marking avoidance automatic for
these empty returning pairs. Their weights are consequently one over any commutative
semiring. Counting the two possible annuli gives an explicit diagonal coefficient formula
for the round-trip commutation map. Combining this count with the four hexagon--rectangle
indicators proves the diagonal coefficient of the homotopy equation in characteristic two.

Off the diagonal as well, the replaced grid line is a common side of the two rectangles of
every pentagon pair.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridPentagonBetween

variable {n : ℕ} {a s t : Fin n} {x y : GridState n}

/-- Two terminal-side pentagons at the same column, the second returning to the source of the
first, share their initial column and exchange their bottom and top rows. -/
theorem left_eq_left_and_bottom_eq_top_and_top_eq_bottom (P : GridPentagonBetween a s x y)
    (Q : GridPentagonBetween a t y x) :
    Q.left = P.left ∧ Q.bottom = P.top ∧ Q.top = P.bottom := by
  have hleft : Q.left = P.left := by
    rcases P.toGridRectangleBetween.left_right_eq_cases Q.toGridRectangleBetween with h | h
    · exact h.1
    · exact False.elim (P.left_ne (h.2.symm.trans Q.right_eq))
  exact ⟨hleft,
    P.toGridRectangleBetween.bottom_eq_top_of_left_eq_left Q.toGridRectangleBetween hleft,
    P.toGridRectangleBetween.top_eq_bottom_of_left_eq_left Q.toGridRectangleBetween hleft⟩

/-- Two returning terminal-side pentagons are empty exactly when their common initial
column is the column immediately before the replaced line. -/
theorem isEmpty_and_isEmpty_iff (P : GridPentagonBetween a s x y)
    (Q : GridPentagonBetween a t y x) : P.IsEmpty ∧ Q.IsEmpty ↔ P.left = a := by
  rw [P.toGridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
    Q.toGridRectangleBetween (P.left_eq_left_and_bottom_eq_top_and_top_eq_bottom Q).1,
    P.right_eq]
  exact ⟨fun h => (finRotate n).injective h.symm, fun h => congrArg (finRotate n) h.symm⟩

/-- A pair of terminal-side pentagons leaving a grid state in column `a` and returning to it is
unique, whatever the column and turn row of the returning pentagon. -/
theorem sigma_eq_of_left_eq {a' : Fin n} {y' : GridState n} (P : GridPentagonBetween a s x y)
    (Q : GridPentagonBetween a' t y x) (P' : GridPentagonBetween a s x y')
    (Q' : GridPentagonBetween a' t y' x) (hP : P.left = a) (hP' : P'.left = a) :
    (⟨y, P, Q⟩ : Σ m, GridPentagonBetween a s x m × GridPentagonBetween a' t m x) =
      ⟨y', P', Q'⟩ := by
  obtain rfl : y = y' := by
    rw [P.target_eq_swapColumns, P'.target_eq_swapColumns, hP, hP']
  obtain rfl : P = P' := Subsingleton.elim _ _
  obtain rfl : Q = Q' := Subsingleton.elim _ _
  rfl

/-- A pair of terminal-side pentagons at the column `a' = a`, turning in the rows `s` and `t`,
leaves `x` in column `a` and returns to it exactly when `s` lies between the rows of `x` in the
column `a` and the next one, and `t` between those in the next column and `a`. It is then the
empty thin annulus in column `a` (`GridPentagonBetween.isEmpty_and_isEmpty_iff`). -/
theorem exists_left_eq_iff {a' : Fin n} (ha : a ≠ finRotate n a) (ha' : a' = a) :
    (∃ (y : GridState n) (P : GridPentagonBetween a s x y) (_ : GridPentagonBetween a' t y x),
        P.left = a) ↔
      s ∈ Grid.cIco (x a) (x (finRotate n a)) ∧ t ∈ Grid.cIco (x (finRotate n a)) (x a) := by
  subst ha'
  constructor
  · rintro ⟨y, P, Q, hP⟩
    obtain ⟨-, hb, ht⟩ := P.left_eq_left_and_bottom_eq_top_and_top_eq_bottom Q
    exact ⟨by simpa only [hP, P.right_eq] using P.turn_mem,
      by simpa only [hb, ht, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
        hP, P.right_eq] using Q.turn_mem_cIco_bottom_top⟩
  · rintro ⟨hs, ht⟩
    let m := x.swapColumns a' (finRotate n a')
    let r := GridRectangleBetween.ofSwapColumns m x a' (finRotate n a') ha
      (GridState.swapColumns_swapColumns _ _ _).symm
    let Q : GridPentagonBetween a' t m x := ofRightEq r
      (GridRectangleBetween.ofSwapColumns_right ..)
      (by simpa only [r, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
        GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right, m,
        GridState.swapColumns_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] using ht)
    exact ⟨m, ofSwapColumns x a' ha hs, Q, ofSwapColumns_left ..⟩

/-- Empty returning pentagons on opposite sides must have the same turn row: their
underlying horizontal annulus consists of a single row. -/
theorem turn_eq_of_isEmpty_and_isEmpty_initial (P : GridPentagonBetween a s x y)
    (Q : GridInitialPentagonBetween a t y x) (h : P.IsEmpty ∧ Q.IsEmpty) : s = t := by
  have hleft : Q.left = P.right := Q.left_eq.trans P.right_eq.symm
  have hthin :=
    (P.toGridRectangleBetween.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right
      Q.toGridRectangleBetween hleft).mp h
  have hbottom := P.toGridRectangleBetween.bottom_eq_bottom_of_left_eq_right
    Q.toGridRectangleBetween hleft
  have htop := P.toGridRectangleBetween.top_eq_top_of_left_eq_right
    Q.toGridRectangleBetween hleft
  exact (P.turn_eq_bottom_of_top_eq_finRotate_bottom hthin).trans
    (hbottom.symm.trans (Q.turn_eq_bottom_of_top_eq_finRotate_bottom
      (by simpa only [hbottom, htop] using hthin)).symm)

end GridPentagonBetween

namespace GridInitialPentagonBetween

variable {n : ℕ} {a s t : Fin n} {x y : GridState n}

/-- Two returning initial-side pentagons are empty exactly when their common terminal
column is the column immediately after the replaced line. -/
theorem isEmpty_and_isEmpty_iff (P : GridInitialPentagonBetween a s x y)
    (Q : GridInitialPentagonBetween a t y x) :
    P.IsEmpty ∧ Q.IsEmpty ↔ P.right = finRotate n (finRotate n a) := by
  have hleft : Q.left = P.left := Q.left_eq.trans P.left_eq.symm
  simpa only [P.left_eq] using
    P.toGridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
      Q.toGridRectangleBetween hleft

/-- Two initial-side pentagons at the same column, the second returning to the source of the
first, share their initial column and exchange their bottom and top rows. -/
theorem left_eq_left_and_bottom_eq_top_and_top_eq_bottom (P : GridInitialPentagonBetween a s x y)
    (Q : GridInitialPentagonBetween a t y x) :
    Q.left = P.left ∧ Q.bottom = P.top ∧ Q.top = P.bottom := by
  have hleft : Q.left = P.left := Q.left_eq.trans P.left_eq.symm
  exact ⟨hleft,
    P.toGridRectangleBetween.bottom_eq_top_of_left_eq_left Q.toGridRectangleBetween hleft,
    P.toGridRectangleBetween.top_eq_bottom_of_left_eq_left Q.toGridRectangleBetween hleft⟩

/-- A pair of initial-side pentagons leaving a grid state with terminal column two after `a` and
returning to it is unique, whatever the column and turn row of the returning pentagon. -/
theorem sigma_eq_of_right_eq {a' : Fin n} {y' : GridState n}
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a' t y x)
    (P' : GridInitialPentagonBetween a s x y') (Q' : GridInitialPentagonBetween a' t y' x)
    (hP : P.right = finRotate n (finRotate n a)) (hP' : P'.right = finRotate n (finRotate n a)) :
    (⟨y, P, Q⟩ : Σ m, GridInitialPentagonBetween a s x m × GridInitialPentagonBetween a' t m x) =
      ⟨y', P', Q'⟩ := by
  obtain rfl : y = y' := by
    rw [P.target_eq_swapColumns, P'.target_eq_swapColumns, hP, hP']
  obtain rfl : P = P' := Subsingleton.elim _ _
  obtain rfl : Q = Q' := Subsingleton.elim _ _
  rfl

/-- A pair of initial-side pentagons at the column `a' = a`, turning in the rows `s` and `t`,
leaves `x` with terminal column two after `a` and returns to it exactly when `s` lies between the
rows of `x` in the column after `a` and the next one, and `t` between those in the next column and
the column after `a`. It is then the empty thin annulus in the column after `a`
(`GridInitialPentagonBetween.isEmpty_and_isEmpty_iff`). -/
theorem exists_right_eq_iff {a' : Fin n} (ha : a ≠ finRotate n a) (ha' : a' = a) :
    (∃ (y : GridState n) (P : GridInitialPentagonBetween a s x y)
        (_ : GridInitialPentagonBetween a' t y x), P.right = finRotate n (finRotate n a)) ↔
      s ∈ Grid.cIco (x (finRotate n a)) (x (finRotate n (finRotate n a))) ∧
        t ∈ Grid.cIco (x (finRotate n (finRotate n a))) (x (finRotate n a)) := by
  subst ha'
  constructor
  · rintro ⟨y, P, Q, hP⟩
    obtain ⟨-, hb, ht⟩ := P.left_eq_left_and_bottom_eq_top_and_top_eq_bottom Q
    exact ⟨by simpa only [hP, P.left_eq] using P.turn_mem,
      by simpa only [hb, ht, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
        hP, P.left_eq] using Q.turn_mem_cIco_bottom_top⟩
  · rintro ⟨hs, ht⟩
    have hbc : finRotate n a' ≠ finRotate n (finRotate n a') := (finRotate n).injective.ne ha
    let m := x.swapColumns (finRotate n a') (finRotate n (finRotate n a'))
    let r := GridRectangleBetween.ofSwapColumns m x (finRotate n a') (finRotate n (finRotate n a'))
      hbc (GridState.swapColumns_swapColumns _ _ _).symm
    let Q : GridInitialPentagonBetween a' t m x :=
      ⟨r, GridRectangleBetween.ofSwapColumns_left ..,
        by simpa only [r, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
          GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
          m, GridState.swapColumns_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
          using ht⟩
    exact ⟨m, ofSwapColumns x (finRotate n (finRotate n a')) hbc.symm hs, Q,
      ofSwapColumns_right ..⟩

end GridInitialPentagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "c" => finRotate n (finRotate n C.column)

private theorem disjoint_pentagon_markings_of_two_turns
    (bottom top : Fin n) (S : Finset (Fin n × Fin n))
    (hs : C.turnRow ∈ Grid.cIco bottom top)
    (ht : C.oppositeTurnRow ∈ Grid.cIco top bottom)
    (hS : ∀ p, p ∈ S ↔ (p.1 = a ∧ p.2 ∈ Grid.cIoo C.turnRow top) ∨
      (p.1 = b ∧ p.2 ∈ Grid.cIco bottom C.turnRow))
    (M : GridState n)
    (ha : M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow))
    (hb : M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow)) :
    Disjoint S M.pointSet := by
  rw [Finset.disjoint_right]
  intro p hp hmem
  have hm := (M.mem_pointSet p).mp hp
  rcases (hS p).mp hmem with ⟨hcol, hmem⟩ | ⟨hcol, hmem⟩
  · have hmark : p.2 ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow) := by
      simpa only [← hcol, hm] using ha
    simp only [Finset.mem_insert, Grid.mem_cIco, Grid.mem_cIoo,
      ne_eq, ← Fin.val_inj] at hs ht hmark hmem
    split_ifs at hs ht hmark hmem <;> omega
  · have hmark : p.2 ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow) := by
      simpa only [← hcol, hm] using hb
    simp only [Finset.mem_insert, Grid.mem_cIco, ne_eq, ← Fin.val_inj] at hs ht hmark hmem
    split_ifs at hs ht hmark hmem <;> omega

private theorem disjoint_returning_pentagon_markings {x y : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween a C.oppositeTurnRow y x) (h : P.IsEmpty ∧ Q.IsEmpty)
    (M : GridState n)
    (ha : M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow))
    (hb : M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow)) :
    Disjoint P.coveredSquares M.pointSet := by
  have hleft := (P.isEmpty_and_isEmpty_iff Q).mp h
  obtain ⟨-, hbottom, htop⟩ := P.left_eq_left_and_bottom_eq_top_and_top_eq_bottom Q
  have hc : Grid.cIco P.left (finRotate n a) = {a} :=
    Grid.cIco_eq_singleton_iff.mpr ⟨hleft, rfl, P.left_ne⟩
  exact G.disjoint_pentagon_markings_of_two_turns C P.bottom P.top P.coveredSquares
    P.turn_mem_cIco_bottom_top (by simpa only [hbottom, htop] using Q.turn_mem_cIco_bottom_top)
    (fun p => by
      simp only [P.mem_coveredSquares, hc, Finset.mem_singleton]
      tauto) M ha hb

private theorem disjoint_returning_initialPentagon_markings {x y : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a C.oppositeTurnRow y x) (h : P.IsEmpty ∧ Q.IsEmpty)
    (M : GridState n)
    (ha : M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow))
    (hb : M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow)) :
    Disjoint P.coveredSquares M.pointSet := by
  have hright := (P.isEmpty_and_isEmpty_iff Q).mp h
  obtain ⟨-, hbottom, htop⟩ := P.left_eq_left_and_bottom_eq_top_and_top_eq_bottom Q
  have hc : Grid.cIco (finRotate n a) P.right = {b} :=
    Grid.cIco_eq_singleton_iff.mpr ⟨rfl, hright, P.right_ne.symm⟩
  exact G.disjoint_pentagon_markings_of_two_turns C P.bottom P.top P.coveredSquares
    P.turn_mem_cIco_bottom_top (by simpa only [hbottom, htop] using Q.turn_mem_cIco_bottom_top)
    (fun p => by
      simp only [P.mem_coveredSquares, hc, Finset.mem_singleton]
      tauto) M ha hb

private theorem returning_pentagon_pair_iff
    (Cr : ColumnCommutationData (G.swapColumns a b))
    (hcolumn : Cr.column = a) (hturn : Cr.turnRow = C.oppositeTurnRow)
    (hopposite : Cr.oppositeTurnRow = C.turnRow) {x : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow Cr.column Cr.turnRow x x) :
    (D.first ∈ G.commutationPentagons C x D.middle ∧
      D.second ∈ (G.swapColumns a b).commutationPentagons Cr D.middle x) ↔
      match D.first, D.second with
      | .inl P, .inl _ => P.left = a
      | .inr P, .inr _ => P.right = c
      | _, _ => False := by
  -- Keep the reverse diagram's marking data while identifying its three geometric parameters.
  rcases Cr with ⟨⟨column, turn, hne⟩, opposite, hnon, hOa, hXa, hOb, hXb⟩
  simp only at hcolumn hturn hopposite
  subst column turn opposite
  let Cr : ColumnCommutationData (G.swapColumns a b) :=
    ⟨⟨a, C.oppositeTurnRow, hne⟩, C.turnRow, hnon, hOa, hXa, hOb, hXb⟩
  rcases D with ⟨m, P, Q⟩
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      -- Same-side turns give a vertical annulus, with both marking tests automatic.
      rw [(G.swapColumns a b).inl_mem_commutationPentagons Cr Q]
      simp only [G.inl_mem_commutationPentagons C, mem_pentagons]
      constructor
      · rintro ⟨⟨hP, _⟩, ⟨hQ, _⟩⟩
        exact (P.isEmpty_and_isEmpty_iff Q).mp ⟨hP, hQ⟩
      · intro hleft
        have h := (P.isEmpty_and_isEmpty_iff Q).mpr hleft
        refine ⟨⟨h.1, G.disjoint_returning_pentagon_markings C P Q h
          G.X C.X_column_below C.X_next_above⟩, ⟨h.2, ?_⟩⟩
        exact (G.swapColumns a b).disjoint_returning_pentagon_markings
          ⟨⟨a, C.oppositeTurnRow, hne⟩, C.turnRow, hnon, hOa, hXa, hOb, hXb⟩
          Q P h.symm _ hXa hXb
    | inr Q =>
      -- Opposite-side turns would force both distinct turn rows into one thin horizontal annulus.
      rw [(G.swapColumns a b).inr_mem_commutationPentagons Cr Q]
      simp only [G.inl_mem_commutationPentagons C, mem_pentagons, mem_initialPentagons]
      exact ⟨fun h => C.turnRow_ne_oppositeTurnRow
        (P.turn_eq_of_isEmpty_and_isEmpty_initial Q ⟨h.1.1, h.2.1⟩), False.elim⟩
  | inr P =>
    cases Q with
    | inl Q =>
      rw [(G.swapColumns a b).inl_mem_commutationPentagons Cr Q]
      simp only [G.inr_mem_commutationPentagons C, mem_pentagons, mem_initialPentagons]
      exact ⟨fun h => C.turnRow_ne_oppositeTurnRow
        (Q.turn_eq_of_isEmpty_and_isEmpty_initial P ⟨h.2.1, h.1.1⟩).symm, False.elim⟩
    | inr Q =>
      rw [(G.swapColumns a b).inr_mem_commutationPentagons Cr Q]
      simp only [G.inr_mem_commutationPentagons C, mem_initialPentagons]
      constructor
      · rintro ⟨⟨hP, _⟩, ⟨hQ, _⟩⟩
        exact (P.isEmpty_and_isEmpty_iff Q).mp ⟨hP, hQ⟩
      · intro hright
        have h := (P.isEmpty_and_isEmpty_iff Q).mpr hright
        refine ⟨⟨h.1, G.disjoint_returning_initialPentagon_markings C P Q h
          G.X C.X_column_below C.X_next_above⟩, ⟨h.2, ?_⟩⟩
        exact (G.swapColumns a b).disjoint_returning_initialPentagon_markings
          ⟨⟨a, C.oppositeTurnRow, hne⟩, C.turnRow, hnon, hOa, hXa, hOb, hXb⟩
          Q P h.symm _ hXa hXb

/-- A counted returning pentagon pair has two terminal-side turns and occupies column `a`,
or two initial-side turns and occupies its successor. Mixed turn sides cannot return. -/
theorem mem_pentagonPairDecompositions_diagonal_iff {x : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x x) :
    D ∈ G.pentagonPairDecompositions C x x ↔
      match D.first, D.second with
      | .inl P, .inl _ => P.left = a
      | .inr P, .inr _ => P.right = c
      | _, _ => False := by
  rw [G.mem_pentagonPairDecompositions C]
  rcases D with ⟨m, P, Q⟩
  cases P <;> cases Q <;>
    exact G.returning_pentagon_pair_iff C C.reverse C.reverse_column C.reverse_turnRow
      C.reverse_oppositeTurnRow _

private theorem returning_pentagon_pair_weight_eq_one
    (Cr : ColumnCommutationData (G.swapColumns a b))
    (hcolumn : Cr.column = a) (hturn : Cr.turnRow = C.oppositeTurnRow)
    (hopposite : Cr.oppositeTurnRow = C.turnRow)
    (R : Type*) [CommSemiring R] {x : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow Cr.column Cr.turnRow x x)
    (hD : D.first ∈ G.commutationPentagons C x D.middle ∧
      D.second ∈ (G.swapColumns a b).commutationPentagons Cr D.middle x) :
    MvPolynomial.rename (Equiv.swap a b) (G.commutationPentagonWeight C R D.first) *
      (G.swapColumns a b).commutationPentagonWeight Cr R D.second = 1 := by
  have hshape := (G.returning_pentagon_pair_iff C Cr hcolumn hturn hopposite D).mp hD
  -- In either surviving vertical annulus, every polynomial factor is one because no O is covered.
  rcases Cr with ⟨⟨column, turn, hne⟩, opposite, hnon, hOa, hXa, hOb, hXb⟩
  simp only at hcolumn hturn hopposite
  subst column turn opposite
  let Cr : ColumnCommutationData (G.swapColumns a b) :=
    ⟨⟨a, C.oppositeTurnRow, hne⟩, C.turnRow, hnon, hOa, hXa, hOb, hXb⟩
  rcases D with ⟨m, P, Q⟩
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      have h := (P.isEmpty_and_isEmpty_iff Q).mpr hshape
      have hPO := G.disjoint_returning_pentagon_markings C P Q h
        G.O C.O_column_below C.O_next_above
      have hQO := (G.swapColumns a b).disjoint_returning_pentagon_markings Cr Q P h.symm
        (G.swapColumns a b).O hOa hOb
      have hP : G.pentagonWeight R C P = 1 := by
        rw [G.pentagonWeight_eq_prod_coveredSquares R C]
        exact Finset.prod_eq_one fun p hp => ite_eq_right (Finset.disjoint_left.mp hPO hp)
      have hQ : (G.swapColumns a b).pentagonWeight R Cr Q = 1 := by
        rw [(G.swapColumns a b).pentagonWeight_eq_prod_coveredSquares R Cr]
        exact Finset.prod_eq_one fun p hp => ite_eq_right (Finset.disjoint_left.mp hQO hp)
      rw [(G.swapColumns a b).commutationPentagonWeight_inl Cr R Q,
        G.commutationPentagonWeight_inl C R P, hP, hQ, map_one, one_mul]
    | inr Q => exact False.elim hshape
  | inr P =>
    cases Q with
    | inl Q => exact False.elim hshape
    | inr Q =>
      have h := (P.isEmpty_and_isEmpty_iff Q).mpr hshape
      have hPO := G.disjoint_returning_initialPentagon_markings C P Q h
        G.O C.O_column_below C.O_next_above
      have hQO := (G.swapColumns a b).disjoint_returning_initialPentagon_markings Cr Q P h.symm
        (G.swapColumns a b).O hOa hOb
      have hP : G.initialPentagonWeight R C P = 1 := by
        rw [G.initialPentagonWeight_eq_prod_coveredSquares R C]
        exact Finset.prod_eq_one fun p hp => ite_eq_right (Finset.disjoint_left.mp hPO hp)
      have hQ : (G.swapColumns a b).initialPentagonWeight R Cr Q = 1 := by
        rw [(G.swapColumns a b).initialPentagonWeight_eq_prod_coveredSquares R Cr]
        exact Finset.prod_eq_one fun p hp => ite_eq_right (Finset.disjoint_left.mp hQO hp)
      rw [(G.swapColumns a b).commutationPentagonWeight_inr Cr R Q,
        G.commutationPentagonWeight_inr C R P, hP, hQ, map_one, one_mul]

/-- Every counted returning pentagon pair has weight one, over any commutative semiring. -/
@[simp]
theorem pentagonPairWeight_eq_one_of_diagonal (R : Type*) [CommSemiring R]
    {x : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x x)
    (hD : D ∈ G.pentagonPairDecompositions C x x) : G.pentagonPairWeight C R D = 1 := by
  rw [G.pentagonPairWeight_def C R D]
  exact G.returning_pentagon_pair_weight_eq_one C C.reverse C.reverse_column C.reverse_turnRow
    C.reverse_oppositeTurnRow R D ((G.mem_pentagonPairDecompositions C D).mp hD)

/-- The diagonal pentagon-pair weighted sum is the cardinality of its counted annuli. -/
theorem sum_pentagonPairWeight_diagonal (R : Type*) [CommSemiring R] (x : GridState n) :
    ∑ D ∈ G.pentagonPairDecompositions C x x, G.pentagonPairWeight C R D =
      ((G.pentagonPairDecompositions C x x).card : MvPolynomial (Fin n) R) := by
  classical
  calc
    _ = ∑ _D ∈ G.pentagonPairDecompositions C x x, (1 : MvPolynomial (Fin n) R) :=
      Finset.sum_congr rfl fun D hD => G.pentagonPairWeight_eq_one_of_diagonal C R D hD
    _ = _ := by simp

private theorem pentagonPair_side_inj (x : GridState n) :
    Set.InjOn (fun D : GridPentagonPairDecomposition a C.turnRow C.reverse.column
      C.reverse.turnRow x x => D.first.isLeft) (G.pentagonPairDecompositions C x x) := by
  rintro ⟨m, P, Q⟩ hD ⟨m', P', Q'⟩ hE hside
  have hD := (G.mem_pentagonPairDecompositions_diagonal_iff C _).mp hD
  have hE := (G.mem_pentagonPairDecompositions_diagonal_iff C _).mp hE
  cases P with
  | inl P =>
    cases P' with
    | inl P' =>
      rcases Q with Q | Q <;> rcases Q' with Q' | Q' <;> simp only at hD hE
      cases P.sigma_eq_of_left_eq Q P' Q' hD hE
      rfl
    | inr P' => simp at hside
  | inr P =>
    cases P' with
    | inl P' => simp at hside
    | inr P' =>
      rcases Q with Q | Q <;> rcases Q' with Q' | Q' <;> simp only at hD hE
      cases P.sigma_eq_of_right_eq Q P' Q' hD hE
      rfl

private theorem exists_pentagonPair_side_iff (x : GridState n) (i : Bool) :
    (∃ D ∈ G.pentagonPairDecompositions C x x, D.first.isLeft = i) ↔
      if i then
        C.turnRow ∈ Grid.cIco (x a) (x b) ∧ C.oppositeTurnRow ∈ Grid.cIco (x b) (x a)
      else
        C.turnRow ∈ Grid.cIco (x b) (x c) ∧ C.oppositeTurnRow ∈ Grid.cIco (x c) (x b) := by
  constructor
  -- The annulus fixes both columns, so the two pentagons supply complementary row tests.
  · rintro ⟨⟨m, P, Q⟩, hD, hi⟩
    have hshape := (G.mem_pentagonPairDecompositions_diagonal_iff C _).mp hD
    cases P with
    | inl P =>
      cases Q with
      | inl Q =>
        have h := (GridPentagonBetween.exists_left_eq_iff C.column_ne_next
          C.reverse_column).mp ⟨m, P, Q, hshape⟩
        cases i <;> simp_all only [Sum.isLeft_inl, Bool.true_eq_false, ite_true,
          C.reverse_turnRow, and_self]
      | inr Q => exact False.elim hshape
    | inr P =>
      cases Q with
      | inl Q => exact False.elim hshape
      | inr Q =>
        have h := (GridInitialPentagonBetween.exists_right_eq_iff C.column_ne_next
          C.reverse_column).mp ⟨m, P, Q, hshape⟩
        cases i <;> simp_all only [Sum.isLeft_inr, Bool.false_eq_true, ite_false,
          C.reverse_turnRow, and_self]
  -- Conversely construct each thin annulus from the two row tests, retaining the actual
  -- reverse commutation indices in the returning pentagon.
  · cases i with
    | true =>
      rintro ⟨hs, ht⟩
      obtain ⟨m, P, Q, h⟩ := (GridPentagonBetween.exists_left_eq_iff (t := C.reverse.turnRow)
        C.column_ne_next C.reverse_column).mpr ⟨hs, by rwa [C.reverse_turnRow]⟩
      exact ⟨⟨m, Sum.inl P, Sum.inl Q⟩,
        (G.mem_pentagonPairDecompositions_diagonal_iff C _).mpr h, rfl⟩
    | false =>
      rintro ⟨hs, ht⟩
      obtain ⟨m, P, Q, h⟩ := (GridInitialPentagonBetween.exists_right_eq_iff
        (t := C.reverse.turnRow) C.column_ne_next C.reverse_column).mpr
        ⟨hs, by rwa [C.reverse_turnRow]⟩
      exact ⟨⟨m, Sum.inr P, Sum.inr Q⟩,
        (G.mem_pentagonPairDecompositions_diagonal_iff C _).mpr h, rfl⟩

/-- The number of returning pentagon pairs is the sum of the two complementary-turn
indicators, one for each column adjacent to the replaced line. -/
theorem card_pentagonPairDecompositions_diagonal (x : GridState n) :
    (G.pentagonPairDecompositions C x x).card =
      (if C.turnRow ∈ Grid.cIco (x a) (x b) ∧
        C.oppositeTurnRow ∈ Grid.cIco (x b) (x a) then 1 else 0) +
      (if C.turnRow ∈ Grid.cIco (x b) (x c) ∧
        C.oppositeTurnRow ∈ Grid.cIco (x c) (x b) then 1 else 0) := by
  classical
  have himage : (G.pentagonPairDecompositions C x x).image (fun D => D.first.isLeft) =
      Finset.univ.filter (fun i : Bool => if i then
        C.turnRow ∈ Grid.cIco (x a) (x b) ∧ C.oppositeTurnRow ∈ Grid.cIco (x b) (x a)
      else C.turnRow ∈ Grid.cIco (x b) (x c) ∧
        C.oppositeTurnRow ∈ Grid.cIco (x c) (x b)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact G.exists_pentagonPair_side_iff C x i
  rw [← Finset.card_image_of_injOn (G.pentagonPair_side_inj C x), himage, Fintype.univ_bool]
  simp only [Finset.filter_insert, Finset.filter_singleton, Bool.coe_false, ite_true, ite_false]
  split_ifs <;> simp

/-- The round-trip commutation map has diagonal coefficient given by the two possible
empty returning pentagon annuli. -/
theorem reverse_commutationMap_commutationMap_single_apply_self
    (R : Type*) [CommSemiring R] (x : GridState n) :
    (G.swapColumns a b).commutationMap R C.reverse
        (G.commutationMap R C (Finsupp.single x 1)) x =
      (if C.turnRow ∈ Grid.cIco (x a) (x b) ∧
        C.oppositeTurnRow ∈ Grid.cIco (x b) (x a) then 1 else 0) +
      (if C.turnRow ∈ Grid.cIco (x b) (x c) ∧
        C.oppositeTurnRow ∈ Grid.cIco (x c) (x b) then 1 else 0) := by
  rw [G.reverse_commutationMap_commutationMap_single_apply C R,
    G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient C R,
    G.sum_pentagonPairWeight_diagonal C R, G.card_pentagonPairDecompositions_diagonal C]
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- The diagonal coefficient of the commutation homotopy equation
`∂H + H∂ = 1 + ΨΦ`, over any commutative semiring of characteristic two. -/
theorem unblockedDifferential_commutationHomotopy_add_single_apply_self_eq_one_add
    (R : Type*) [CommSemiring R] [CharP R 2] (x : GridState n) :
    (G.unblockedDifferential R (G.commutationHomotopy R C (Finsupp.single x 1)) +
        G.commutationHomotopy R C (G.unblockedDifferential R (Finsupp.single x 1))) x =
      1 + (G.swapColumns a b).commutationMap R C.reverse
        (G.commutationMap R C (Finsupp.single x 1)) x := by
  classical
  rw [G.unblockedDifferential_commutationHomotopy_add_single_apply_self C R,
    G.reverse_commutationMap_commutationMap_single_apply_self C R]
  have huv : x a ≠ x b := x.toPerm.injective.ne C.column_ne_next
  have hvw : x b ≠ x c :=
    x.toPerm.injective.ne ((finRotate n).injective.ne C.column_ne_next)
  have hst := C.turnRow_ne_oppositeTurnRow
  have hleft := (Grid.ite_eq_or_mem_cIoo_eq_add_add huv hst).symm
  have hright := (Grid.ite_eq_or_mem_cIoo_eq_add_add hvw.symm hst.symm).symm
  have hpartition :
      ((if x b = C.oppositeTurnRow ∨ x b ∈ Grid.cIoo C.turnRow C.oppositeTurnRow
        then 1 else 0) : ℕ) +
      (if x b = C.turnRow ∨ x b ∈ Grid.cIoo C.oppositeTurnRow C.turnRow
        then 1 else 0) = 1 := by
    simp only [Grid.mem_cIoo, Fin.ext_iff] at hst ⊢
    split_ifs <;> omega
  have hsum := congrArg (fun k : ℕ => (k : MvPolynomial (Fin n) R))
    ((congrArg₂ (fun k l : ℕ => k + l) hleft hright).trans hpartition)
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hsum
  simp only [@and_comm (C.oppositeTurnRow ∈ Grid.cIco (x c) (x b))] at hsum
  apply CharTwo.eq_add_iff_add_eq.mpr
  convert hsum using 1
  ac_rfl

/-- The diagonal commutation homotopy identity as sums of polygon-pair weights, over any
commutative semiring of characteristic two. -/
theorem sum_hexagonRectangleWeight_add_sum_rectangleHexagonWeight_self_eq_one_add
    (R : Type*) [CommSemiring R] [CharP R 2] (x : GridState n) :
    (∑ D ∈ G.hexagonRectangleDecompositions C x x, G.hexagonRectangleWeight C R D) +
        ∑ D ∈ G.rectangleHexagonDecompositions C x x, G.rectangleHexagonWeight C R D =
      1 + ∑ D ∈ G.pentagonPairDecompositions C x x, G.pentagonPairWeight C R D := by
  simpa only [Finsupp.add_apply,
    G.unblockedDifferential_commutationHomotopy_single_apply C R,
    G.commutationHomotopy_unblockedDifferential_single_apply C R,
    G.reverse_commutationMap_commutationMap_single_apply C R,
    G.sum_commutationHexagonCoefficient_mul_unblockedCoefficient C R,
    G.sum_unblockedCoefficient_mul_commutationHexagonCoefficient C R,
    G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient C R] using
    G.unblockedDifferential_commutationHomotopy_add_single_apply_self_eq_one_add C R x

/-! ### The replaced grid line as a common side -/

/-- The replaced grid line is a common side of the two rectangles of a pentagon pair: the
terminal side of a terminal-side pentagon and the initial side of an initial-side one. -/
theorem finRotate_mem_commonSideColumns_of_pentagonPair {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x z) :
    b ∈ D.toRectangleDecomposition.commonSideColumns := by
  rcases D with ⟨m, P | P, Q | Q⟩
  · simp [P.right_eq, Q.right_eq]
  · simp [P.right_eq, Q.left_eq]
  · simp [P.left_eq, Q.right_eq]
  · simp [P.left_eq, Q.left_eq]

end GridDiagram
end TauCeti
