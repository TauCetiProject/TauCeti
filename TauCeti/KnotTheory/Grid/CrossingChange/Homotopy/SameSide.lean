/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Recut
import TauCeti.Data.Finset.Basic

/-!
# Same-side pentagon pairs of a crossing change

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row. The round trip `Ψ ∘ Φ` of the crossing change maps
counts a pentagon of `G` turning in row `s` (`GridDiagram.commutationMap` of `C`) followed by a
pentagon of `G' = G.swapColumns a b` turning in row `t` (the commutation map of `G'` at
`C.withTurnRow t`). This file treats the pairs whose two pentagons turn on the same side of the
replaced grid line `b`: both on their terminal side, or both on their initial side. Off the
diagonal, each of them is matched with exactly one unpaired composite of the crossing change
homotopy equation (`GridDiagram.crossingChangeUnpairedHexagonComposites`): the recut of its two
rectangles, of the same weight.

The two rectangles of such a pair share the grid line `b` and are stacked along it: for two
terminal-side pentagons the second lies directly below the first, so `t` lies below `s`, and for
two initial-side pentagons it lies directly above the first, so `s` lies below `t`. Their union is
an L-shaped domain, and its recut from the proof of `∂² = 0` consists of a rectangle and a
rectangle spanning the rows of both with the side `b`. The latter contains both turn rows in the
order of a hexagon of the crossing change, so it underlies a hexagon cutting away the rows between
the two turn points in one of the columns `a` and `b`, and adding the rows strictly between them
in the other. Away from these two columns the hexagon and the other rectangle cover the squares of
the original rectangles. In the two columns a comparison of cyclic row intervals shows that they
cover exactly the squares the two pentagons carry, the second read in `G` by exchanging the
columns. So the composite is counted and has the weight of the pair, without any assumption on
where the markings of the columns `a` and `b` lie. Neither pentagon contains both turn rows, so
no composite has the rectangles of the pair, and the composite is unpaired. If the annulus squares
carry no `X`-marking it is the only counted composite recutting the pair.

## Main results

* `existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair`, in the namespace
  `TauCeti.GridDiagram`: a counted off-diagonal pair of terminal-side pentagons has exactly one
  unpaired composite recutting its rectangles, and their weights agree.
* `existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair`, in the namespace
  `TauCeti.GridDiagram`: the same for pairs of initial-side pentagons.

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

variable (R : Type*) [CommSemiring R]

/-! ### Terminal-side pairs -/

section TerminalPair

variable {x y z : GridState n} (P : GridPentagonBetween C.column C.turnRow x y)
  (Q : GridPentagonBetween C.column t y z)

/-- Let a rectangle `S` and a terminal-side hexagon `H` from `t` up to `s` cover the squares of
the rectangles of a terminal-side pentagon pair without overlap, `H` spanning the rows of both.
Then `S` and the squares `H` carries as a hexagon of the crossing change cover exactly the squares
the two pentagons carry, the second read in `G` by exchanging the columns `a` and `b`, and both
pairs of sets are disjoint. -/
private theorem terminalPair_squares {u v u' v' : GridState n} (S : GridRectangleBetween u v)
    (H : GridHexagonBetween a t C.turnRow u' v')
    (hrep : S.toGridRectangle.coveredSquares ∪ H.toGridRectangle.coveredSquares =
      P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares)
    (hSH : Disjoint S.toGridRectangle.coveredSquares H.toGridRectangle.coveredSquares)
    (hPQ : Disjoint P.toGridRectangle.coveredSquares Q.toGridRectangle.coveredSquares)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom)
    (hHb : H.bottom = Q.bottom) (hHt : H.top = P.top) :
    P.coveredSquares ∪
        Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      S.toGridRectangle.coveredSquares ∪ H.crossingCoveredSquares ∧
    Disjoint P.coveredSquares
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) ∧
    Disjoint S.toGridRectangle.coveredSquares H.crossingCoveredSquares := by
  have hab := C.column_ne_next
  have hs := P.turn_mem_cIco_bottom_top
  have ht : t ∈ Grid.cIco Q.bottom P.bottom := htop ▸ Q.turn_mem_cIco_bottom_top
  -- The rectangle of the hexagon covers column `a` in the rows of both pentagons.
  have hHa (r : Fin n) :
      (a, r) ∈ H.toGridRectangle.coveredSquares ↔ r ∈ Grid.cIco Q.bottom P.top := by
    rw [H.mem_toGridRectangle_coveredSquares, ← hHb, ← hHt]
    exact and_iff_right (Grid.self_mem_cIco_finRotate H.left_ne)
  -- The rectangle `S` covers no square of the hexagon's rectangle, so it covers nothing in
  -- column `a`, and nothing in column `b` since neither pentagon's rectangle does.
  have hS (p : Fin n × Fin n) (h : p ∈ S.toGridRectangle.coveredSquares) : p.1 ≠ a ∧ p.1 ≠ b := by
    obtain ⟨c, r⟩ := p
    have hPQr := hrep ▸ Finset.mem_union_left _ h
    refine ⟨?_, ?_⟩ <;> rintro rfl
    · refine Finset.disjoint_left.mp hSH h ((hHa r).mpr ?_)
      rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow, Finset.mem_union]
      rcases Finset.mem_union.mp hPQr with h' | h'
      · exact Or.inr ((P.mk_mem_toGridRectangle_coveredSquares_left_column r).mp h')
      · exact Or.inl (htop ▸ (Q.mk_mem_toGridRectangle_coveredSquares_left_column r).mp h')
    · rcases Finset.mem_union.mp hPQr with h' | h'
      · exact P.mk_notMem_toGridRectangle_coveredSquares_right_column r h'
      · exact Q.mk_notMem_toGridRectangle_coveredSquares_right_column r h'
  refine Finset.union_eq_union_and_disjoint_and_disjoint_of_repartition
    (fun p : Fin n × Fin n => p.1 = a ∨ p.1 = b) hrep hSH hPQ
    (fun p hp => P.mem_coveredSquares_iff_of_ne (hp <| .inl ·) (hp <| .inr ·))
    (fun p hp => (Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ (hp <| .inl ·)
      (hp <| .inr ·)).trans (Q.mem_coveredSquares_iff_of_ne (hp <| .inl ·) (hp <| .inr ·)))
    (fun p hp => by
      rw [not_or] at hp
      rw [H.mem_crossingCoveredSquares]
      simp only [hp.1, hp.2, false_and, not_false_eq_true, and_true, or_false])
    (fun p h => not_or.mpr (hS p h)) ?_
  -- In the columns `a` and `b`, membership in each domain is a cyclic row interval.
  rintro ⟨c, r⟩ (rfl | rfl)
  · rw [P.mk_mem_coveredSquares_left_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
      Equiv.swap_apply_left, Q.mk_mem_coveredSquares_right_column, H.mem_crossingCoveredSquares,
      hHa]
    simp only [true_and, hab, false_and, or_false]
    obtain ⟨h₁, h₂⟩ :=
      Grid.mem_cIco_or_mem_cIoo_iff_mem_cIco_and_notMem_insert_cIco (r := r) hrow ht hs
    exact ⟨or_comm.trans h₁, fun h => h₂ h.symm⟩
  · rw [P.mk_mem_coveredSquares_right_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
      Equiv.swap_apply_right, Q.mk_mem_coveredSquares_left_column, htop,
      H.mem_crossingCoveredSquares]
    simp only [H.mem_toGridRectangle_coveredSquares, Grid.right_notMem_cIco, false_and,
      hab.symm, false_or, true_and]
    obtain ⟨h₁, h₂⟩ := Grid.mem_cIoo_or_mem_cIco_iff_mem_cIoo (r := r) hrow ht hs
    exact ⟨or_comm.trans h₁, fun h => h₂ h.symm⟩

/-- The recut of the rectangles of a counted terminal-side pentagon pair whose first initial side
lies inside the columns of the second rectangle underlies a counted composite of the weight of
the pair. -/
private theorem terminalPair_exists_of_first_left_mem_cIoo
    (hone : GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ : GridRectangleDecomposition x z))
    (hp : P.IsEmpty) (hq : Q.IsEmpty) (hpX : Disjoint P.coveredSquares G.XSet)
    (hqX' : Disjoint
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom)
    (hlower : t ∈ Grid.cIco Q.bottom P.top) (hupper : C.turnRow ∈ Grid.cIoo t P.top)
    (hcol : P.left ∈ Grid.cIoo Q.left P.right) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition =
          GridRectangleDecomposition.recut ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
            hone hp hq ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.pentagonWeight R C P) *
            (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right := P.right_eq.trans Q.right_eq.symm
  let E := D.recut hone hp hq
  have hrecut := D.isRecut_recut hone hp hq
  rw [rename_pentagonWeight, G.pentagonWeight_swapColumns R (C.withTurnRow t)]
  -- The first initial side lies inside the second rectangle's columns: the recut is a rectangle
  -- followed by a rectangle spanning the rows of both, with terminal side `b`.
  obtain ⟨-, -, -, -, hsb, hst⟩ :=
    D.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol hp hq
  have hsr : E.second.right = b := by
    rcases (D.isRecutOfRightEqRight_recut hcommon hone hp hq).recut_branch with h | h
    · exact h.2.2.2.trans P.right_eq
    · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hcol
        (Grid.mem_cIoo_cyclic_right h.1)).elim
  let H : GridHexagonBetween a t C.turnRow E.middle z :=
    { toGridRectangleBetween := E.second
      right_eq := hsr
      lower_mem := by
        rw [← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, hsb, hst]
        exact hlower
      upper_mem := by
        rw [← GridRectangleBetween.top_def, hst]
        exact hupper }
  have hkey := terminalPair_squares P Q E.first H hrecut.isRepartition.coveredSquares_union_eq
    hrecut.isRepartition.disjoint_coveredSquares_right
    hrecut.isRepartition.disjoint_coveredSquares_left hrow htop hsb hst
  rw [← GridCommutationHexagonBetween.crossingCoveredSquares_inl] at hkey
  obtain ⟨hSX, hHX, hw⟩ :=
    disjoint_XSet_and_OMonomial_mul_crossingChangeCommutationHexagonWeight_eq R E.first
      (.inl H) hkey hpX hqX'
  rw [← hw]
  exact exists_inr_mem_crossingChangeHexagonCompositeDecompositions R (.inl H)
    (GridCommutationHexagonBetween.toGridRectangleBetween_inl H) hrecut.isEmpty_first
    hrecut.isEmpty_second hSX hHX

/-- The recut of the rectangles of a counted terminal-side pentagon pair whose second initial side
lies inside the columns of the first rectangle underlies a counted composite of the weight of
the pair. -/
private theorem terminalPair_exists_of_second_left_mem_cIoo
    (hone : GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ : GridRectangleDecomposition x z))
    (hp : P.IsEmpty) (hq : Q.IsEmpty) (hpX : Disjoint P.coveredSquares G.XSet)
    (hqX' : Disjoint
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet)
    (hrow : P.bottom ∈ Grid.cIoo Q.bottom P.top) (htop : Q.top = P.bottom)
    (hlower : t ∈ Grid.cIco Q.bottom P.top) (hupper : C.turnRow ∈ Grid.cIoo t P.top)
    (hcol : Q.left ∈ Grid.cIoo P.left P.right) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition =
          GridRectangleDecomposition.recut ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
            hone hp hq ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.pentagonWeight R C P) *
            (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right := P.right_eq.trans Q.right_eq.symm
  let E := D.recut hone hp hq
  have hrecut := D.isRecut_recut hone hp hq
  rw [rename_pentagonWeight, G.pentagonWeight_swapColumns R (C.withTurnRow t)]
  -- The second initial side lies inside the first rectangle's columns: the recut is a rectangle
  -- spanning the rows of both, with terminal side `b`, followed by a rectangle.
  obtain ⟨hfr, -, hfb, hft, -, -⟩ :=
    D.recut_geometry_of_right_eq_right_of_second_left_mem_cIoo hcommon hcol hp hq
  let H : GridHexagonBetween a t C.turnRow x E.middle :=
    { toGridRectangleBetween := E.first
      right_eq := hfr.trans P.right_eq
      lower_mem := by
        rw [← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, hfb, hft]
        exact hlower
      upper_mem := by
        rw [← GridRectangleBetween.top_def, hft]
        exact hupper }
  have hkey := terminalPair_squares P Q E.second H
    (by rw [Finset.union_comm]; exact hrecut.isRepartition.coveredSquares_union_eq)
    hrecut.isRepartition.disjoint_coveredSquares_right.symm
    hrecut.isRepartition.disjoint_coveredSquares_left hrow htop hfb hft
  rw [← GridCommutationHexagonBetween.crossingCoveredSquares_inl] at hkey
  obtain ⟨hSX, hHX, hw⟩ :=
    disjoint_XSet_and_OMonomial_mul_crossingChangeCommutationHexagonWeight_eq R E.second
      (.inl H) hkey hpX hqX'
  rw [← hw, mul_comm]
  exact exists_inl_mem_crossingChangeHexagonCompositeDecompositions R (.inl H)
    (GridCommutationHexagonBetween.toGridRectangleBetween_inl H) hrecut.isEmpty_first
    hrecut.isEmpty_second hHX hSX

/-- The recut of the rectangles of a counted terminal-side pentagon pair with distinct initial
sides underlies a counted composite of the weight of the pair. -/
private theorem terminalPair_exists (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z)
    (hone : GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ : GridRectangleDecomposition x z))
    (hne : P.left ≠ Q.left) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition =
          GridRectangleDecomposition.recut ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
            hone ((G.mem_pentagons P).mp hP).1
            (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ).1 ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.pentagonWeight R C P) *
            (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ
  have hqX' := (G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right := P.right_eq.trans Q.right_eq.symm
  obtain ⟨hrow, htop⟩ := P.bottom_mem_cIoo_and_top_eq_of_right_eq_right Q.toGridRectangleBetween
    (P.right_eq.trans Q.right_eq.symm) hne hp hq
  have ht : t ∈ Grid.cIco Q.bottom P.bottom := htop ▸ Q.turn_mem_cIco_bottom_top
  obtain ⟨hlower, hupper⟩ :=
    Grid.mem_cIco_and_mem_cIoo_of_mem_cIco_of_mem_cIco hrow ht P.turn_mem_cIco_bottom_top
  rcases (D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hne hp hq).1 with hcol | hcol
  · exact terminalPair_exists_of_first_left_mem_cIoo R P Q hone hp hq hpX hqX' hrow htop hlower
      hupper hcol
  · exact terminalPair_exists_of_second_left_mem_cIoo R P Q hone hp hq hpX hqX' hrow htop hlower
      hupper hcol

end TerminalPair

/-- **Terminal-side pentagon pairs of a crossing change.** Let the annulus squares carry no
`X`-marking. A counted pentagon of `G` turning on its terminal side in the turn row of `C`,
followed by a counted terminal-side pentagon of `G' = G.swapColumns a b` turning in row `t`, from
`x` to `z ≠ x`, has exactly one unpaired composite of the crossing change homotopy equation
recutting its two rectangles, and their weights agree. That composite consists of a rectangle and
a terminal-side hexagon spanning the rows of both pentagons. -/
theorem existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x y z : GridState n} (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween a t y z) (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z) (hzx : z ≠ x) :
    (∃! F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition) ∧
      ∀ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        GridRectangleDecomposition.IsRecut
            (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
              GridRectangleDecomposition x z) F.toRectangleDecomposition →
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.pentagonWeight R C P) *
              (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  have hp := ((G.mem_pentagons P).mp hP).1
  have hq := (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ).1
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.right = D.second.right := P.right_eq.trans Q.right_eq.symm
  -- Off the diagonal, the common terminal side is the only common side.
  have hone : D.HasOneCommonSide := D.hasOneCommonSide_of_mem_commonSideColumns
    (c := D.first.right)
    (by simp [D.mem_commonSideColumns, GridRectangleBetween.mem_sideColumns, hcommon]) hzx
  have hne : P.left ≠ Q.left := fun h => D.sideColumns_ne_of_hasOneCommonSide hone (by
    rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns]
    exact congrArg₂ (fun c d => ({c, d} : Finset (Fin n))) h hcommon)
  obtain ⟨hrow, htop⟩ := P.bottom_mem_cIoo_and_top_eq_of_right_eq_right Q.toGridRectangleBetween
    (P.right_eq.trans Q.right_eq.symm) hne hp hq
  have hdisj := Grid.disjoint_cIco_cIco_of_mem_cIoo hrow
  refine existsUnique_crossingChangeUnpairedHexagonComposite_isRecut R hX hone hp hq
    (fun F => F.toRectangleDecomposition_ne_of_notMem_cIco (fun h => ?_) (fun h => ?_))
    (terminalPair_exists R P Q hP hQ hone hne)
  · exact Finset.disjoint_left.mp hdisj (htop ▸ Q.turn_mem_cIco_bottom_top) h
  · exact Finset.disjoint_left.mp hdisj (htop ▸ h) P.turn_mem_cIco_bottom_top

/-! ### Initial-side pairs -/

section InitialPair

variable {x y z : GridState n} (P : GridInitialPentagonBetween C.column C.turnRow x y)
  (Q : GridInitialPentagonBetween C.column t y z)

/-- Let a rectangle `S` and an initial-side hexagon `H` from `s` up to `t` cover the squares of
the rectangles of an initial-side pentagon pair without overlap, `H` spanning the rows of both.
Then `S` and the squares `H` carries as a hexagon of the crossing change cover exactly the squares
the two pentagons carry, the second read in `G` by exchanging the columns `a` and `b`, and both
pairs of sets are disjoint. -/
private theorem initialPair_squares {u v u' v' : GridState n} (S : GridRectangleBetween u v)
    (H : GridInitialHexagonBetween a C.turnRow t u' v')
    (hrep : S.toGridRectangle.coveredSquares ∪ H.toGridRectangle.coveredSquares =
      P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares)
    (hSH : Disjoint S.toGridRectangle.coveredSquares H.toGridRectangle.coveredSquares)
    (hPQ : Disjoint P.toGridRectangle.coveredSquares Q.toGridRectangle.coveredSquares)
    (hrow : P.top ∈ Grid.cIoo P.bottom Q.top) (hbottom : Q.bottom = P.top)
    (hHb : H.bottom = P.bottom) (hHt : H.top = Q.top) :
    P.coveredSquares ∪
        Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      S.toGridRectangle.coveredSquares ∪ H.crossingCoveredSquares ∧
    Disjoint P.coveredSquares
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) ∧
    Disjoint S.toGridRectangle.coveredSquares H.crossingCoveredSquares := by
  have hab := C.column_ne_next
  have hs := P.turn_mem_cIco_bottom_top
  have ht : t ∈ Grid.cIco P.top Q.top := hbottom ▸ Q.turn_mem_cIco_bottom_top
  -- The rectangle of the hexagon covers column `b` in the rows of both pentagons.
  have hHb' (r : Fin n) :
      (b, r) ∈ H.toGridRectangle.coveredSquares ↔ r ∈ Grid.cIco P.bottom Q.top := by
    rw [H.mem_toGridRectangle_coveredSquares, ← hHb, ← hHt]
    exact and_iff_right (Grid.left_mem_cIco H.right_ne.symm)
  have hHa (r : Fin n) : (a, r) ∉ H.toGridRectangle.coveredSquares := by
    rw [H.mem_toGridRectangle_coveredSquares]
    exact fun h => (by simp : a ∉ Grid.cIco b H.right) h.1
  -- The rectangle `S` covers no square of the hexagon's rectangle, so it covers nothing in
  -- column `b`, and nothing in column `a` since neither pentagon's rectangle does.
  have hS (p : Fin n × Fin n) (h : p ∈ S.toGridRectangle.coveredSquares) : p.1 ≠ a ∧ p.1 ≠ b := by
    obtain ⟨c, r⟩ := p
    have hPQr := hrep ▸ Finset.mem_union_left _ h
    refine ⟨?_, ?_⟩ <;> rintro rfl
    · rcases Finset.mem_union.mp hPQr with h' | h'
      · exact P.mk_notMem_toGridRectangle_coveredSquares_left_column r h'
      · exact Q.mk_notMem_toGridRectangle_coveredSquares_left_column r h'
    · refine Finset.disjoint_left.mp hSH h ((hHb' r).mpr ?_)
      rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow, Finset.mem_union]
      rcases Finset.mem_union.mp hPQr with h' | h'
      · exact Or.inl ((P.mk_mem_toGridRectangle_coveredSquares_right_column r).mp h')
      · exact Or.inr (hbottom ▸ (Q.mk_mem_toGridRectangle_coveredSquares_right_column r).mp h')
  refine Finset.union_eq_union_and_disjoint_and_disjoint_of_repartition
    (fun p : Fin n × Fin n => p.1 = a ∨ p.1 = b) hrep hSH hPQ
    (fun p hp => P.mem_coveredSquares_iff_of_ne (hp <| .inl ·) (hp <| .inr ·))
    (fun p hp => (Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ (hp <| .inl ·)
      (hp <| .inr ·)).trans (Q.mem_coveredSquares_iff_of_ne (hp <| .inl ·) (hp <| .inr ·)))
    (fun p hp => by
      rw [not_or] at hp
      rw [H.mem_crossingCoveredSquares]
      simp only [hp.1, hp.2, false_and, not_false_eq_true, and_true, or_false])
    (fun p h => not_or.mpr (hS p h)) ?_
  -- In the columns `a` and `b`, membership in each domain is a cyclic row interval.
  rintro ⟨c, r⟩ (rfl | rfl)
  · rw [P.mk_mem_coveredSquares_left_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
      Equiv.swap_apply_left, Q.mk_mem_coveredSquares_right_column, hbottom,
      H.mem_crossingCoveredSquares]
    simp only [hHa r, false_and, hab, false_or, true_and]
    exact Grid.mem_cIoo_or_mem_cIco_iff_mem_cIoo hrow hs ht
  · rw [P.mk_mem_coveredSquares_right_column, Finset.mk_mem_map_swap_prodCongr_refl_iff,
      Equiv.swap_apply_right, Q.mk_mem_coveredSquares_left_column, H.mem_crossingCoveredSquares,
      hHb']
    simp only [true_and, hab.symm, false_and, or_false]
    exact Grid.mem_cIco_or_mem_cIoo_iff_mem_cIco_and_notMem_insert_cIco hrow hs ht

/-- The recut of the rectangles of a counted initial-side pentagon pair whose first terminal side
lies inside the columns of the second rectangle underlies a counted composite of the weight of
the pair. -/
private theorem initialPair_exists_of_first_right_mem_cIoo
    (hone : GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ : GridRectangleDecomposition x z))
    (hp : P.IsEmpty) (hq : Q.IsEmpty) (hpX : Disjoint P.coveredSquares G.XSet)
    (hqX' : Disjoint
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet)
    (hrow : P.top ∈ Grid.cIoo P.bottom Q.top) (hbottom : Q.bottom = P.top)
    (hlower : C.turnRow ∈ Grid.cIco P.bottom Q.top) (hupper : t ∈ Grid.cIoo C.turnRow Q.top)
    (hcol : P.right ∈ Grid.cIoo P.left Q.right) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition =
          GridRectangleDecomposition.recut ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
            hone hp hq ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
            (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  let E := D.recut hone hp hq
  have hrecut := D.isRecut_recut hone hp hq
  rw [rename_initialPentagonWeight, G.initialPentagonWeight_swapColumns R (C.withTurnRow t)]
  -- The first terminal side lies inside the second rectangle's columns: the recut is a
  -- rectangle followed by a rectangle spanning the rows of both, with initial side `b`.
  obtain ⟨-, -, hsl, -⟩ :=
    D.recut_sides_of_left_eq_left_of_first_right_mem_cIoo hcommon hcol hp hq
  obtain ⟨hsb, hst⟩ :=
    D.recut_second_bottom_top_of_left_eq_left_of_first_right_mem_cIoo hcommon hcol hp hq
  let H : GridInitialHexagonBetween a C.turnRow t E.middle z :=
    { toGridRectangleBetween := E.second
      left_eq := hsl.trans P.left_eq
      lower_mem := by
        rw [← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, hsb, hst]
        exact hlower
      upper_mem := by
        rw [← GridRectangleBetween.top_def, hst]
        exact hupper }
  have hkey := initialPair_squares P Q E.first H hrecut.isRepartition.coveredSquares_union_eq
    hrecut.isRepartition.disjoint_coveredSquares_right
    hrecut.isRepartition.disjoint_coveredSquares_left hrow hbottom hsb hst
  rw [← GridCommutationHexagonBetween.crossingCoveredSquares_inr] at hkey
  obtain ⟨hSX, hHX, hw⟩ :=
    disjoint_XSet_and_OMonomial_mul_crossingChangeCommutationHexagonWeight_eq R E.first
      (.inr H) hkey hpX hqX'
  rw [← hw]
  exact exists_inr_mem_crossingChangeHexagonCompositeDecompositions R (.inr H)
    (GridCommutationHexagonBetween.toGridRectangleBetween_inr H) hrecut.isEmpty_first
    hrecut.isEmpty_second hSX hHX

/-- The recut of the rectangles of a counted initial-side pentagon pair whose second terminal side
lies inside the columns of the first rectangle underlies a counted composite of the weight of
the pair. -/
private theorem initialPair_exists_of_second_right_mem_cIoo
    (hone : GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ : GridRectangleDecomposition x z))
    (hp : P.IsEmpty) (hq : Q.IsEmpty) (hpX : Disjoint P.coveredSquares G.XSet)
    (hqX' : Disjoint
      (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet)
    (hrow : P.top ∈ Grid.cIoo P.bottom Q.top) (hbottom : Q.bottom = P.top)
    (hlower : C.turnRow ∈ Grid.cIco P.bottom Q.top) (hupper : t ∈ Grid.cIoo C.turnRow Q.top)
    (hcol : Q.right ∈ Grid.cIoo P.left P.right) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition =
          GridRectangleDecomposition.recut ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
            hone hp hq ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
            (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  let E := D.recut hone hp hq
  have hrecut := D.isRecut_recut hone hp hq
  rw [rename_initialPentagonWeight, G.initialPentagonWeight_swapColumns R (C.withTurnRow t)]
  -- The second terminal side lies inside the first rectangle's columns: the recut is a
  -- rectangle spanning the rows of both, with initial side `b`, followed by a rectangle.
  obtain ⟨hfl, -, -, -⟩ := D.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hcol hp hq
  obtain ⟨hfb, hft⟩ := D.recut_first_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hcol hp hq
  let H : GridInitialHexagonBetween a C.turnRow t x E.middle :=
    { toGridRectangleBetween := E.first
      left_eq := hfl.trans P.left_eq
      lower_mem := by
        rw [← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, hfb, hft]
        exact hlower
      upper_mem := by
        rw [← GridRectangleBetween.top_def, hft]
        exact hupper }
  have hkey := initialPair_squares P Q E.second H
    (by rw [Finset.union_comm]; exact hrecut.isRepartition.coveredSquares_union_eq)
    hrecut.isRepartition.disjoint_coveredSquares_right.symm
    hrecut.isRepartition.disjoint_coveredSquares_left hrow hbottom hfb hft
  rw [← GridCommutationHexagonBetween.crossingCoveredSquares_inr] at hkey
  obtain ⟨hSX, hHX, hw⟩ :=
    disjoint_XSet_and_OMonomial_mul_crossingChangeCommutationHexagonWeight_eq R E.second
      (.inr H) hkey hpX hqX'
  rw [← hw, mul_comm]
  exact exists_inl_mem_crossingChangeHexagonCompositeDecompositions R (.inr H)
    (GridCommutationHexagonBetween.toGridRectangleBetween_inr H) hrecut.isEmpty_first
    hrecut.isEmpty_second hHX hSX

/-- The recut of the rectangles of a counted initial-side pentagon pair with distinct terminal
sides underlies a counted composite of the weight of the pair. -/
private theorem initialPair_exists (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z)
    (hone : GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ : GridRectangleDecomposition x z))
    (hne : P.right ≠ Q.right) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition =
          GridRectangleDecomposition.recut ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
            hone ((G.mem_initialPentagons P).mp hP).1
            (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ).1 ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
            (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ
  have hqX' := (G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  obtain ⟨hrow, hbottom⟩ := P.top_mem_cIoo_and_bottom_eq_of_left_eq_left Q.toGridRectangleBetween
    (P.left_eq.trans Q.left_eq.symm) hne hp hq
  have ht : t ∈ Grid.cIco P.top Q.top := hbottom ▸ Q.turn_mem_cIco_bottom_top
  obtain ⟨hlower, hupper⟩ :=
    Grid.mem_cIco_and_mem_cIoo_of_mem_cIco_of_mem_cIco hrow P.turn_mem_cIco_bottom_top ht
  rcases (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hne hp hq).1 with hcol | hcol
  · exact initialPair_exists_of_first_right_mem_cIoo R P Q hone hp hq hpX hqX' hrow hbottom hlower
      hupper hcol
  · exact initialPair_exists_of_second_right_mem_cIoo R P Q hone hp hq hpX hqX' hrow hbottom hlower
      hupper hcol

end InitialPair

/-- **Initial-side pentagon pairs of a crossing change.** Let the annulus squares carry no
`X`-marking. A counted pentagon of `G` turning on its initial side in the turn row of `C`,
followed by a counted initial-side pentagon of `G' = G.swapColumns a b` turning in row `t`, from
`x` to `z ≠ x`, has exactly one unpaired composite of the crossing change homotopy equation
recutting its two rectangles, and their weights agree. That composite consists of a rectangle and
an initial-side hexagon spanning the rows of both pentagons. -/
theorem existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x y z : GridState n} (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a t y z) (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z) (hzx : z ≠ x) :
    (∃! F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        GridRectangleDecomposition.IsRecut
          (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) F.toRectangleDecomposition) ∧
      ∀ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        GridRectangleDecomposition.IsRecut
            (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
              GridRectangleDecomposition x z) F.toRectangleDecomposition →
          G.crossingChangeHexagonCompositeWeight C t R F =
            rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
              (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  have hp := ((G.mem_initialPentagons P).mp hP).1
  have hq := (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ).1
  let D : GridRectangleDecomposition x z := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  -- Off the diagonal, the common initial side is the only common side.
  have hone : D.HasOneCommonSide := D.hasOneCommonSide_of_mem_commonSideColumns
    (c := D.first.left)
    (by simp [D.mem_commonSideColumns, GridRectangleBetween.mem_sideColumns, hcommon]) hzx
  have hne : P.right ≠ Q.right := fun h => D.sideColumns_ne_of_hasOneCommonSide hone (by
    rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns]
    exact congrArg₂ (fun c d => ({c, d} : Finset (Fin n))) hcommon h)
  obtain ⟨hrow, hbottom⟩ := P.top_mem_cIoo_and_bottom_eq_of_left_eq_left Q.toGridRectangleBetween
    (P.left_eq.trans Q.left_eq.symm) hne hp hq
  have hdisj := Grid.disjoint_cIco_cIco_of_mem_cIoo hrow
  refine existsUnique_crossingChangeUnpairedHexagonComposite_isRecut R hX hone hp hq
    (fun F => F.toRectangleDecomposition_ne_of_notMem_cIco (fun h => ?_) (fun h => ?_))
    (initialPair_exists R P Q hP hQ hone hne)
  · exact Finset.disjoint_left.mp hdisj h (hbottom ▸ Q.turn_mem_cIco_bottom_top)
  · exact Finset.disjoint_left.mp hdisj P.turn_mem_cIco_bottom_top (hbottom ▸ h)

end TauCeti.GridDiagram
