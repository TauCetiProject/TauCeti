/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Recut
import TauCeti.Data.Finset.Basic
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Mixed.Recut

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

* `exists_crossingChangeHexagonComposite_of_terminalInitialPentagonPair`, in the namespace
  `TauCeti.GridDiagram`: a counted terminal--initial pentagon pair has the same rectangles and
  weight as a counted composite, with no off-diagonal or marking assumption.
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

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Terminal-side followed by initial-side -/

private theorem terminalInitial_squares_initial {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y) (Q : GridInitialPentagonBetween a t y z)
    (H : GridInitialHexagonBetween a C.turnRow t y z)
    (hH : H.toGridRectangleBetween = Q.toGridRectangleBetween)
    (p : Fin n × Fin n) :
    (p ∈ P.coveredSquares ∨
        p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
      p ∈ P.toGridRectangle.coveredSquares ∨ p ∈ H.crossingCoveredSquares) ∧
    (p ∈ P.coveredSquares ∧
        p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
      p ∈ P.toGridRectangle.coveredSquares ∧ p ∈ H.crossingCoveredSquares) := by
  have hbottom := Q.bottom_eq_bottom_of_pentagon P
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  have hst : t ∈ Grid.cIoo C.turnRow H.top := H.upper_mem
  have hlow : C.turnRow ∈ Grid.cIco H.bottom H.top := H.lower_mem
  rw [hH, hbottom] at hlow
  rw [hH] at hst
  rw [hbottom] at ht
  have hrect : H.toGridRectangle = Q.toGridRectangle :=
    congrArg GridRectangleBetween.toGridRectangle hH
  rcases p with ⟨c, r⟩
  by_cases ha : c = a
  · subst c
    simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_left,
      P.mk_mem_coveredSquares_left_column, Q.mk_mem_coveredSquares_right_column,
      P.mk_mem_toGridRectangle_coveredSquares_left_column, H.mem_crossingCoveredSquares,
      hrect, Q.mk_notMem_toGridRectangle_coveredSquares_left_column, C.column_ne_next,
      false_and, false_or, true_and, hbottom]
    simp only [Grid.mem_cIco, Grid.mem_cIoo] at hs ht hst hlow ⊢
    split_ifs at * <;> omega
  · by_cases hb : c = b
    · subst c
      simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_right,
        P.mk_mem_coveredSquares_right_column, Q.mk_mem_coveredSquares_left_column,
        P.mk_notMem_toGridRectangle_coveredSquares_right_column, H.mem_crossingCoveredSquares,
        hrect, Q.mk_mem_toGridRectangle_coveredSquares_right_column, C.column_ne_next.symm,
        false_and, false_or, true_and, hbottom, Finset.mem_insert]
      simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hs ht hst hlow ⊢
      split_ifs at * <;> grind
    · rw [P.mem_coveredSquares_iff_of_ne ha hb,
        Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb,
        Q.mem_coveredSquares_iff_of_ne ha hb, H.mem_crossingCoveredSquares, hrect]
      simp only [ha, hb, false_and, not_false_eq_true, and_true, or_false, and_self]

private theorem terminalInitial_squares_terminal {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y) (Q : GridInitialPentagonBetween a t y z)
    (H : GridHexagonBetween a t C.turnRow x y)
    (hH : H.toGridRectangleBetween = P.toGridRectangleBetween)
    (p : Fin n × Fin n) :
    (p ∈ P.coveredSquares ∨
        p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
      p ∈ H.crossingCoveredSquares ∨ p ∈ Q.toGridRectangle.coveredSquares) ∧
    (p ∈ P.coveredSquares ∧
        p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
      p ∈ H.crossingCoveredSquares ∧ p ∈ Q.toGridRectangle.coveredSquares) := by
  have hbottom := Q.bottom_eq_bottom_of_pentagon P
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  have hst : C.turnRow ∈ Grid.cIoo t H.top := H.upper_mem
  have hlow : t ∈ Grid.cIco H.bottom H.top := H.lower_mem
  rw [hH] at hlow hst
  rw [hbottom] at ht
  have hrect : H.toGridRectangle = P.toGridRectangle :=
    congrArg GridRectangleBetween.toGridRectangle hH
  rcases p with ⟨c, r⟩
  by_cases ha : c = a
  · subst c
    simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_left,
      P.mk_mem_coveredSquares_left_column, Q.mk_mem_coveredSquares_right_column,
      H.mem_crossingCoveredSquares, hrect, P.mk_mem_toGridRectangle_coveredSquares_left_column,
      Q.mk_notMem_toGridRectangle_coveredSquares_left_column, C.column_ne_next,
      false_and, and_false, or_false, true_and, hbottom, Finset.mem_insert]
    simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hs ht hst hlow ⊢
    split_ifs at * <;> grind
  · by_cases hb : c = b
    · subst c
      simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_right,
        P.mk_mem_coveredSquares_right_column, Q.mk_mem_coveredSquares_left_column,
        H.mem_crossingCoveredSquares, hrect,
        P.mk_notMem_toGridRectangle_coveredSquares_right_column,
        Q.mk_mem_toGridRectangle_coveredSquares_right_column, C.column_ne_next.symm,
        false_and, false_or, true_and, hbottom]
      simp only [Grid.mem_cIco, Grid.mem_cIoo] at hs ht hst hlow ⊢
      split_ifs at * <;> omega
    · rw [P.mem_coveredSquares_iff_of_ne ha hb,
        Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb,
        Q.mem_coveredSquares_iff_of_ne ha hb, H.mem_crossingCoveredSquares, hrect]
      simp only [ha, hb, false_and, not_false_eq_true, and_true, or_false, and_self]

/-- Square-multiplicity preservation for a terminal--initial pair transports countedness
and its total O-weight. -/
private theorem terminalInitial_disjoint_and_weight (R : Type*) [CommSemiring R]
    {x y z : GridState n} (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween a t y z) (S T : Finset (Fin n × Fin n))
    (h : ∀ p,
      (p ∈ P.coveredSquares ∨
          p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
        p ∈ S ∨ p ∈ T) ∧
      (p ∈ P.coveredSquares ∧
          p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
        p ∈ S ∧ p ∈ T))
    (hP : Disjoint P.coveredSquares G.XSet)
    (hQ : Disjoint Q.coveredSquares (G.swapColumns a b).XSet) :
    Disjoint S G.XSet ∧ Disjoint T G.XSet ∧
      rename (Equiv.swap a b) (G.pentagonWeight R C P) *
          (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q =
        (∏ c ∈ G.OColumnsOfSquares S, (MvPolynomial.X c : MvPolynomial (Fin n) R)) *
          ∏ c ∈ G.OColumnsOfSquares T, MvPolynomial.X c := by
  have hu : P.coveredSquares ∪
      Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding =
        S ∪ T := by
    ext p
    simpa only [Finset.mem_union] using (h p).1
  have hi : P.coveredSquares ∩
      Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding =
        S ∩ T := by
    ext p
    simpa only [Finset.mem_inter] using (h p).2
  obtain ⟨hSX, hTX, hw⟩ := G.disjoint_and_prod_OSet_eq_of_union_inter_eq
    (MvPolynomial.X (R := R)) _ _ S T hu hi hP ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hQ)
  refine ⟨hSX, hTX, ?_⟩
  rw [G.rename_pentagonWeight, swapColumns_initialPentagonWeight_withTurnRow R]
  simpa only [G.prod_ite_OSet_eq_prod_OColumnsOfSquares] using hw

/-- For distinct turn rows, a counted terminal-side pentagon followed by a counted initial-side
reverse pentagon has a counted crossing-change hexagon composite with the same underlying
rectangles and polynomial weight. The two turn rows may be in either cyclic order, and no
interleaving or marking-position assumption is needed. -/
theorem exists_crossingChangeHexagonComposite_of_terminalInitialPentagonPair
    (R : Type*) [CommSemiring R] {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y) (Q : GridInitialPentagonBetween a t y z)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y z)
    (hst : C.turnRow ≠ t) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          rename (Equiv.swap a b) (G.pentagonWeight R C P) *
            (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ :=
    ((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp hQ
  have hbottom := Q.bottom_eq_bottom_of_pentagon P
  have ht : t ∈ Grid.cIco P.bottom Q.top := by
    rw [← hbottom]
    exact Q.turn_mem_cIco_bottom_top
  -- Compare both turns from the shared bottom row; the farther turn selects the hexagon.
  rcases Grid.mem_cIco_and_mem_cIoo_or_mem_cIco_and_mem_cIoo_of_ne
      P.turn_mem_cIco_bottom_top ht hst with hturn | hturn
  · have hturnQ : C.turnRow ∈ Grid.cIco Q.bottom Q.top := by
      rw [hbottom]
      exact hturn.1
    let H : GridInitialHexagonBetween a C.turnRow t y z :=
      ⟨Q.toGridRectangleBetween, Q.left_eq, hturnQ, hturn.2⟩
    have hH : H.toGridRectangleBetween = Q.toGridRectangleBetween := rfl
    obtain ⟨hPX, hHX, hw⟩ := terminalInitial_disjoint_and_weight G C t R P Q
      P.toGridRectangle.coveredSquares H.crossingCoveredSquares
      (terminalInitial_squares_initial C t P Q H hH) hpX hqX
    obtain ⟨F, hF, hFD, hFw⟩ := exists_inr_mem_crossingChangeHexagonCompositeDecompositions R
      (E := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩) (.inr H)
      (GridCommutationHexagonBetween.toGridRectangleBetween_inr H) hp hq hPX
      (by rwa [GridCommutationHexagonBetween.crossingCoveredSquares_inr])
    refine ⟨F, hF, hFD, hFw.trans ?_⟩
    simpa only [crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
      GridCommutationHexagonBetween.crossingCoveredSquares_inr,
      OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares] using hw.symm
  · let H : GridHexagonBetween a t C.turnRow x y :=
      ⟨P.toGridRectangleBetween, P.right_eq, hturn.1, hturn.2⟩
    have hH : H.toGridRectangleBetween = P.toGridRectangleBetween := rfl
    obtain ⟨hHX, hQX, hw⟩ := terminalInitial_disjoint_and_weight G C t R P Q
      H.crossingCoveredSquares Q.toGridRectangle.coveredSquares
      (terminalInitial_squares_terminal C t P Q H hH) hpX hqX
    obtain ⟨F, hF, hFD, hFw⟩ := exists_inl_mem_crossingChangeHexagonCompositeDecompositions R
      (E := ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩) (.inl H)
      (GridCommutationHexagonBetween.toGridRectangleBetween_inl H) hp hq
      (by rwa [GridCommutationHexagonBetween.crossingCoveredSquares_inl]) hQX
    refine ⟨F, hF, hFD, hFw.trans ?_⟩
    simpa only [crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
      GridCommutationHexagonBetween.crossingCoveredSquares_inl,
      OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares] using hw.symm

/-! ### Comparing the squares of two pairs of domains -/

variable {G C t}

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
  have hbottom := Q.bottom_eq_bottom_of_pentagon P
  have ht : t ∈ Grid.cIco P.bottom Q.top := hbottom ▸ Q.turn_mem_cIco_bottom_top
  obtain ⟨F, hF, hFD, hFw⟩ :=
    exists_crossingChangeHexagonComposite_of_terminalInitialPentagonPair G C t R P Q hP hQ hst
  rw [← hFw]
  exact existsUnique_crossingChangeUnpairedHexagonComposite_of_toRectangleDecomposition_eq R hX
    (GridRectangleDecomposition.hasOneCommonSide_of_right_eq_left_of_ne
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
      (P.right_eq.trans Q.left_eq.symm) hzx) hp hq
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
