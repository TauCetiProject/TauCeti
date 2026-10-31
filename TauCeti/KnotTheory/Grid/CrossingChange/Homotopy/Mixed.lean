/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Decomposition
import TauCeti.Data.Finset.Basic

/-!
# Terminal--initial pentagon pairs for a crossing change

A terminal-side pentagon followed by an initial-side pentagon for the reverse column turn
shares a bottom row. The rectangle of the pentagon whose turn is farther from that row
supports a crossing-change hexagon; the other rectangle is an ordinary differential term.
The resulting composite has the same underlying rectangles and the same polynomial weight.

Unlike commutation hexagons, crossing-change hexagons retain the bigons containing markings.
Consequently the matching preserves the multiplicity of every square, without assumptions
on the positions of the markings. In particular it preserves both X-avoidance and O-weights.
This supplies the terminal--initial part of the matching in the crossing-change homotopy
equation; it does not assert that the matching exhausts all composites.

## References

P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, Section 6.1;
M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
The choice of the hexagon-bearing rectangle parallels the commutation construction in
`TauCeti.KnotTheory.Grid.Commutation.Homotopy.Mixed.Pair`.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

private theorem terminalInitial_bottom_eq {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y) (Q : GridInitialPentagonBetween a t y z) :
    Q.bottom = P.bottom := by
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.bottom_def, Q.left_eq,
    ← P.right_eq, P.map_right]

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
  have hbottom := terminalInitial_bottom_eq C t P Q
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
  have hbottom := terminalInitial_bottom_eq C t P Q
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
  have hQ' := (G.disjoint_map_swapColumns_XSet_iff a b _).mpr hQ
  have hX : Disjoint (P.coveredSquares ∪
      Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet :=
    Finset.disjoint_union_left.mpr ⟨hP, hQ'⟩
  have hu : P.coveredSquares ∪
      Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding =
        S ∪ T := by
    ext p
    simpa only [Finset.mem_union] using (h p).1
  rw [hu, Finset.disjoint_union_left] at hX
  refine ⟨hX.1, hX.2, ?_⟩
  have hQw : (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q =
      ∏ p ∈ Q.coveredSquares.map
          ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding,
        if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R) := by
    rw [initialPentagonWeight_eq_prod_coveredSquares, Finset.prod_map]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp
  rw [G.rename_pentagonWeight, hQw]
  simp_rw [G.prod_ite_OSet_eq_prod_OColumnsOfSquares]
  have hu' : G.OColumnsOfSquares P.coveredSquares ∪
      G.OColumnsOfSquares (Q.coveredSquares.map
        ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) =
      G.OColumnsOfSquares S ∪ G.OColumnsOfSquares T := by
    ext c
    simp only [Finset.mem_union, mem_OColumnsOfSquares]
    exact (h _).1
  have hi' : G.OColumnsOfSquares P.coveredSquares ∩
      G.OColumnsOfSquares (Q.coveredSquares.map
        ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) =
      G.OColumnsOfSquares S ∩ G.OColumnsOfSquares T := by
    ext c
    simp only [Finset.mem_inter, mem_OColumnsOfSquares]
    exact (h _).2
  rw [← Finset.prod_union_inter, hu', hi', Finset.prod_union_inter]

/-- A counted terminal-side pentagon followed by a counted initial-side reverse pentagon
has a counted crossing-change hexagon composite with the same underlying rectangles and
polynomial weight. The two turn rows may be in either cyclic order, and no interleaving or
marking-position assumption is needed. -/
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
  have hbottom := terminalInitial_bottom_eq C t P Q
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
    refine ⟨.inr ⟨y, P.toGridRectangleBetween, .inr H⟩, ?_, ?_, ?_⟩
    · simp only [inr_mem_crossingChangeHexagonCompositeDecompositions,
        mem_crossingChangeRectangleHexagonDecompositions, mem_unblockedRectangles,
        GridRectangleHexagonDecomposition.hexagon, GridRectangleHexagonDecomposition.rectangle,
        mem_crossingChangeCommutationHexagons,
        GridCommutationHexagonBetween.toGridRectangleBetween_inr,
        GridCommutationHexagonBetween.crossingCoveredSquares_inr]
      exact ⟨⟨hp, hPX⟩, by simpa only [hH] using hq, hHX⟩
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        GridRectangleHexagonDecomposition.toRectangleDecomposition,
        GridCommutationHexagonBetween.toGridRectangleBetween_inr, hH]
    · simpa only [crossingChangeHexagonCompositeWeight_inr,
        crossingChangeRectangleHexagonWeight_def,
        GridRectangleHexagonDecomposition.hexagon, GridRectangleHexagonDecomposition.rectangle,
        crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
        GridCommutationHexagonBetween.crossingCoveredSquares_inr,
        OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares] using hw.symm
  · let H : GridHexagonBetween a t C.turnRow x y :=
      ⟨P.toGridRectangleBetween, P.right_eq, hturn.1, hturn.2⟩
    have hH : H.toGridRectangleBetween = P.toGridRectangleBetween := rfl
    obtain ⟨hHX, hQX, hw⟩ := terminalInitial_disjoint_and_weight G C t R P Q
      H.crossingCoveredSquares Q.toGridRectangle.coveredSquares
      (terminalInitial_squares_terminal C t P Q H hH) hpX hqX
    refine ⟨.inl ⟨y, .inl H, Q.toGridRectangleBetween⟩, ?_, ?_, ?_⟩
    · simp only [inl_mem_crossingChangeHexagonCompositeDecompositions,
        mem_crossingChangeHexagonRectangleDecompositions, mem_unblockedRectangles,
        GridHexagonRectangleDecomposition.hexagon, GridHexagonRectangleDecomposition.rectangle,
        mem_crossingChangeCommutationHexagons,
        GridCommutationHexagonBetween.toGridRectangleBetween_inl,
        GridCommutationHexagonBetween.crossingCoveredSquares_inl]
      exact ⟨⟨by simpa only [hH] using hp, hHX⟩, hq, hQX⟩
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        GridHexagonRectangleDecomposition.toRectangleDecomposition,
        GridCommutationHexagonBetween.toGridRectangleBetween_inl, hH]
    · simpa only [crossingChangeHexagonCompositeWeight_inl,
        crossingChangeHexagonRectangleWeight_def,
        GridHexagonRectangleDecomposition.hexagon, GridHexagonRectangleDecomposition.rectangle,
        crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
        GridCommutationHexagonBetween.crossingCoveredSquares_inl,
        OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares] using hw.symm

end TauCeti.GridDiagram
