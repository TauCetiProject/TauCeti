/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Decomposition
import TauCeti.Data.Finset.Basic

/-!
# Initial--terminal pentagon pairs in the crossing-change homotopy

An initial-side pentagon followed by a terminal-side pentagon at the other turn point
has the same domain as a crossing-change hexagon and an ordinary rectangle. Their common
corner is on the top row. The order of the turn points below that row determines which
rectangle underlies the hexagon.

The matching preserves both the union and the intersection of the covered-square sets,
after reading the second pentagon in the original diagram. Thus it preserves multiplicities,
not just support: the composite avoids the `X`-markings and has exactly the polynomial
weight of the pentagon pair. These are the initial--terminal contributions to the
crossing-change homotopy equation. No placement assumption on the markings is needed.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 6.1.
* Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.

The hexagon selection follows the initial--terminal commutation argument in
`TauCeti.KnotTheory.Grid.Commutation.Homotopy.Mixed.Pair`; here the crossing-change
squares retain the bigons, so square identities replace the commutation marking estimates.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "σ" => Equiv.toEmbedding
  (Equiv.prodCongr (Equiv.swap C.column (finRotate n C.column)) (Equiv.refl (Fin n)))

private noncomputable def firstCrossingSquares {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) : Finset (Fin n × Fin n) :=
  F.elim (fun D => D.hexagon.crossingCoveredSquares)
    (fun D => D.rectangle.toGridRectangle.coveredSquares)

private noncomputable def secondCrossingSquares {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) : Finset (Fin n × Fin n) :=
  F.elim (fun D => D.rectangle.toGridRectangle.coveredSquares)
    (fun D => D.hexagon.crossingCoveredSquares)

section Geometry

variable {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridPentagonBetween C.column t y z)

private theorem initialTerminal_top : Q.top = P.top := by
  rw [GridRectangleBetween.top_def, GridRectangleBetween.top_def, Q.right_eq,
    ← P.left_eq, P.map_left]

/-- The reverse pentagon's square memberships, read in the original diagram. -/
private theorem initialTerminal_reverse_squares :
    (∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b →
      (p ∈ Q.coveredSquares.map σ ↔ p ∈ Q.toGridRectangle.coveredSquares)) ∧
    ∀ r : Fin n,
      ((a, r) ∈ Q.coveredSquares.map σ ↔ r ∈ Grid.cIco Q.bottom t) ∧
      ((b, r) ∈ Q.coveredSquares.map σ ↔ r ∈ Grid.cIoo t Q.top) := by
  refine ⟨fun p ha hb => (Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb).trans
    (Q.mem_coveredSquares_iff_of_ne ha hb), fun r => ?_⟩
  simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Q.mk_mem_coveredSquares_left_column,
    Q.mk_mem_coveredSquares_right_column, and_self]

/-- On a column with overlapping pentagon arcs, recutting preserves both multiplicities. -/
private theorem initialTerminal_recut_column {u v : GridState n}
    (D : GridRectangleBetween u v) {S₁ S₂ : Finset (Fin n × Fin n)}
    {p : Fin n × Fin n} {B s t : Fin n}
    (ht : t ∈ Grid.cIco B D.top) (hst : t ∈ Grid.cIoo s D.top)
    (hP : p ∈ S₁ ↔ p.2 ∈ Grid.cIoo s D.top)
    (hQ : p ∈ S₂ ↔ p.2 ∈ Grid.cIco B t)
    (hrect : p ∈ D.toGridRectangle.coveredSquares ↔ p.2 ∈ Grid.cIco B D.top) :
    (p ∈ S₁ ∨ p ∈ S₂ ↔ p.2 ∈ Grid.cIoo s t ∨ p ∈ D.toGridRectangle.coveredSquares) ∧
      (p ∈ S₁ ∧ p ∈ S₂ ↔ p.2 ∈ Grid.cIoo s t ∧ p ∈ D.toGridRectangle.coveredSquares) := by
  have hu := Finset.ext_iff.mp (Grid.cIoo_union_cIco_eq_union_of_mem_cIoo ht hst) p.2
  have hi := Finset.ext_iff.mp (Grid.cIoo_inter_cIco_eq_inter_of_mem_cIoo ht hst) p.2
  simp only [Finset.mem_union, Finset.mem_inter] at hu hi
  grind only

/-- On the other column, deleting the closed turn arc leaves disjoint pentagon arcs. -/
private theorem initialTerminal_cut_column {u v : GridState n}
    (D : GridRectangleBetween u v) {S₁ S₂ : Finset (Fin n × Fin n)}
    {p : Fin n × Fin n} {s t : Fin n}
    (hs : s ∈ Grid.cIco D.bottom D.top) (hst : t ∈ Grid.cIoo s D.top)
    (hP : p ∈ S₁ ↔ p.2 ∈ Grid.cIco D.bottom s)
    (hQ : p ∈ S₂ ↔ p.2 ∈ Grid.cIoo t D.top)
    (hrect : p ∈ D.toGridRectangle.coveredSquares ↔
      p.2 ∈ Grid.cIco D.bottom D.top) :
    (p ∈ S₁ ∨ p ∈ S₂ ↔ p ∈ D.toGridRectangle.coveredSquares ∧
      p.2 ∉ insert t (Grid.cIco s t)) ∧ ¬(p ∈ S₁ ∧ p ∈ S₂) := by
  have hu := Finset.ext_iff.mp (Grid.cIco_union_cIoo_eq_sdiff_of_mem_cIoo hs hst) p.2
  have hd : p.2 ∈ Grid.cIco D.bottom s → p.2 ∉ Grid.cIoo t D.top :=
    fun hr => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIoo_of_mem_cIoo hs hst) hr
  simp only [Finset.mem_union, Finset.mem_sdiff] at hu
  grind only

/-- The two cyclic turn orders give a hexagon composite with the same square multiplicities. -/
private theorem exists_initialTerminal_square_match (hst : C.turnRow ≠ t) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
      P.coveredSquares ∪ Q.coveredSquares.map σ =
        firstCrossingSquares C t F ∪ secondCrossingSquares C t F ∧
      P.coveredSquares ∩ Q.coveredSquares.map σ =
        firstCrossingSquares C t F ∩ secondCrossingSquares C t F := by
  have htop := initialTerminal_top C t P Q
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  have ht' : t ∈ Grid.cIco Q.bottom P.top := by rwa [htop] at ht
  obtain ⟨hoff, hcol⟩ := initialTerminal_reverse_squares C t Q
  -- The cyclic order selects the hexagon-bearing rectangle. In each branch, check the
  -- two adjacent columns explicitly; every other column retains its rectangle squares.
  rcases Grid.mem_cIoo_or_mem_cIoo_of_ne hs ht' hst with hturn | hturn
  · let H : GridInitialHexagonBetween a C.turnRow t x y :=
      ⟨P.toGridRectangleBetween, P.left_eq, hs, hturn⟩
    let F : GridHexagonCompositeDecomposition a C.turnRow t x z := .inl ⟨y, .inr H,
      Q.toGridRectangleBetween⟩
    refine ⟨F, by simp [F, GridHexagonRectangleDecomposition.toRectangleDecomposition, H], ?_, ?_⟩
    all_goals
      ext ⟨c, r⟩
      have hrecut := initialTerminal_recut_column Q.toGridRectangleBetween ht
        (by simpa only [htop] using hturn)
        (by simpa only [htop] using P.mk_mem_coveredSquares_left_column r)
        (hcol r).1 (Q.mk_mem_toGridRectangle_coveredSquares_left_column r)
      have hcut := initialTerminal_cut_column P.toGridRectangleBetween hs hturn
        (P.mk_mem_coveredSquares_right_column r)
        (by simpa only [htop] using (hcol r).2)
        (P.mk_mem_toGridRectangle_coveredSquares_right_column r)
      have hPa := P.mk_notMem_toGridRectangle_coveredSquares_left_column r
      have hQb := Q.mk_notMem_toGridRectangle_coveredSquares_right_column r
      have hab := C.column_ne_next
      simp only [firstCrossingSquares, secondCrossingSquares, F,
        GridHexagonRectangleDecomposition.hexagon, GridHexagonRectangleDecomposition.rectangle,
        Sum.elim_inl, GridCommutationHexagonBetween.crossingCoveredSquares_inr,
        Finset.mem_union, Finset.mem_inter, GridInitialHexagonBetween.mem_crossingCoveredSquares]
      dsimp only [H]
      by_cases ha : c = a <;> by_cases hb : c = b <;>
        grind only [P.mem_coveredSquares_iff_of_ne]
  -- In the other turn order the second rectangle, rather than the first, bears the hexagon.
  · have hturnQ : C.turnRow ∈ Grid.cIoo t Q.top := by rwa [htop]
    let H : GridHexagonBetween a t C.turnRow y z :=
      ⟨Q.toGridRectangleBetween, Q.right_eq, ht, hturnQ⟩
    let F : GridHexagonCompositeDecomposition a C.turnRow t x z := .inr ⟨y,
      P.toGridRectangleBetween, .inl H⟩
    refine ⟨F, by simp [F, GridRectangleHexagonDecomposition.toRectangleDecomposition, H], ?_, ?_⟩
    all_goals
      ext ⟨c, r⟩
      have hcut := initialTerminal_cut_column Q.toGridRectangleBetween ht hturnQ
        (hcol r).1 (by simpa only [htop] using P.mk_mem_coveredSquares_left_column r)
        (Q.mk_mem_toGridRectangle_coveredSquares_left_column r)
      have hrecut := initialTerminal_recut_column P.toGridRectangleBetween hs hturn
        (by simpa only [htop] using (hcol r).2) (P.mk_mem_coveredSquares_right_column r)
        (P.mk_mem_toGridRectangle_coveredSquares_right_column r)
      have hPa := P.mk_notMem_toGridRectangle_coveredSquares_left_column r
      have hQb := Q.mk_notMem_toGridRectangle_coveredSquares_right_column r
      have hab := C.column_ne_next
      simp only [firstCrossingSquares, secondCrossingSquares, F,
        GridRectangleHexagonDecomposition.hexagon, GridRectangleHexagonDecomposition.rectangle,
        Sum.elim_inr, GridCommutationHexagonBetween.crossingCoveredSquares_inl,
        Finset.mem_union, Finset.mem_inter, GridHexagonBetween.mem_crossingCoveredSquares]
      dsimp only [H]
      by_cases ha : c = a <;> by_cases hb : c = b <;>
        grind only [P.mem_coveredSquares_iff_of_ne]

end Geometry

variable (R : Type*) [CommSemiring R]

/-- A square match transfers marking avoidance, emptiness, and the product weight. -/
private theorem initialTerminal_counted_match {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridPentagonBetween C.column t y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z)
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z)
    (hFD : F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩)
    (hu : P.coveredSquares ∪ Q.coveredSquares.map σ =
      firstCrossingSquares C t F ∪ secondCrossingSquares C t F)
    (hi : P.coveredSquares ∩ Q.coveredSquares.map σ =
      firstCrossingSquares C t F ∩ secondCrossingSquares C t F) :
    F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
      G.crossingChangeHexagonCompositeWeight C t R F =
        MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
          (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp hQ
  -- Union equality transfers avoidance; union and intersection together transfer multiplicities.
  have hX : Disjoint (firstCrossingSquares C t F) G.XSet ∧
      Disjoint (secondCrossingSquares C t F) G.XSet := by
    rw [← Finset.disjoint_union_left, ← hu, Finset.disjoint_union_left]
    exact ⟨hpX, (G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX⟩
  have hempty : F.toRectangleDecomposition.first.IsEmpty ∧
      F.toRectangleDecomposition.second.IsEmpty := by rw [hFD]; exact ⟨hp, hq⟩
  have hweight :
      (∏ p ∈ firstCrossingSquares C t F,
          if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
        (∏ p ∈ secondCrossingSquares C t F,
          if p ∈ G.OSet then MvPolynomial.X p.1 else 1) =
      (∏ p ∈ P.coveredSquares,
          if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
        (∏ p ∈ Q.coveredSquares.map σ,
          if p ∈ G.OSet then MvPolynomial.X p.1 else 1) := by
    rw [← Finset.prod_union_inter (s₁ := firstCrossingSquares C t F),
      ← Finset.prod_union_inter (s₁ := P.coveredSquares), hu, hi]
  rw [G.rename_initialPentagonWeight, pentagonWeight_withTurnRow,
    ← G.prod_ite_OSet_eq_prod_OColumnsOfSquares]
  refine ⟨?_, ?_⟩
  · cases F with
    | inl F =>
      have hempty : F.hexagon.toGridRectangleBetween.IsEmpty ∧ F.rectangle.IsEmpty := by
        exact (congrArg (fun D : GridRectangleDecomposition x z =>
          D.first.IsEmpty ∧ D.second.IsEmpty)
          (GridHexagonCompositeDecomposition.toRectangleDecomposition_inl F)).mp hempty
      exact (G.inl_mem_crossingChangeHexagonCompositeDecompositions C t F).mpr
        ((G.mem_crossingChangeHexagonRectangleDecompositions C t F).mpr
          ⟨(G.mem_crossingChangeCommutationHexagons C t F.hexagon).mpr ⟨hempty.1, hX.1⟩,
            (G.mem_unblockedRectangles F.rectangle).mpr ⟨hempty.2, hX.2⟩⟩)
    | inr F =>
      have hempty : F.rectangle.IsEmpty ∧ F.hexagon.toGridRectangleBetween.IsEmpty := by
        exact (congrArg (fun D : GridRectangleDecomposition x z =>
          D.first.IsEmpty ∧ D.second.IsEmpty)
          (GridHexagonCompositeDecomposition.toRectangleDecomposition_inr F)).mp hempty
      exact (G.inr_mem_crossingChangeHexagonCompositeDecompositions C t F).mpr
        ((G.mem_crossingChangeRectangleHexagonDecompositions C t F).mpr
          ⟨(G.mem_unblockedRectangles F.rectangle).mpr ⟨hempty.1, hX.1⟩,
            (G.mem_crossingChangeCommutationHexagons C t F.hexagon).mpr ⟨hempty.2, hX.2⟩⟩)
  · cases F <;>
      simpa only [crossingChangeHexagonCompositeWeight_inl,
        crossingChangeHexagonCompositeWeight_inr, crossingChangeHexagonRectangleWeight_def,
        crossingChangeRectangleHexagonWeight_def, OMonomial_eq_prod_coveredSquares,
        crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
        ← prod_ite_OSet_eq_prod_OColumnsOfSquares, firstCrossingSquares, secondCrossingSquares,
        Sum.elim_inl, Sum.elim_inr] using hweight

/-- Every counted initial-side pentagon followed by a terminal-side pentagon at a distinct
turn row matches a counted crossing-change hexagon composite with the same underlying
rectangles and polynomial weight, over every commutative coefficient semiring.
No interleaving or knot hypothesis is needed. -/
theorem exists_crossingChangeHexagonComposite_of_initialTerminalPentagonPair
    (hst : C.turnRow ≠ t) {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridPentagonBetween C.column t y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y z) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
            (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q := by
  obtain ⟨F, hFD, hu, hi⟩ := exists_initialTerminal_square_match C t P Q hst
  obtain ⟨hF, hw⟩ := initialTerminal_counted_match G C t R P Q hP hQ F hFD hu hi
  exact ⟨F, hF, hFD, hw⟩

end TauCeti.GridDiagram
