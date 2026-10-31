/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Disjoint
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Cancellation

/-!
# Recut pairing in the crossing change homotopy equation

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row. The left-hand side `∂ ∘ H + H ∘ ∂` of the crossing change
homotopy equation counts two-step domains made of a crossing-change hexagon and a rectangle of
`G`, in either order. Both orders are treated as one family of composites
(`TauCeti.GridHexagonCompositeDecomposition`), as for the commutation homotopy. When the two
rectangles of a composite share exactly one side column, their union is an L-shaped domain and the
recut from the proof of `∂² = 0` cuts it the other way
(`TauCeti.GridRectangleDecomposition.recut`). If the recut of a counted composite underlies a
counted composite again, the two terms cancel in characteristic two.

The weights agree when the annulus squares `GridDiagram.crossingChangeAnnulusSquares` carry no
`X`-marking, as they do for the crossing change maps of interleaving columns. Then a hexagon
cutting from `t` up to `s` cuts away the `X`-marking of column `a`, and one cutting from `s` up to
`t` that of column `b`; so the rectangle under a counted hexagon carries exactly one `X`-marking,
in the column the hexagon cuts away (`TauCeti.GridCommutationHexagonBetween.cutColumn`), while a
counted rectangle carries none. Two
composites with the same union therefore carry the same single `X`-marking, so their hexagons
have the same shape. The weight of a hexagon differs from that of its rectangle by the
`O`-markings in the squares it cuts away and in those it adds, which depend only on its shape, so
the two composites have the same weight. The position of the `X`-marking also determines which
rectangle of a composite underlies its hexagon, so recut partners form a fixed-point-free
involution.

Off the diagonal, what remains of the left-hand side are the counted composites whose recut is
not again a counted composite (`TauCeti.GridDiagram.crossingChangeUnpairedHexagonComposites`).
They are to be matched with the pairs of pentagons counted by `Ψ ∘ Φ`; that matching is not part
of this file.

## Main definition

* `TauCeti.GridDiagram.crossingChangeUnpairedHexagonComposites`: the counted composites sharing a
  side column whose recut underlies no counted composite.

## Main results

* `TauCeti.GridDiagram.crossingChangeHexagonCompositeWeight_eq_of_isRepartition`: two counted
  composites repartitioning the same squares have the same weight.
* `TauCeti.GridDiagram.injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions`:
  a counted composite is determined by its underlying rectangle decomposition.
* `TauCeti.GridDiagram.mem_crossingChangeUnpairedHexagonComposites_of_toRectangleDecomposition_eq`:
  a counted composite is unpaired as soon as the canonical recut of its underlying decomposition
  underlies no counted composite.
* `TauCeti.GridDiagram.sum_crossingChangeHexagonCompositeWeight_overlap_eq_sum_unpaired`: in
  characteristic two, the overlapping composites have the total weight of the unpaired ones.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired`: the
  equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ`, with `w` the annulus weight, is equivalent to the identity
  between the unpaired composites and the pentagon coefficient products off the diagonal. Its
  versions `_of_mem_columnArc` and `_of_notMem_columnArc` treat the crossing change maps of
  interleaving columns, with `w = V_b`, respectively `w = V_a`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the juxtaposition argument for the hexagon
  homotopies of commutation and of a crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti

namespace GridCommutationHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- The squares of the underlying rectangle that a crossing-change hexagon leaves out: those of the
column it cuts away, in the rows from its lower corner up to its upper one. -/
private noncomputable def crossingCutSquares (P : GridCommutationHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  P.elim (fun _ => {a} ×ˢ insert s (Grid.cIco s' s))
    fun _ => {finRotate n a} ×ˢ insert s' (Grid.cIco s s')

/-- The squares outside the underlying rectangle that a crossing-change hexagon covers: those of
the column across the replaced grid line, strictly between its two corners. -/
private noncomputable def crossingAddedSquares (P : GridCommutationHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  P.elim (fun _ => {finRotate n a} ×ˢ Grid.cIoo s' s) fun _ => {a} ×ˢ Grid.cIoo s s'

/-- A crossing-change hexagon covers the squares of its rectangle except those it cuts away,
together with the squares it adds. -/
private theorem crossingCoveredSquares_eq_sdiff_union
    (P : GridCommutationHexagonBetween a s s' x y) :
    P.crossingCoveredSquares =
      P.toGridRectangleBetween.toGridRectangle.coveredSquares \ P.crossingCutSquares ∪
        P.crossingAddedSquares := by
  ext p
  cases P with
  | inl P =>
    simp only [crossingCoveredSquares_inl, GridHexagonBetween.mem_crossingCoveredSquares,
      crossingCutSquares, crossingAddedSquares, Sum.elim_inl, toGridRectangleBetween_inl,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_product, Finset.mem_singleton]
  | inr P =>
    simp only [crossingCoveredSquares_inr, GridInitialHexagonBetween.mem_crossingCoveredSquares,
      crossingCutSquares, crossingAddedSquares, Sum.elim_inr, toGridRectangleBetween_inr,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_product, Finset.mem_singleton]

/-- The squares a crossing-change hexagon cuts away lie in its underlying rectangle. -/
private theorem crossingCutSquares_subset (P : GridCommutationHexagonBetween a s s' x y) :
    P.crossingCutSquares ⊆ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
  intro p hp
  cases P with
  | inl P =>
    simp only [crossingCutSquares, Sum.elim_inl, Finset.mem_product, Finset.mem_singleton] at hp
    rw [toGridRectangleBetween_inl, P.mem_toGridRectangle_coveredSquares, hp.1]
    exact ⟨Grid.self_mem_cIco_finRotate P.left_ne, P.insert_cIco_subset_cIco_bottom_top hp.2⟩
  | inr P =>
    simp only [crossingCutSquares, Sum.elim_inr, Finset.mem_product, Finset.mem_singleton] at hp
    rw [toGridRectangleBetween_inr, P.mem_toGridRectangle_coveredSquares, hp.1]
    exact ⟨Grid.left_mem_cIco P.right_ne.symm, P.insert_cIco_subset_cIco_bottom_top hp.2⟩

/-- The squares a crossing-change hexagon adds lie outside its underlying rectangle. -/
private theorem disjoint_crossingAddedSquares (P : GridCommutationHexagonBetween a s s' x y) :
    Disjoint P.toGridRectangleBetween.toGridRectangle.coveredSquares P.crossingAddedSquares := by
  rw [Finset.disjoint_right]
  intro p hp hr
  cases P with
  | inl P =>
    simp only [crossingAddedSquares, Sum.elim_inl, Finset.mem_product,
      Finset.mem_singleton] at hp
    rw [toGridRectangleBetween_inl, P.mem_toGridRectangle_coveredSquares, hp.1] at hr
    exact Grid.right_notMem_cIco _ _ hr.1
  | inr P =>
    simp only [crossingAddedSquares, Sum.elim_inr, Finset.mem_product,
      Finset.mem_singleton] at hp
    rw [toGridRectangleBetween_inr, P.mem_toGridRectangle_coveredSquares, hp.1] at hr
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hr.1
      (Grid.self_mem_cIco_finRotate P.right_ne)

/-- For distinct adjacent columns, two crossing-change hexagons with the same cut column cut away
the same squares and add the same squares. -/
private theorem crossingCutSquares_eq_and_crossingAddedSquares_eq {u v : GridState n}
    (hab : a ≠ finRotate n a) (P : GridCommutationHexagonBetween a s s' x y)
    (Q : GridCommutationHexagonBetween a s s' u v) (h : P.cutColumn = Q.cutColumn) :
    P.crossingCutSquares = Q.crossingCutSquares ∧
      P.crossingAddedSquares = Q.crossingAddedSquares := by
  cases P <;> cases Q <;> simp_all [crossingCutSquares, crossingAddedSquares]

end GridCommutationHexagonBetween

namespace GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### The markings of a counted hexagon -/

section Markings

variable {G C t}

/-- If the annulus squares carry no `X`-marking, the `X`-marking of column `a` lies in the rows
from `t` up to the turn row. -/
private theorem X_column_mem_insert_cIco (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) :
    G.X a ∈ insert C.turnRow (Grid.cIco t C.turnRow) := by
  rw [Grid.mem_insert_cIco_iff_notMem_cIoo hst.symm]
  exact fun h => Finset.disjoint_left.mp hX
    ((mem_crossingChangeAnnulusSquares C t _).mpr (Or.inl ⟨rfl, h⟩)) ((G.mk_mem_XSet _ _).mpr rfl)

/-- If the annulus squares carry no `X`-marking, the `X`-marking of column `b` lies in the rows
from the turn row up to `t`. -/
private theorem X_next_mem_insert_cIco (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) :
    G.X b ∈ insert t (Grid.cIco C.turnRow t) := by
  rw [Grid.mem_insert_cIco_iff_notMem_cIoo hst]
  exact fun h => Finset.disjoint_left.mp hX
    ((mem_crossingChangeAnnulusSquares C t _).mpr (Or.inr ⟨rfl, h⟩)) ((G.mk_mem_XSet _ _).mpr rfl)

/-- If the annulus squares carry no `X`-marking, then the rectangle under a counted
crossing-change hexagon carries exactly one `X`-marking, that of the column the hexagon cuts
away. -/
theorem XSet_inter_coveredSquares_of_mem_crossingChangeCommutationHexagons
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x y : GridState n} {P : GridCommutationHexagonBetween a C.turnRow t x y}
    (hP : P ∈ G.crossingChangeCommutationHexagons C t x y) :
    G.XSet ∩ P.toGridRectangleBetween.toGridRectangle.coveredSquares =
      {(P.cutColumn, G.X P.cutColumn)} := by
  have hK := ((G.mem_crossingChangeCommutationHexagons C t P).mp hP).2
  have hst := P.ne
  cases P with
  | inl P =>
    rw [GridCommutationHexagonBetween.crossingCoveredSquares_inl] at hK
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inl,
      GridCommutationHexagonBetween.cutColumn_inl]
    exact XSet_inter_eq_of_hexagon (X_column_mem_insert_cIco hst hX) hK
  | inr P =>
    rw [GridCommutationHexagonBetween.crossingCoveredSquares_inr] at hK
    rw [GridCommutationHexagonBetween.toGridRectangleBetween_inr,
      GridCommutationHexagonBetween.cutColumn_inr]
    exact XSet_inter_eq_of_initialHexagon (X_next_mem_insert_cIco hst hX) hK

end Markings

variable (R : Type*) [CommSemiring R]

/-- The weight of a crossing-change hexagon times the `O`-weight of the squares it cuts away is
the weight of its rectangle times the `O`-weight of the squares it adds. -/
private theorem crossingChangeCommutationHexagonWeight_mul_prod {x y : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow t x y) :
    G.crossingChangeCommutationHexagonWeight C t R P *
        ∏ p ∈ P.crossingCutSquares, (if p ∈ G.OSet then MvPolynomial.X p.1 else 1) =
      G.OMonomial R P.toGridRectangleBetween.toGridRectangle *
        ∏ p ∈ P.crossingAddedSquares, (if p ∈ G.OSet then MvPolynomial.X p.1 else 1) := by
  rw [crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares,
    ← G.prod_ite_OSet_eq_prod_OColumnsOfSquares,
    GridCommutationHexagonBetween.crossingCoveredSquares_eq_sdiff_union,
    Finset.prod_union (P.disjoint_crossingAddedSquares.mono_left Finset.sdiff_subset),
    OMonomial_eq_prod_coveredSquares, ← Finset.prod_sdiff P.crossingCutSquares_subset]
  ring

open scoped Classical in
/-- The overlapping counted composites have the total weight of the overlapping
hexagon--rectangle and rectangle--hexagon decompositions. -/
theorem sum_crossingChangeHexagonCompositeWeight_filter_not_hasDisjointSides
    (x z : GridState n) :
    ∑ D ∈ (G.crossingChangeHexagonCompositeDecompositions C t x z).filter
        (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeHexagonCompositeWeight C t R D =
      (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.crossingChangeHexagonRectangleWeight C t R D) +
        ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.crossingChangeRectangleHexagonWeight C t R D := by
  simp only [Finset.sum_filter, crossingChangeHexagonCompositeDecompositions_def,
    Finset.sum_disjSum, GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
    crossingChangeHexagonCompositeWeight_inl, crossingChangeHexagonCompositeWeight_inr]

variable {G C t}

/-- The column a composite's hexagon cuts away. -/
private def compositeCutColumn {s s' : Fin n} {x z : GridState n}
    (D : GridHexagonCompositeDecomposition C.column s s' x z) : Fin n :=
  D.elim (fun D => D.hexagon.cutColumn) fun D => D.hexagon.cutColumn

/-- The squares a composite's hexagon cuts away from its rectangle. -/
private noncomputable def compositeCutSquares {s s' : Fin n} {x z : GridState n}
    (D : GridHexagonCompositeDecomposition C.column s s' x z) : Finset (Fin n × Fin n) :=
  D.elim (fun D => D.hexagon.crossingCutSquares) fun D => D.hexagon.crossingCutSquares

/-- The squares a composite's hexagon adds to its rectangle. -/
private noncomputable def compositeAddedSquares {s s' : Fin n} {x z : GridState n}
    (D : GridHexagonCompositeDecomposition C.column s s' x z) : Finset (Fin n × Fin n) :=
  D.elim (fun D => D.hexagon.crossingAddedSquares) fun D => D.hexagon.crossingAddedSquares

/-- If the annulus squares carry no `X`-marking, a counted composite
carries exactly one `X`-marking, in the column its hexagon cuts away, and its weight differs from
the product of the weights of its two rectangles by the `O`-markings its hexagon cuts away and
adds. -/
private theorem XSet_inter_and_weight_of_mem
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {D : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hD : D ∈ G.crossingChangeHexagonCompositeDecompositions C t x z) :
    G.XSet ∩ (D.toRectangleDecomposition.first.toGridRectangle.coveredSquares ∪
        D.toRectangleDecomposition.second.toGridRectangle.coveredSquares) =
        {(compositeCutColumn D, G.X (compositeCutColumn D))} ∧
      G.crossingChangeHexagonCompositeWeight C t R D *
          ∏ p ∈ compositeCutSquares D, (if p ∈ G.OSet then MvPolynomial.X p.1 else 1) =
        G.OMonomial R D.toRectangleDecomposition.first.toGridRectangle *
            G.OMonomial R D.toRectangleDecomposition.second.toGridRectangle *
          ∏ p ∈ compositeAddedSquares D, (if p ∈ G.OSet then MvPolynomial.X p.1 else 1) := by
  cases D with
  | inl D =>
    obtain ⟨hP, hr⟩ := (G.mem_crossingChangeHexagonRectangleDecompositions C t D).mp
      ((G.inl_mem_crossingChangeHexagonCompositeDecompositions C t D).mp hD)
    refine ⟨?_, ?_⟩
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        Finset.inter_union_distrib_left,
        XSet_inter_coveredSquares_of_mem_crossingChangeCommutationHexagons hX hP,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm,
        Finset.union_empty]
      simp only [compositeCutColumn, Sum.elim_inl]
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
      simp only [crossingChangeHexagonCompositeWeight_inl, crossingChangeHexagonRectangleWeight_def,
        compositeCutSquares, compositeAddedSquares, Sum.elim_inl]
      rw [mul_right_comm, crossingChangeCommutationHexagonWeight_mul_prod, mul_right_comm]
  | inr D =>
    obtain ⟨hr, hP⟩ := (G.mem_crossingChangeRectangleHexagonDecompositions C t D).mp
      ((G.inr_mem_crossingChangeHexagonCompositeDecompositions C t D).mp hD)
    refine ⟨?_, ?_⟩
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        Finset.inter_union_distrib_left,
        XSet_inter_coveredSquares_of_mem_crossingChangeCommutationHexagons hX hP,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm,
        Finset.empty_union]
      simp only [compositeCutColumn, Sum.elim_inr]
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
      simp only [crossingChangeHexagonCompositeWeight_inr, crossingChangeRectangleHexagonWeight_def,
        compositeCutSquares, compositeAddedSquares, Sum.elim_inr]
      rw [mul_assoc, crossingChangeCommutationHexagonWeight_mul_prod, mul_assoc]

/-- If the annulus squares carry no `X`-marking, two counted composites
whose underlying rectangle decompositions repartition the same squares have the same weight. -/
theorem crossingChangeHexagonCompositeWeight_eq_of_isRepartition
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {D E : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hD : D ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    (hE : E ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    (h : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition) :
    G.crossingChangeHexagonCompositeWeight C t R D =
      G.crossingChangeHexagonCompositeWeight C t R E := by
  obtain ⟨hDX, hDw⟩ := XSet_inter_and_weight_of_mem R hX hD
  obtain ⟨hEX, hEw⟩ := XSet_inter_and_weight_of_mem R hX hE
  -- Both composites cover the same squares, hence the same single `X`-marking, so their hexagons
  -- cut away the same column and have the same shape.
  rw [h.coveredSquares_union_eq, hDX, Finset.singleton_inj] at hEX
  have hcut : compositeCutSquares D = compositeCutSquares E ∧
      compositeAddedSquares D = compositeAddedSquares E := by
    have hc := (Prod.mk.inj hEX).1
    cases D <;> cases E <;>
      exact GridCommutationHexagonBetween.crossingCutSquares_eq_and_crossingAddedSquares_eq
        C.column_ne_next _ _ hc
  rw [← hcut.1, ← hcut.2, h.OMonomial_mul_OMonomial G R, ← hDw,
    G.prod_ite_OSet_eq_prod_OColumnsOfSquares] at hEw
  -- Cancel the variables of the `O`-markings both hexagons cut away.
  exact ((isRegular_prod_X _).right hEw).symm

/-- If the annulus squares carry no `X`-marking, a counted composite is
determined by its underlying rectangle decomposition, including the order of its hexagon and
rectangle. -/
theorem injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    (x z : GridState n) :
    Set.InjOn GridHexagonCompositeDecomposition.toRectangleDecomposition
      (G.crossingChangeHexagonCompositeDecompositions C t x z :
        Set (GridHexagonCompositeDecomposition a C.turnRow t x z)) := by
  -- The first rectangle covers an `X`-marking exactly when the hexagon comes first: the rectangle
  -- under the hexagon covers an `X`-marking, while the counted rectangle covers none.
  have key : ∀ D ∈ G.crossingChangeHexagonCompositeDecompositions C t x z, D.isLeft ↔
      (G.XSet ∩ D.toRectangleDecomposition.first.toGridRectangle.coveredSquares).Nonempty := by
    rintro (D | D) hD
    · obtain ⟨hP, -⟩ := (G.mem_crossingChangeHexagonRectangleDecompositions C t D).mp
        ((G.inl_mem_crossingChangeHexagonCompositeDecompositions C t D).mp hD)
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        XSet_inter_coveredSquares_of_mem_crossingChangeCommutationHexagons hX hP]
      simp
    · obtain ⟨hr, -⟩ := (G.mem_crossingChangeRectangleHexagonDecompositions C t D).mp
        ((G.inr_mem_crossingChangeHexagonCompositeDecompositions C t D).mp hD)
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm]
      simp
  exact GridHexagonCompositeDecomposition.injOn_toRectangleDecomposition_of_isLeft_iff
    (fun D => (G.XSet ∩ D.first.toGridRectangle.coveredSquares).Nonempty) key

/-! ### The recut pairing -/

variable (G C t)

/-- The counted composites from `x` to `z` whose two rectangles have a common side column and
whose recut is not the underlying rectangle decomposition of any counted composite. -/
noncomputable def crossingChangeUnpairedHexagonComposites (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeHexagonCompositeDecompositions C t x z).filter fun D =>
    ¬D.toRectangleDecomposition.HasDisjointSides ∧
      ∀ E ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
        ¬D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition

/-- A composite is unpaired exactly when it is counted, its rectangles have a common side column,
and its recut underlies no counted composite. -/
@[simp]
theorem mem_crossingChangeUnpairedHexagonComposites {x z : GridState n}
    (D : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    D ∈ G.crossingChangeUnpairedHexagonComposites C t x z ↔
      D ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ∧
        ¬D.toRectangleDecomposition.HasDisjointSides ∧
          ∀ E ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
            ¬D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [crossingChangeUnpairedHexagonComposites, Finset.mem_filter]

variable {G C t}

/-- A counted composite is unpaired when its underlying decomposition has exactly one common side
and the recut of that decomposition underlies no counted composite. -/
theorem mem_crossingChangeUnpairedHexagonComposites_of_toRectangleDecomposition_eq
    {x z : GridState n} {D : GridRectangleDecomposition x z} (hone : D.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hrecut : ∀ E ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
      E.toRectangleDecomposition ≠ D.recut hone hfirst hsecond)
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    (hFD : F.toRectangleDecomposition = D) :
    F ∈ G.crossingChangeUnpairedHexagonComposites C t x z := by
  refine (G.mem_crossingChangeUnpairedHexagonComposites C t F).mpr
    ⟨hF, ?_, fun E hE hrec => hrecut E hE ?_⟩
  · rw [hFD]
    exact D.not_hasDisjointSides_of_hasOneCommonSide hone
  · rw [hFD] at hrec
    exact (D.existsUnique_isRecut hone hfirst hsecond).unique hrec (D.isRecut_recut _ _ _)

/-- If the annulus squares carry no `X`-marking, a counted composite whose underlying
decomposition has exactly one common side, and whose recut underlies no counted composite, is the
only unpaired composite with this decomposition. -/
theorem existsUnique_crossingChangeUnpairedHexagonComposite_of_toRectangleDecomposition_eq
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {D : GridRectangleDecomposition x z} (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty)
    (hsecond : D.second.IsEmpty)
    (hrecut : ∀ E ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
      E.toRectangleDecomposition ≠ D.recut hone hfirst hsecond)
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    (hFD : F.toRectangleDecomposition = D) :
    ∃! F' : GridHexagonCompositeDecomposition a C.turnRow t x z,
      F' ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        F'.toRectangleDecomposition = D ∧
          G.crossingChangeHexagonCompositeWeight C t R F' =
            G.crossingChangeHexagonCompositeWeight C t R F := by
  refine ⟨F, ⟨mem_crossingChangeUnpairedHexagonComposites_of_toRectangleDecomposition_eq hone
    hfirst hsecond hrecut hF hFD, hFD, rfl⟩, fun F' hF' => ?_⟩
  exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F').mp hF'.1).1 hF
    (hF'.2.1.trans hFD.symm)

variable [CharP R 2]

open scoped Classical in
/-- If the annulus squares carry no `X`-marking, then off the diagonal and in characteristic two
the counted composites whose rectangles share a side column have the total weight of the unpaired
ones: recut partners cancel in pairs
(`GridRectangleDecomposition.sum_filter_not_hasDisjointSides_eq_sum_filter_forall_not_isRecut`). -/
theorem sum_crossingChangeHexagonCompositeWeight_overlap_eq_sum_unpaired
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ (G.crossingChangeHexagonCompositeDecompositions C t x z).filter
        (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeHexagonCompositeWeight C t R D =
      ∑ D ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R D := by
  rw [GridRectangleDecomposition.sum_filter_not_hasDisjointSides_eq_sum_filter_forall_not_isRecut
    _ _ _ CharTwo.add_self_eq_zero hzx
    (fun _ hD => isEmpty_of_mem_crossingChangeHexagonCompositeDecompositions hD)
    (injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z)
    (fun _ hD _ hE h => crossingChangeHexagonCompositeWeight_eq_of_isRepartition R hX hD hE h)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext D
  simp only [Finset.mem_filter, mem_crossingChangeUnpairedHexagonComposites]

open scoped Classical in
/-- **Reduction of the crossing change homotopy equation to unpaired composites.** If the turn
rows `s` and `t` differ and the annulus squares carry no `X`-marking, then over a commutative
semiring of characteristic two the equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ`, with `w` the annulus
weight, holds on every chain exactly when, for all distinct grid states `x` and `z`, the unpaired
composites from `x` to `z` have the total weight of the products of the coefficients of `Φ`,
renamed by the column swap, and of `Ψ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        G.crossingChangeAnnulusWeight R C t • c +
          (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, x ≠ z →
        ∑ D ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
            G.crossingChangeHexagonCompositeWeight C t R D =
          ∑ y : GridState n,
            rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
              (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [G.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_ne C t R hst hX]
  refine forall₂_congr fun x z => forall_congr' fun hxz => ?_
  rw [← sum_crossingChangeHexagonCompositeWeight_filter_not_hasDisjointSides,
    sum_crossingChangeHexagonCompositeWeight_overlap_eq_sum_unpaired R hX (Ne.symm hxz)]

open scoped Classical in
/-- **Reduction of the crossing change homotopy equation to unpaired composites**, for markings in
the order `O_b, O_a, X_b, X_a`. If the segments of the columns `a` and `b = finRotate n a`
interleave with `O_a` on the arc of column `b`, the crossing change maps turn in the rows of
`O_a` and `X_b`, and `R` has characteristic two, then `∂ ∘ H + H ∘ ∂ = V_b + Ψ ∘ Φ` holds on every
chain exactly when, between distinct grid states, the unpaired composites have the total weight of
the pentagon coefficient products. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
          (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, x ≠ z →
        ∑ D ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
            G.crossingChangeHexagonCompositeWeight C t R D =
          ∑ y : GridState n,
            rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
              (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [← crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc R h hO hs ht]
  exact unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht)

open scoped Classical in
/-- **Reduction of the crossing change homotopy equation to unpaired composites**, for markings in
the order `O_b, X_a, X_b, O_a`. If the segments of the columns `a` and `b = finRotate n a`
interleave with `O_a` off the arc of column `b`, the crossing change maps turn in the rows of
`X_a` and `O_b`, and `R` has characteristic two, then `∂ ∘ H + H ∘ ∂ = V_a + Ψ ∘ Φ` holds on every
chain exactly when, between distinct grid states, the unpaired composites have the total weight of
the pentagon coefficient products. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
          (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, x ≠ z →
        ∑ D ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
            G.crossingChangeHexagonCompositeWeight C t R D =
          ∑ y : GridState n,
            rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
              (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [← crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc R h hO hs ht]
  exact unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht)

end GridDiagram

end TauCeti
