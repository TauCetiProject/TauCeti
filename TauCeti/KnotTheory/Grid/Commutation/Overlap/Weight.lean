/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Counted

/-!
# Weights of the overlap recuts for grid commutation

Let `C` be a validated column commutation of a grid diagram `G`, commuting the columns `a` and
`b = finRotate n a`, and let `G' = G.swapColumns a b`. The chain-map equation for the pentagon
map compares, coefficient by coefficient, a sum over a rectangle of `G` followed by a pentagon,
weighted by `GridDiagram.rectanglePentagonWeight`, with a sum over a pentagon followed by a
rectangle of `G'`, weighted by `GridDiagram.pentagonRectangleWeight`. When the two domains share
exactly one side, their union is recut the other way (`Overlap/Basic.lean`, `Overlap/Right.lean`),
and `Overlap/Counted.lean` shows that the recuts landing in the other sum are counted there. This
file shows that each of these recuts of a rectangle followed by a pentagon has the weight of the
domain it came from: a recut into the other sum contributes the same monomial there, and the recut
that stays in the same sum pairs two terms of equal weight, which cancel in characteristic two.

Both weights depend only on the composite domain, its squares counted with multiplicity: a
square carrying the `O`-marking of column `c` of `G` contributes the variable of column
`Equiv.swap a b c`, the column of that marking in `G'`. A rectangle of `G'` is read in `G` with
its two commuted columns exchanged, since the `O`-marking of column `c` of `G'` is the `O`-marking
of column `Equiv.swap a b c` of `G`. This gives the two weight criteria below.

The recuts preserve the squares covered by the *underlying* rectangles, but a pentagon covers
only part of its underlying rectangle in the two columns next to the replaced grid line: the rows
above the turn row in column `a`, and in column `b` the rows from its bottom row up to the turn
row. Matching the composite domains therefore comes down to a balance in these two columns. In
the second common-initial-side branch it needs the cyclic order of the three corner rows that
emptiness forces (`GridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left`).

## Main results

* `TauCeti.GridDiagram.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq`
  and `TauCeti.GridDiagram.rectanglePentagonWeight_eq_of_val_add_val_eq`: two composite domains
  covering the same squares with the same multiplicities have the same weight.
* `TauCeti.GridDiagram.pentagonRectangleWeight_recutLeftEqLeft`: the recut along a common initial
  side preserves the weight.
* `TauCeti.GridDiagram.pentagonRectangleWeight_recutRightEqRightFirst`: so does the recut along a
  common terminal side when the first new rectangle inherits the replaced grid line.
* `TauCeti.GridDiagram.rectanglePentagonWeight_recutRightEqRightSecond`: so does the recut along a
  common terminal side when the second new rectangle inherits it, which pairs two terms of the
  same sum.

## References

The pairing of composite domains in the chain-map equation of a column commutation follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace Grid

variable {n : ℕ}

/-- A point `v` strictly inside the arc from `u` to `w` cuts every arc from `u` to a point `s` of
the arc from `v` to `w`, counted. -/
private theorem ite_mem_cIco_eq_add_of_mem_cIoo {u v w s : Fin n} (hv : v ∈ cIoo u w)
    (hs : s ∈ cIco v w) (t : Fin n) :
    (if t ∈ cIco u s then 1 else 0 : ℕ) =
      (if t ∈ cIco u v then 1 else 0) + if t ∈ cIco v s then 1 else 0 := by
  simp only [mem_cIco, mem_cIoo, ne_eq, ← Fin.val_inj] at hv hs ⊢
  split_ifs at hv hs ⊢ <;> omega

/-- A point `s` of the arc from `u` to `w` cuts it into the arc before `s`, the point `s` and the
open arc after `s`, counted. -/
private theorem ite_mem_cIco_eq_add_add {u w s : Fin n} (hs : s ∈ cIco u w) (t : Fin n) :
    (if t ∈ cIco u w then 1 else 0 : ℕ) =
      (if t ∈ cIco u s then 1 else 0) + (if t = s then 1 else 0) +
        if t ∈ cIoo s w then 1 else 0 := by
  simp only [mem_cIco, mem_cIoo, ne_eq, ← Fin.val_inj] at hs ⊢
  split_ifs at hs ⊢ <;> omega

end Grid

namespace GridPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- The two columns next to the replaced grid line of a pentagon are distinct. -/
private theorem ne_finRotate (P : GridPentagonBetween a s x y) : a ≠ finRotate n a := fun h =>
  Grid.right_notMem_cIco P.left (finRotate n a) (h ▸ Grid.self_mem_cIco_finRotate P.left_ne)

/-- In the column before the replaced grid line a pentagon covers the rows above the turn row. -/
private theorem mk_mem_coveredSquares_left_column (P : GridPentagonBetween a s x y) (t : Fin n) :
    (a, t) ∈ P.coveredSquares ↔ t ∈ Grid.cIoo s P.top := by
  simp only [P.mem_coveredSquares, ne_eq, not_true_eq_false, false_and, true_and, false_or,
    P.ne_finRotate, or_false]

/-- In the column after the replaced grid line a pentagon covers the rows from its bottom row up
to the turn row. -/
private theorem mk_mem_coveredSquares_right_column (P : GridPentagonBetween a s x y) (t : Fin n) :
    (finRotate n a, t) ∈ P.coveredSquares ↔ t ∈ Grid.cIco P.bottom s := by
  simp only [P.mem_coveredSquares, Grid.right_notMem_cIco, P.ne_finRotate.symm, false_and,
    and_false, true_and, false_or]

/-- In the column before the replaced grid line the underlying rectangle of a pentagon covers
all of its rows. -/
private theorem mk_mem_toGridRectangle_coveredSquares_left_column
    (P : GridPentagonBetween a s x y) (t : Fin n) :
    (a, t) ∈ P.toGridRectangle.coveredSquares ↔ t ∈ Grid.cIco P.bottom P.top := by
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, P.right_eq, Grid.self_mem_cIco_finRotate P.left_ne,
    true_and]

/-- The underlying rectangle of a pentagon covers nothing in the column after the replaced grid
line. -/
private theorem mk_notMem_toGridRectangle_coveredSquares_right_column
    (P : GridPentagonBetween a s x y) (t : Fin n) :
    (finRotate n a, t) ∉ P.toGridRectangle.coveredSquares := by
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    P.right_eq, Grid.right_notMem_cIco, false_and, not_false_eq_true]

/-- The turn row of a pentagon lies among its rows. -/
private theorem turn_mem_cIco_bottom_top (P : GridPentagonBetween a s x y) :
    s ∈ Grid.cIco P.bottom P.top := by
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
  exact P.turn_mem

end GridPentagonBetween

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- A repartition covers the same squares with the same multiplicities on both sides. -/
private theorem IsRepartition.val_add_val_eq {D E : GridRectangleDecomposition x z}
    (h : D.IsRepartition E) :
    E.first.toGridRectangle.coveredSquares.val + E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val +
        D.second.toGridRectangle.coveredSquares.val := by
  rw [Multiset.add_eq_union_iff_disjoint.mpr
      (Finset.disjoint_val.mpr h.disjoint_coveredSquares_right),
    Multiset.add_eq_union_iff_disjoint.mpr
      (Finset.disjoint_val.mpr h.disjoint_coveredSquares_left),
    ← Finset.union_val, ← Finset.union_val, h.coveredSquares_union_eq]

end GridRectangleDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A pentagon followed by a rectangle and a rectangle followed by a pentagon have the same
composite domain, squares counted with multiplicity and the columns `a` and `finRotate n a` of the
second rectangle exchanged, when their underlying rectangles repartition the same squares and the
two columns balance: at every row `t`, the second rectangle covers `(a, t)` and `t` lies between
the new pentagon's bottom row and the turn row as often as the second rectangle covers
`(finRotate n a, t)` and `t` lies between the original pentagon's bottom row and the turn row. -/
private theorem val_add_val_eq_of_isRepartition (D : GridRectanglePentagonDecomposition a s x z)
    (E : GridPentagonRectangleDecomposition a s x z)
    (hrep : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition)
    (hcol : ∀ t : Fin n,
      ((if (a, t) ∈ E.rectangle.toGridRectangle.coveredSquares then 1 else 0) +
          if t ∈ Grid.cIco E.pentagon.bottom s then 1 else 0 : ℕ) =
        (if (finRotate n a, t) ∈ E.rectangle.toGridRectangle.coveredSquares then 1 else 0) +
          if t ∈ Grid.cIco D.pentagon.bottom s then 1 else 0) :
    E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  have hrep' := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle] at hrep'
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  obtain ⟨c, t⟩ := p
  simp only [Prod.map_apply, Equiv.refl_apply]
  by_cases hca : c = a
  · subst hca
    have h1 := hrep' (c, t)
    have h2 := hrep' (finRotate n c, t)
    have h3 := hcol t
    have h4 := Grid.ite_mem_cIco_eq_add_add E.pentagon.turn_mem_cIco_bottom_top t
    have h5 := Grid.ite_mem_cIco_eq_add_add D.pentagon.turn_mem_cIco_bottom_top t
    simp only [GridPentagonBetween.mk_mem_coveredSquares_left_column,
      GridPentagonBetween.mk_mem_toGridRectangle_coveredSquares_left_column,
      GridPentagonBetween.mk_notMem_toGridRectangle_coveredSquares_right_column,
      Equiv.swap_apply_left, ↓reduceIte, zero_add, add_zero] at h1 h2 ⊢
    omega
  by_cases hcb : c = finRotate n a
  · subst hcb
    have h2 := hrep' (finRotate n a, t)
    have h3 := hcol t
    simp only [GridPentagonBetween.mk_mem_coveredSquares_right_column,
      GridPentagonBetween.mk_notMem_toGridRectangle_coveredSquares_right_column,
      Equiv.swap_apply_right, ↓reduceIte, zero_add, add_zero] at h2 ⊢
    omega
  · have h := hrep' (c, t)
    simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
      E.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb]
    omega

/-- Two rectangle--pentagon decompositions cover the same squares with the same multiplicities
when their underlying rectangle decompositions are repartitions of each other and their pentagons
have the same bottom row. -/
private theorem val_add_val_eq_of_isRepartition_of_bottom_eq
    (D D' : GridRectanglePentagonDecomposition a s x z)
    (hrep : D.toRectangleDecomposition.IsRepartition D'.toRectangleDecomposition)
    (hbottom : D'.pentagon.bottom = D.pentagon.bottom) :
    D'.rectangle.toGridRectangle.coveredSquares.val + D'.pentagon.coveredSquares.val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  have hrep' := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle] at hrep'
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val]
  obtain ⟨c, t⟩ := p
  by_cases hca : c = a
  · subst hca
    have h := hrep' (c, t)
    have h₁ := Grid.ite_mem_cIco_eq_add_add D'.pentagon.turn_mem_cIco_bottom_top t
    have h₂ := Grid.ite_mem_cIco_eq_add_add D.pentagon.turn_mem_cIco_bottom_top t
    simp only [GridPentagonBetween.mk_mem_coveredSquares_left_column,
      GridPentagonBetween.mk_mem_toGridRectangle_coveredSquares_left_column] at h ⊢
    rw [hbottom] at h h₁
    omega
  by_cases hcb : c = finRotate n a
  · subst hcb
    have h := hrep' (finRotate n a, t)
    simp only [GridPentagonBetween.mk_mem_coveredSquares_right_column,
      GridPentagonBetween.mk_notMem_toGridRectangle_coveredSquares_right_column, ↓reduceIte,
      add_zero, hbottom] at h ⊢
    omega
  · have h := hrep' (c, t)
    simp only [D'.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb]
    omega

end GridRectanglePentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

section SquareWeight

variable (R : Type*) [CommSemiring R]

/-- The weight of a square in a column commutation of the columns `a` and `b`: the variable of
the commuted column of its `O`-marking, and `1` on unmarked squares. -/
private noncomputable def swapSquareWeight (a b : Fin n) (p : Fin n × Fin n) :
    MvPolynomial (Fin n) R :=
  if p ∈ G.OSet then MvPolynomial.X (Equiv.swap a b p.1) else 1

/-- The renamed `O`-monomial of a rectangle of the original diagram, square by square. -/
private theorem rename_OMonomial_eq_prod_swapSquareWeight (a b : Fin n) (r : GridRectangle n) :
    MvPolynomial.rename (Equiv.swap a b) (G.OMonomial R r) =
      ∏ p ∈ r.coveredSquares, G.swapSquareWeight R a b p := by
  rw [G.OMonomial_eq_prod_coveredSquares R, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  unfold swapSquareWeight
  split_ifs <;> simp

/-- The `O`-monomial of a rectangle of the commuted diagram, square by square: a square of the
commuted diagram carries the marking of the square of the original diagram in the swapped
column. -/
private theorem OMonomial_swapColumns_eq_prod_swapSquareWeight (a b : Fin n)
    (r : GridRectangle n) :
    (G.swapColumns a b).OMonomial R r =
      ∏ p ∈ r.coveredSquares.map
        ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding,
        G.swapSquareWeight R a b p := by
  rw [(G.swapColumns a b).OMonomial_eq_prod_coveredSquares R, Finset.prod_map]
  refine Finset.prod_congr rfl fun p _ => ?_
  obtain ⟨c, t⟩ := p
  simp only [swapSquareWeight, mem_OSet_swapColumns, Equiv.coe_toEmbedding,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.swap_apply_self]

/-- The weight of a pentagon, square by square. -/
private theorem pentagonWeight_eq_prod_swapSquareWeight (C : ColumnCommutationData G)
    {x y : GridState n} (P : GridPentagonBetween C.column C.turnRow x y) :
    G.pentagonWeight R C P =
      ∏ p ∈ P.coveredSquares, G.swapSquareWeight R C.column (finRotate n C.column) p :=
  G.pentagonWeight_eq_prod_coveredSquares R C P

end SquareWeight

variable (C : ColumnCommutationData G) (R : Type*) [CommSemiring R] {x z : GridState n}

local notation "b" => finRotate n C.column

/-- A pentagon followed by a rectangle of the commuted diagram has the weight of a rectangle
followed by a pentagon when the two composite domains cover the same squares with the same
multiplicities, the squares of the rectangle of the commuted diagram being read in the
original diagram, that is with the two commuted columns exchanged. -/
theorem pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    G.pentagonRectangleWeight C R E = G.rectanglePentagonWeight C R D := by
  rw [pentagonRectangleWeight_def, rectanglePentagonWeight_def,
    pentagonWeight_eq_prod_swapSquareWeight, pentagonWeight_eq_prod_swapSquareWeight,
    OMonomial_swapColumns_eq_prod_swapSquareWeight, rename_OMonomial_eq_prod_swapSquareWeight]
  simp only [Finset.prod_eq_multiset_prod, ← Multiset.prod_add, ← Multiset.map_add, h]

/-- Two rectangle--pentagon decompositions have the same weight when they cover the same squares
with the same multiplicities. -/
theorem rectanglePentagonWeight_eq_of_val_add_val_eq
    (D D' : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (h : D'.rectangle.toGridRectangle.coveredSquares.val + D'.pentagon.coveredSquares.val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    G.rectanglePentagonWeight C R D' = G.rectanglePentagonWeight C R D := by
  rw [rectanglePentagonWeight_def, rectanglePentagonWeight_def,
    pentagonWeight_eq_prod_swapSquareWeight, pentagonWeight_eq_prod_swapSquareWeight,
    rename_OMonomial_eq_prod_swapSquareWeight, rename_OMonomial_eq_prod_swapSquareWeight]
  simp only [Finset.prod_eq_multiset_prod, ← Multiset.prod_add, ← Multiset.map_add, h]

/-- Recutting a rectangle followed by a pentagon along their common initial side preserves the
weight: the promoted pentagon followed by the remaining rectangle of the commuted diagram has
the weight of the original rectangle followed by the original pentagon. -/
theorem pentagonRectangleWeight_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    G.pentagonRectangleWeight C R (D.recutLeftEqLeft hcommon hone hrectangle hpentagon) =
      G.rectanglePentagonWeight C R D := by
  set E := D.recutLeftEqLeft hcommon hone hrectangle hpentagon with hE
  have hfirst : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  have hsecond : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle,
      D.toRectangleDecomposition_second_toGridRectangle] using hpentagon
  have hleft : D.toRectangleDecomposition.first.left = D.toRectangleDecomposition.second.left := by
    simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] using hcommon
  have hdata : D.toRectangleDecomposition.IsRecutOfLeftEqLeft E.toRectangleDecomposition := by
    rw [hE, D.recutLeftEqLeft_toRectangleDecomposition]
    exact D.toRectangleDecomposition.isRecutOfLeftEqLeft_recut hleft hone hfirst hsecond
  apply G.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq C R
  refine D.val_add_val_eq_of_isRepartition E
    (D.isRecut_recutLeftEqLeft hcommon hone hrectangle hpentagon).isRepartition fun t => ?_
  have hEright := hdata.recut_sides.2
  simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right] at hEright
  have hPbottom : D.pentagon.bottom = x D.rectangle.right := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, D.rectangle.map_left]
  simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEright]
  rcases hdata.recut_branch with ⟨hcol, -, hPleft, hrleft⟩ | ⟨hcol, hmiddle, hPleft, hrleft⟩
  -- The remaining rectangle has the original rectangle's columns, before the two commuted
  -- columns, and the promoted pentagon starts where the original pentagon does.
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      D.pentagon.right_eq] at hcol hPleft hrleft
    have ha : C.column ∉ Grid.cIco D.rectangle.left D.rectangle.right := fun ha =>
      Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol) ha
        (Grid.self_mem_cIco_finRotate (Grid.ne_right_of_mem_cIoo hcol))
    have hb : finRotate n C.column ∉ Grid.cIco D.rectangle.left D.rectangle.right := fun hb =>
      Grid.right_notMem_cIco _ _ (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hb hcol)
    rw [hrleft, GridRectangleBetween.bottom_def, hPleft, hPbottom]
    simp only [ha, hb, false_and, ↓reduceIte]
  -- The remaining rectangle starts at the commuted grid line and keeps the original rectangle's
  -- rows, while the promoted pentagon reaches back to the original rectangle's initial row.
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      D.pentagon.right_eq] at hcol hmiddle hPleft hrleft
    have ha : C.column ∉ Grid.cIco (finRotate n C.column) D.rectangle.right := fun ha =>
      Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)
        (Grid.self_mem_cIco_finRotate (Grid.ne_left_of_mem_cIoo hcol).symm) ha
    have hb : finRotate n C.column ∈ Grid.cIco (finRotate n C.column) D.rectangle.right :=
      Grid.left_mem_cIco (Grid.ne_right_of_mem_cIoo hcol)
    have hord := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hleft
      (by simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
        D.pentagon.right_eq] using (Grid.ne_right_of_mem_cIoo hcol).symm) hfirst hsecond).2
    have hsecondTop := congrArg GridRectangle.top D.toRectangleDecomposition_second_toGridRectangle
    simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      GridRectangleBetween.toGridRectangle_top] at hord hsecondTop
    rw [hsecondTop] at hord
    have hturn := D.pentagon.turn_mem_cIco_bottom_top
    rw [hPbottom] at hturn
    rw [hrleft, GridRectangleBetween.bottom_def, hPleft, hPbottom, hmiddle,
      GridState.swapColumns_apply, GridState.swapColumns_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne D.rectangle.left_ne_right.symm
        (Grid.ne_right_of_mem_cIoo hcol).symm]
    simp only [ha, hb, false_and, true_and, ↓reduceIte, zero_add]
    exact Grid.ite_mem_cIco_eq_add_of_mem_cIoo hord hturn t

/-- Recutting a rectangle followed by a pentagon along their common terminal side preserves the
weight when the first new rectangle inherits the replaced grid line: the promoted pentagon
followed by the remaining rectangle of the commuted diagram has the weight of the original
rectangle followed by the original pentagon. -/
theorem pentagonRectangleWeight_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right = D.pentagon.right) :
    G.pentagonRectangleWeight C R
        (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst) =
      G.rectanglePentagonWeight C R D := by
  set E := D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst with hE
  apply G.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq C R
  refine D.val_add_val_eq_of_isRepartition E
    (D.isRecut_recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).isRepartition
    fun t => ?_
  obtain ⟨-, -, -, -, hcols, ha, -⟩ :=
    D.recutRightEqRightFirst_rectangle_geometry hcommon hone hrectangle hpentagon hfirst
  rw [← hE] at hcols ha
  obtain ⟨hcol, -, hleft⟩ :=
    D.first_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hfirst
  simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] at hcol hleft
  -- The remaining rectangle lies inside the original rectangle, which stops before the
  -- replaced grid line, and misses the column before that line.
  have hb : finRotate n C.column ∉ E.rectangle.toGridRectangle.coveredColumns :=
    fun hb => Grid.right_notMem_cIco D.rectangle.left (finRotate n C.column) (by
      simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, hcommon, D.pentagon.right_eq] using hcols hb)
  -- The promoted pentagon starts where the original pentagon does.
  have hbottom : E.pentagon.bottom = D.pentagon.bottom := by
    rw [hE, D.recutRightEqRightFirst_pentagon_bottom, GridRectangleBetween.bottom_def, hleft,
      GridRectangleBetween.bottom_def, D.rectangle.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol)
        (Grid.ne_right_of_mem_cIoo hcol)]
  simp only [GridRectangle.mem_coveredSquares, ha, hb, hbottom, false_and, ↓reduceIte]

/-- Recutting a rectangle followed by a pentagon along their common terminal side preserves the
weight when the second new rectangle inherits the replaced grid line: the new rectangle followed
by the promoted pentagon has the weight of the original rectangle followed by the original
pentagon. -/
theorem rectanglePentagonWeight_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.right) :
    G.rectanglePentagonWeight C R
        (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond) =
      G.rectanglePentagonWeight C R D := by
  apply G.rectanglePentagonWeight_eq_of_val_add_val_eq C R
  refine D.val_add_val_eq_of_isRepartition_of_bottom_eq _
    (D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).isRepartition ?_
  obtain ⟨hcol, -, hleft, hmiddle⟩ :=
    D.second_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hsecond
  simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] at hcol hleft hmiddle
  -- The promoted pentagon starts on the original rectangle's initial side, where the recut
  -- state has the row of the original pentagon's initial side.
  rw [D.recutRightEqRightSecond_pentagon_bottom, GridRectangleBetween.bottom_def, hleft, hmiddle,
    GridState.swapColumns_apply, Equiv.swap_apply_right, GridRectangleBetween.bottom_def,
    D.rectangle.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol).symm
      (fun h => D.pentagon.left_ne_right (h.trans hcommon))]

end GridDiagram

end TauCeti
