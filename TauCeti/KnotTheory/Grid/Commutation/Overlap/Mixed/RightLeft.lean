/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Weight

/-!
# Recutting a rectangle that ends where a pentagon starts

Consider a rectangle of the original diagram followed by a commutation pentagon turning on its
terminal side, which is the grid line `b = finRotate n a` replaced in the commutation. This file
treats the mixed overlap in which the rectangle's terminal side is the pentagon's initial side.

Write `p` and `q` for the rectangle's sides and `q`, `b` for the pentagon's. The two domains share
their bottom row, the row of the source state on `p`. The generic empty-rectangle recut has its
first rectangle ending on `b`, with the pentagon's top row as its top row. Emptiness leaves two
branches: either the rectangle's top row lies strictly between the common bottom row and the
pentagon's top row, and the first recut rectangle spans the rows from the former to the latter;
or the pentagon's top row lies strictly inside the rectangle's rows, and the first recut rectangle
spans exactly the pentagon's rows. In both branches it contains the turn row exactly when the turn
row lies in the rows from the rectangle's top to the pentagon's top. It then promotes to a
pentagon followed by a rectangle of the commuted diagram.

The promoted pentagon and the original one both end on `b`, have the same top row and contain
the turn row, while the original rectangle has no side on `b` and so covers the two columns next
to `b` in the same rows. Counting the squares of these two columns against the generic
repartition therefore shows that both composite domains cover the same squares with the same
multiplicities (`coveredSquares_val_add_val_recutRightEqLeft`). The recut of a counted domain is
counted with the same monomial weight, and these terms cancel between the rectangle--pentagon and
pentagon--rectangle sums of the chain-map equation
(`GridDiagram.add_sum_rectanglePentagonWeight_eq_add_sum_iff_sdiff_rightLeftOverlap`).

In the remaining case, where the rectangle's top row lies between the common bottom row and the
pentagon's top row and the turn row lies below the rectangle's top row, the second recut rectangle
ends on `b` instead. The recut then stays among rectangle--pentagon terms, as the partner of a
common-terminal-side self-pair (`GridDiagram.terminalSelfPairs`). This file is the half-turn
mirror of the mixed `left = right` overlap of initial-side pentagons in
`TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.LeftRight`.

## Main definitions

* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqLeft`: the promoted
  pentagon--rectangle recut of the mixed `right = left` overlap.
* `TauCeti.GridDiagram.rightLeftOverlapSources`: the counted rectangle--pentagon domains with this
  mixed overlap whose recut lands in the pentagon--rectangle sum.
* `TauCeti.GridDiagram.rightLeftOverlapPartners`: their recuts.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.isRecut_recutRightEqLeft`: the promoted
  decomposition is an empty-rectangle recut of the original domain.
* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqLeft_top`: its pentagon has the
  original pentagon's top row and its rectangle the original rectangle's top row.
* `TauCeti.GridRectanglePentagonDecomposition.coveredSquares_val_add_val_recutRightEqLeft`: both
  decompositions cover the same squares with the same multiplicities.
* `TauCeti.GridDiagram.recutRightEqLeft_mem_pentagonRectangleDecompositions` and
  `TauCeti.GridDiagram.pentagonRectangleWeight_recutRightEqLeft`: the recut of a counted domain is
  counted, with the same weight.
* `TauCeti.GridDiagram.sum_rectanglePentagonWeight_rightLeftOverlapSources_eq_sum_partners` and
  `TauCeti.GridDiagram.add_sum_rectanglePentagonWeight_eq_add_sum_iff_sdiff_rightLeftOverlap`:
  the sources and their recuts contribute equally and can be removed from the chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- If the turn row lies in the rows from the rectangle's top to the pentagon's top, the
rectangle's initial side is not the pentagon's terminal side: otherwise the two domains would
share their top row, and these rows would be empty. -/
theorem rectangle_left_ne_pentagon_right_of_mem_cIco
    (D : GridRectanglePentagonDecomposition a s x z)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    D.rectangle.left ≠ D.pentagon.right := by
  intro hother
  have htop : D.pentagon.top = D.rectangle.top := by
    rw [GridRectangleBetween.top_def, ← hother, D.rectangle.map_left,
      GridRectangleBetween.top_def]
  rw [htop] at hturn
  simp at hturn

/-- A mixed overlap whose rectangle terminal side is the pentagon initial side has exactly one
common side column when its two other sides differ. -/
theorem hasOneCommonSide_of_right_eq_left (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hother : D.rectangle.left ≠ D.pentagon.right) :
    D.toRectangleDecomposition.HasOneCommonSide := by
  apply D.toRectangleDecomposition.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.rectangle.right, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left,
      toRectangleDecomposition_second_right] at hc
    have hfirst := D.rectangle.left_ne_right
    have hsecond := D.pentagon.left_ne_right
    grind

/-- The generic recut of a mixed `right = left` overlap whose turn row lies in the rows from the
rectangle's top to the pentagon's top. -/
private noncomputable def rightLeftRecut (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    GridRectangleDecomposition x z :=
  D.recutOfIsEmpty (D.hasOneCommonSide_of_right_eq_left hcommon
      (D.rectangle_left_ne_pentagon_right_of_mem_cIco hturn))
    hrectangle hpentagon

/-- The first rectangle of the generic recut ends on the replaced line, with the pentagon's top
row, and contains the turn row; the second has the rectangle's top row. -/
private theorem rightLeftRecut_geometry (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    let E := D.rightLeftRecut hcommon hrectangle hpentagon hturn
    E.first.right = finRotate n a ∧ E.first.top = D.pentagon.top ∧
      E.second.top = D.rectangle.top ∧ s ∈ Grid.cIco E.first.bottom E.first.top := by
  intro E
  have hother := D.rectangle_left_ne_pentagon_right_of_mem_cIco hturn
  have hone := D.hasOneCommonSide_of_right_eq_left hcommon hother
  obtain ⟨hfb, hft, hst⟩ : D.toRectangleDecomposition.first.bottom = D.rectangle.bottom ∧
      D.toRectangleDecomposition.first.top = D.rectangle.top ∧
        D.toRectangleDecomposition.second.top = D.pentagon.top := by
    simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right, toRectangleDecomposition_middle, and_self]
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqLeft E := by
    simp only [E, rightLeftRecut]
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.toRectangleDecomposition.isRecutOfRightEqLeft_recut
      (by simpa only [toRectangleDecomposition_first_right, toRectangleDecomposition_second_left]
        using hcommon) hone _ _
  obtain ⟨hEft, hEst⟩ := hdata.recut_sides
  rw [hst] at hEft
  rw [hft] at hEst
  -- The source state has the same row on `b` before and after the rectangle, since `b` is not a
  -- side of the rectangle; so the first recut rectangle's top row lies on `b`.
  have hright : E.first.right = finRotate n a := by
    apply x.toPerm.injective
    have hb : D.pentagon.right = finRotate n a := D.pentagon.right_eq
    have hleft : finRotate n a ≠ D.rectangle.left := hb ▸ hother.symm
    have hrightNe : finRotate n a ≠ D.rectangle.right :=
      hcommon ▸ hb ▸ D.pentagon.left_ne_right.symm
    exact ((GridRectangleBetween.top_def _).symm.trans hEft).trans
      ((GridRectangleBetween.top_def _).trans (by
        rw [hb, D.rectangle.map_of_ne _ hleft hrightNe]))
  refine ⟨hright, hEft, hEst, ?_⟩
  rw [hEft]
  -- The two domains share their bottom row, so the turn row lies in the rows from the
  -- rectangle's bottom to the pentagon's top.
  have hbottom : D.pentagon.bottom = D.rectangle.bottom := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, D.rectangle.map_right,
      GridRectangleBetween.bottom_def]
  have hturnWhole : s ∈ Grid.cIco D.rectangle.bottom D.pentagon.top := by
    simpa only [hbottom] using D.pentagon.turn_mem_cIco_bottom_top
  rcases hdata.recut_branch with ⟨-, -, hEfb, -⟩ | ⟨-, -, hEfb, -⟩
  · -- The first recut rectangle spans the rows from the rectangle's top to the pentagon's top.
    rw [hft] at hEfb
    rw [hEfb]
    exact hturn
  · -- The first recut rectangle spans the pentagon's rows.
    rw [hfb] at hEfb
    rw [hEfb]
    exact hturnWhole

/-- Promote the first generic recut rectangle of a mixed `right = left` overlap to a pentagon,
when the turn row lies in the rows from the rectangle's top to the pentagon's top. -/
noncomputable def recutRightEqLeft (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    GridPentagonRectangleDecomposition a s x z where
  middle := (D.rightLeftRecut hcommon hrectangle hpentagon hturn).middle
  pentagon := GridPentagonBetween.ofRightEq
    (D.rightLeftRecut hcommon hrectangle hpentagon hturn).first
    (D.rightLeftRecut_geometry hcommon hrectangle hpentagon hturn).1
    (D.rightLeftRecut_geometry hcommon hrectangle hpentagon hturn).2.2.2
  rectangle := (D.rightLeftRecut hcommon hrectangle hpentagon hturn).second

/-- Forgetting the turn row of the promoted decomposition recovers the generic recut. -/
@[simp]
theorem recutRightEqLeft_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    (D.recutRightEqLeft hcommon hrectangle hpentagon hturn).toRectangleDecomposition =
      D.recutOfIsEmpty (D.hasOneCommonSide_of_right_eq_left hcommon
          (D.rectangle_left_ne_pentagon_right_of_mem_cIco hturn))
        hrectangle hpentagon := by
  apply GridRectangleDecomposition.ext
  · simp only [recutRightEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left]
    exact GridPentagonBetween.ofRightEq_left _ _ _
  · simp only [recutRightEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
      GridPentagonBetween.ofRightEq_right]
    exact (D.rightLeftRecut_geometry hcommon hrectangle hpentagon hturn).1.symm
  · simp only [recutRightEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left, rightLeftRecut]
  · simp only [recutRightEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right, rightLeftRecut]

/-- The promoted decomposition is an empty-rectangle recut of the original composite domain. -/
theorem isRecut_recutRightEqLeft (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    D.toRectangleDecomposition.IsRecut
      (D.recutRightEqLeft hcommon hrectangle hpentagon hturn).toRectangleDecomposition := by
  rw [recutRightEqLeft_toRectangleDecomposition]
  exact D.isRecut_recutOfIsEmpty _ _ _

/-- The promoted pentagon of a mixed `right = left` recut has the original pentagon's top row,
and the promoted rectangle has the original rectangle's top row. -/
theorem recutRightEqLeft_top (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    (D.recutRightEqLeft hcommon hrectangle hpentagon hturn).pentagon.top = D.pentagon.top ∧
      (D.recutRightEqLeft hcommon hrectangle hpentagon hturn).rectangle.top =
        D.rectangle.top := by
  obtain ⟨-, htop, hsecondTop, -⟩ := D.rightLeftRecut_geometry hcommon hrectangle hpentagon hturn
  exact ⟨by simpa only [recutRightEqLeft, GridPentagonBetween.ofRightEq_top] using htop,
    by simpa only [recutRightEqLeft] using hsecondTop⟩

/-- The promoted recut of a mixed `right = left` overlap covers the squares of the original domain
with the same multiplicities, the rectangle of the commuted diagram being read in the original
diagram with the two columns next to the replaced line exchanged. -/
theorem coveredSquares_val_add_val_recutRightEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top) :
    (D.recutRightEqLeft hcommon hrectangle hpentagon hturn).pentagon.coveredSquares.val +
        ((D.recutRightEqLeft hcommon hrectangle hpentagon
            hturn).rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  obtain ⟨hEtop, -⟩ := D.recutRightEqLeft_top hcommon hrectangle hpentagon hturn
  have hrep := (D.isRecut_recutRightEqLeft hcommon hrectangle hpentagon hturn).isRepartition
  set E := D.recutRightEqLeft hcommon hrectangle hpentagon hturn
  have hother := D.rectangle_left_ne_pentagon_right_of_mem_cIco hturn
  -- The original rectangle has neither side on the replaced line, so it covers the two columns
  -- next to that line together or misses them together. Both pentagons end on that line: they
  -- cover the column before it and miss the column after it.
  have hDab :
      finRotate n a ∈ Grid.cIco D.rectangle.left D.rectangle.right ↔
        a ∈ Grid.cIco D.rectangle.left D.rectangle.right :=
    Grid.mem_cIco_finRotate_iff_of_ne (by simpa only [D.pentagon.right_eq] using hother)
      (hcommon ▸ D.pentagon.left_ne)
  have haP : a ∈ Grid.cIco D.pentagon.left (finRotate n a) :=
    Grid.self_mem_cIco_finRotate D.pentagon.left_ne
  have haE : a ∈ Grid.cIco E.pentagon.left (finRotate n a) :=
    Grid.self_mem_cIco_finRotate E.pentagon.left_ne
  have hbP : finRotate n a ∉ Grid.cIco D.pentagon.left (finRotate n a) :=
    Grid.right_notMem_cIco _ _
  have hbE : finRotate n a ∉ Grid.cIco E.pentagon.left (finRotate n a) :=
    Grid.right_notMem_cIco _ _
  have hcounts := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle] at hcounts
  refine D.coveredSquares_val_add_val_eq_of_isRepartition E hrep fun t => ?_
  -- In each of the two columns next to the replaced line, compare the counts of the generic
  -- repartition; the two pentagons share their top row and both contain the turn row, so their
  -- rows split at the turn row with the same part above it.
  have ha' := hcounts (a, t)
  have hb' := hcounts (finRotate n a, t)
  have hsplitD := Grid.ite_mem_cIco_eq_add_add D.pentagon.turn_mem_cIco_bottom_top t
  have hsplitE := Grid.ite_mem_cIco_eq_add_add E.pentagon.turn_mem_cIco_bottom_top t
  simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
    ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def] at ha' hb' ⊢
  simp only [D.pentagon.right_eq, E.pentagon.right_eq, hDab, haP, haE, hbP, hbE, hEtop, true_and,
    false_and, ↓reduceIte] at ha' hb' hsplitE ⊢
  omega

end TauCeti.GridRectanglePentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

section Weights

variable (R : Type*) [CommSemiring R]

variable {x z : GridState n}
  (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.rectangle.right = D.pentagon.left)
  (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∈ Grid.cIco D.rectangle.top D.pentagon.top)

/-- Recutting a mixed `right = left` overlap into the pentagon--rectangle sum preserves the
weight. -/
@[simp]
theorem pentagonRectangleWeight_recutRightEqLeft :
    G.pentagonRectangleWeight C R (D.recutRightEqLeft hcommon hrectangle hpentagon hturn) =
      G.rectanglePentagonWeight C R D :=
  G.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutRightEqLeft hcommon hrectangle hpentagon hturn)

end Weights

variable {x z : GridState n}
  (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.rectangle.right = D.pentagon.left)
  (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∈ Grid.cIco D.rectangle.top D.pentagon.top)

/-- The recut of a counted mixed `right = left` overlap whose turn row lies in the rows from the
rectangle's top to the pentagon's top is a counted pentagon--rectangle domain. -/
theorem recutRightEqLeft_mem_pentagonRectangleDecompositions
    (hD : D ∈ G.rectanglePentagonDecompositions C x z) :
    D.recutRightEqLeft hcommon hrectangle hpentagon hturn ∈
      G.pentagonRectangleDecompositions C x z :=
  have hrecut := D.isRecut_recutRightEqLeft hcommon hrectangle hpentagon hturn
  G.mem_pentagonRectangleDecompositions_of_val_add_val_eq C hD
    (GridPentagonRectangleDecomposition.isEmpty_pentagon_of_isRecut _ hrecut)
    (GridPentagonRectangleDecomposition.isEmpty_rectangle_of_isRecut _ hrecut)
    (D.coveredSquares_val_add_val_recutRightEqLeft hcommon hrectangle hpentagon hturn)

/-! ### Cancelling the mixed `right = left` cross terms -/

variable (x z) in
/-- The counted rectangle--pentagon decompositions whose rectangle ends where the pentagon starts
and whose turn row lies in the rows from the rectangle's top to the pentagon's top: the mixed
`right = left` overlaps whose recut lands in the pentagon--rectangle sum. -/
noncomputable def rightLeftOverlapSources :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectanglePentagonDecompositions C x z).filter fun D =>
    D.rectangle.right = D.pentagon.left ∧ C.turnRow ∈ Grid.cIco D.rectangle.top D.pentagon.top

/-- Membership in the mixed `right = left` source family records counting, the common side and
the position of the turn row. -/
@[simp]
theorem mem_rightLeftOverlapSources :
    D ∈ G.rightLeftOverlapSources C x z ↔
      D ∈ G.rectanglePentagonDecompositions C x z ∧
        D.rectangle.right = D.pentagon.left ∧
          C.turnRow ∈ Grid.cIco D.rectangle.top D.pentagon.top := by
  classical
  simp [rightLeftOverlapSources]

private theorem rightLeftOverlapSource_data (hD : D ∈ G.rightLeftOverlapSources C x z) :
    D.rectangle.right = D.pentagon.left ∧
      C.turnRow ∈ Grid.cIco D.rectangle.top D.pentagon.top ∧
        D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty := by
  obtain ⟨hcounted, hcommon, hturn⟩ := (G.mem_rightLeftOverlapSources C D).1 hD
  rw [G.mem_rectanglePentagonDecompositions, G.mem_unblockedRectangles, G.mem_pentagons]
    at hcounted
  exact ⟨hcommon, hturn, hcounted.1.1, hcounted.2.1⟩

private noncomputable def rightLeftOverlapPartner
    (D : {D // D ∈ G.rightLeftOverlapSources C x z}) :
    GridPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutRightEqLeft
    (G.rightLeftOverlapSource_data C D.val D.property).1
    (G.rightLeftOverlapSource_data C D.val D.property).2.2.1
    (G.rightLeftOverlapSource_data C D.val D.property).2.2.2
    (G.rightLeftOverlapSource_data C D.val D.property).2.1

private theorem rightLeftOverlapPartner_isRecut
    (D : {D // D ∈ G.rightLeftOverlapSources C x z}) :
    D.val.toRectangleDecomposition.IsRecut
      (G.rightLeftOverlapPartner C D).toRectangleDecomposition :=
  D.val.isRecut_recutRightEqLeft _ _ _ _

/-- A source has exactly one common side and two empty underlying rectangles, so it has a unique
recut. -/
private theorem rightLeftOverlapSource_recut_data (hD : D ∈ G.rightLeftOverlapSources C x z) :
    D.toRectangleDecomposition.HasOneCommonSide ∧ D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨hcommon, hturn, hrectangle, hpentagon⟩ := G.rightLeftOverlapSource_data C D hD
  refine ⟨D.hasOneCommonSide_of_right_eq_left hcommon
    (D.rectangle_left_ne_pentagon_right_of_mem_cIco hturn), ?_, ?_⟩
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
      using hpentagon

private theorem rightLeftOverlapPartner_injective :
    Function.Injective (G.rightLeftOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.rightLeftOverlapPartner_isRecut C D
  have hE := G.rightLeftOverlapPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨honeD, hfD, hsD⟩ := G.rightLeftOverlapSource_recut_data C D.val D.property
  obtain ⟨honeE, hfE, hsE⟩ := G.rightLeftOverlapSource_recut_data C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

variable (x z) in
/-- The pentagon--rectangle partners obtained by recutting the mixed `right = left` sources: the
exact recut image of `GridDiagram.rightLeftOverlapSources`. -/
noncomputable def rightLeftOverlapPartners :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rightLeftOverlapSources C x z).attach.map
    ⟨G.rightLeftOverlapPartner C, G.rightLeftOverlapPartner_injective C⟩

/-- A pentagon--rectangle term is a partner exactly when its underlying rectangles are the recut
of a mixed `right = left` source. -/
@[simp]
theorem mem_rightLeftOverlapPartners
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.rightLeftOverlapPartners C x z ↔
      ∃ D ∈ G.rightLeftOverlapSources C x z,
        D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [rightLeftOverlapPartners, Finset.mem_map, Finset.mem_attach, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.rightLeftOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨hone, hf, hs⟩ := G.rightLeftOverlapSource_recut_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
    exact (D.toRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
      (G.rightLeftOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Each mixed `right = left` source belongs to the rectangle--pentagon sum. -/
theorem rightLeftOverlapSources_subset :
    G.rightLeftOverlapSources C x z ⊆ G.rectanglePentagonDecompositions C x z := fun D hD =>
  ((G.mem_rightLeftOverlapSources C D).1 hD).1

/-- Each partner belongs to the pentagon--rectangle sum. -/
theorem rightLeftOverlapPartners_subset :
    G.rightLeftOverlapPartners C x z ⊆ G.pentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [rightLeftOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  exact G.recutRightEqLeft_mem_pentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_rightLeftOverlapSources C D.val).1 D.property).1

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- Recutting identifies the total contribution of the mixed `right = left` sources with the total
contribution of their partners. -/
theorem sum_rectanglePentagonWeight_rightLeftOverlapSources_eq_sum_partners :
    ∑ D ∈ G.rightLeftOverlapSources C x z, G.rectanglePentagonWeight C R D =
      ∑ E ∈ G.rightLeftOverlapPartners C x z, G.pentagonRectangleWeight C R E := by
  classical
  rw [rightLeftOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, rightLeftOverlapPartner,
    pentagonRectangleWeight_recutRightEqLeft, Finset.sum_attach]

variable (x z) in
open scoped Classical in
/-- In an equation between the rectangle--pentagon sum and the pentagon--rectangle sum, each
augmented by further terms, the mixed `right = left` sources and their partners can be
removed. -/
theorem add_sum_rectanglePentagonWeight_eq_add_sum_iff_sdiff_rightLeftOverlap
    [IsCancelAdd R] (A B : MvPolynomial (Fin n) R) :
    A + ∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D =
        B + ∑ E ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R E ↔
      A + ∑ D ∈ G.rectanglePentagonDecompositions C x z \ G.rightLeftOverlapSources C x z,
          G.rectanglePentagonWeight C R D =
        B + ∑ E ∈ G.pentagonRectangleDecompositions C x z \ G.rightLeftOverlapPartners C x z,
          G.pentagonRectangleWeight C R E := by
  rw [← Finset.sum_sdiff (G.rightLeftOverlapSources_subset C)
      (f := G.rectanglePentagonWeight C R),
    ← Finset.sum_sdiff (G.rightLeftOverlapPartners_subset C)
      (f := G.pentagonRectangleWeight C R),
    G.sum_rectanglePentagonWeight_rightLeftOverlapSources_eq_sum_partners C x z R,
    ← add_assoc, ← add_assoc]
  exact add_right_cancel_iff

end TauCeti.GridDiagram
