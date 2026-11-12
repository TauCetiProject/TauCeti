/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.Trans

import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# Attaching cells to a CW complex gives a CW complex

Let `c : TopCat.RelativeCWComplex f` be a categorical relative CW complex, so that `Y` is obtained
from `X` by attaching cells along `f : X ⟶ Y`, and let `X` carry a classical CW structure. If all
the cells of `X` have dimension less than some `N`, and `c` attaches no cells of dimension less
than `N`, then `Y` is a CW complex (`TopCat.RelativeCWComplex.cwComplexTrans`) when it is
Hausdorff. Its `m`-cells are the `m`-cells of `X`, included by `f`, together with the cells that
`c` attaches in dimension `m` (`TopCat.RelativeCWComplex.cwComplexTransCellEquiv`).

The structure combines the classical relative structure `c.toRelCWComplex` with the CW structure of
`X` carried to the range of the closed embedding `f`, by composing relative CW complexes
(`TauCeti.relCWComplexTrans`). The condition on dimensions guarantees the compatibility that
composition needs: the boundary of an attached `m`-cell meets the range of `f` inside its skeleton
below dimension `m`, which is all of it.

This is how spaces built from a CW complex by attaching cells of higher dimension, such as a
presentation complex built from a wedge of circles, or the colimit of a tower of cell attachments
killing homotopy groups, are read as CW complexes.

## Main definitions

* `TopCat.RelativeCWComplex.cwComplexTrans`: the CW structure on `Y`.
* `TopCat.RelativeCWComplex.cwComplexTransCellEquiv`: its `m`-cells are the `m`-cells of `X` and
  the cells attached in dimension `m`.

## Main results

* `TopCat.RelativeCWComplex.coe_map_cwComplexTransCellEquiv_symm_inl`,
  `TopCat.RelativeCWComplex.map_cwComplexTransCellEquiv_symm_inr`: the characteristic maps.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 for CW complexes built by attaching cells inductively.
-/

public section

noncomputable section

open CategoryTheory Topology Topology.RelCWComplex

universe u

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f) [T2Space Y]
  [Topology.CWComplex (Set.univ : Set X)] {N : ℕ}
  (hX : ∀ m, N ≤ m → IsEmpty (cell (Set.univ : Set X) m))
  (hc : ∀ m < N, IsEmpty (c.attachCells m (not_isMax m)).ι)

/-- The CW structure on `X`, carried to the range of `f`. -/
private abbrev rangeRelCWComplex : RelCWComplex (Set.range f) ∅ :=
  c.isClosedEmbedding.relCWComplex Set.image_univ (Set.image_empty _)

include hX hc in
/-- The part in the range of `f` of the boundary of an attached `m`-cell lies in the skeleton of
the range of `f` below dimension `m`: the attached cells have dimension at least `N`, and the
range of `f` has no cells of dimension at least `N`, so that skeleton is the whole range. -/
private lemma cellFrontier_inter_range_subset_skeletonLT :
    letI := c.rangeRelCWComplex
    letI := c.toRelCWComplex
    ∀ m (i : cell (Set.univ : Set Y) m),
      cellFrontier m i ∩ Set.range f ⊆ skeletonLT (Set.range f) m := by
  let := c.rangeRelCWComplex
  let := c.toRelCWComplex
  intro m i
  have hm : N ≤ m := by
    by_contra hm
    exact (hc m (Nat.lt_of_not_le hm)).false (c.toRelCWComplexCellEquiv m i)
  refine Set.inter_subset_right.trans
    (TauCeti.skeletonLT_eq_complex_of_isEmpty_cell _ m fun k hk ↦ ?_).superset
  exact (IsClosedEmbedding.relCWComplexCellEquiv _ _ _ k).isEmpty_congr.2 (hX k (hm.trans hk))

/-- **Attaching cells to a CW complex gives a CW complex.** If `X` is a CW complex all of whose
cells have dimension less than `N`, and the relative CW complex `c` attaches no cells of dimension
less than `N`, then the Hausdorff space `Y` is a CW complex. Its `m`-cells are the `m`-cells of
`X`, included by `f`, together with the cells attached in dimension `m`
(`TopCat.RelativeCWComplex.cwComplexTransCellEquiv`). -/
@[instance_reducible]
def cwComplexTrans : Topology.CWComplex (Set.univ : Set Y) :=
  letI := c.rangeRelCWComplex
  letI := c.toRelCWComplex
  letI := TauCeti.relCWComplexTrans Set.univ (Set.range f) ∅
    (c.cellFrontier_inter_range_subset_skeletonLT hX hc)
  RelCWComplex.toCWComplex _

/-- The `m`-cells of `TopCat.RelativeCWComplex.cwComplexTrans` are the `m`-cells of `X` together
with the cells attached in dimension `m`. -/
def cwComplexTransCellEquiv (m : ℕ) :
    @cell _ _ (Set.univ : Set Y) ∅ (c.cwComplexTrans hX hc).instRelCWComplex m ≃
      cell (Set.univ : Set X) m ⊕ (c.attachCells m (not_isMax m)).ι :=
  letI := c.rangeRelCWComplex
  letI := c.toRelCWComplex
  (TauCeti.relCWComplexTransCellEquiv (c.cellFrontier_inter_range_subset_skeletonLT hX hc)
      m).trans <|
    Equiv.sumCongr (IsClosedEmbedding.relCWComplexCellEquiv _ _ _ m) (c.toRelCWComplexCellEquiv m)

/-- The characteristic map of an `m`-cell of `X`, as a cell of
`TopCat.RelativeCWComplex.cwComplexTrans`, is its characteristic map in `X` followed by `f`. -/
@[simp]
lemma coe_map_cwComplexTransCellEquiv_symm_inl (m : ℕ) (i : cell (Set.univ : Set X) m) :
    ⇑(@map _ _ (Set.univ : Set Y) ∅ (c.cwComplexTrans hX hc).instRelCWComplex m
        ((c.cwComplexTransCellEquiv hX hc m).symm (.inl i))) = f ∘ map m i := by
  let := c.rangeRelCWComplex
  let := c.toRelCWComplex
  refine (congrArg (fun e : PartialEquiv _ _ ↦ ⇑e) (TauCeti.map_relCWComplexTrans_inl
    (c.cellFrontier_inter_range_subset_skeletonLT hX hc) m
      ((IsClosedEmbedding.relCWComplexCellEquiv _ _ _ m).symm i))).trans ?_
  rw [IsClosedEmbedding.coe_map_relCWComplex, Equiv.apply_symm_apply]

/-- The characteristic map of a cell attached in dimension `m`, as a cell of
`TopCat.RelativeCWComplex.cwComplexTrans`, is the inclusion of the attached disk, read on the
closed unit ball of the sup norm through the radial homeomorphism
`TauCeti.diskHomeomorphClosedBall`. -/
@[simp]
lemma map_cwComplexTransCellEquiv_symm_inr (m : ℕ) (i : (c.attachCells m (not_isMax m)).ι)
    (y : Metric.closedBall (0 : Fin m → ℝ) 1) :
    @map _ _ (Set.univ : Set Y) ∅ (c.cwComplexTrans hX hc).instRelCWComplex m
        ((c.cwComplexTransCellEquiv hX hc m).symm (.inr i)) y =
      (⟨m, not_isMax m, i⟩ : c.Cells).ι ((TauCeti.diskHomeomorphClosedBall m).symm y) := by
  let := c.rangeRelCWComplex
  let := c.toRelCWComplex
  refine (congrArg (fun e : PartialEquiv (Fin m → ℝ) Y ↦ e y)
    (TauCeti.map_relCWComplexTrans_inr (c.cellFrontier_inter_range_subset_skeletonLT hX hc) m
      ((c.toRelCWComplexCellEquiv m).symm i))).trans ?_
  rw [toRelCWComplex_map_apply, Equiv.apply_symm_apply]

end TopCat.RelativeCWComplex
