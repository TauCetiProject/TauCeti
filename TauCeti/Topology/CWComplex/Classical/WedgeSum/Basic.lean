/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.Zero
public import TauCeti.Topology.WedgeSum

/-!
# The CW structure on a wedge sum of CW complexes

Let `X i` be a family of CW complexes whose base points `x i` are `0`-cells. The wedge sum
`⋁ᵢ X i` is again a CW complex (`TauCeti.WedgeSum.cwComplex`, an instance). Its cells are the
wedge point, a `0`-cell, together with the cells of the summands other than their base points
(`TauCeti.WedgeSum.Cell`, through `TauCeti.WedgeSum.cellEquiv`). The characteristic map of a cell of
`X i` is followed by the inclusion of `X i` (`TauCeti.WedgeSum.coe_map_inclCell`). There is no
finiteness hypothesis on the family, and the wedge sum of the empty family is a point.

The hypothesis that `x i` is a `0`-cell is the class argument
`Fact (x i ∈ skeletonLT (univ : Set (X i)) 1)`, so that the structure is an instance. The wedge
point is then a `0`-cell of the wedge sum (`TauCeti.WedgeSum.base_mem_skeletonLT_one`), so wedge
sums of such wedge sums carry the same structure.

Every cell `j` of a summand `X i`, including its base cell, gives the cell
`TauCeti.WedgeSum.inclCell x i j` of the wedge sum, whose open and closed cells are the images of
those of `j`. These cells make each summand a subcomplex (`TauCeti.WedgeSum.summandSubcomplex`).

The summands are closed in the wedge sum (`TauCeti.WedgeSum.isClosedEmbedding_incl`), so the
characteristic maps of the summand cells, followed by the inclusions, keep their continuity
properties. The weak topology of the wedge sum is its quotient topology, in which a set is closed
as soon as its trace on every summand is (`TauCeti.WedgeSum.isClosed_iff`).

## Main definitions

* `TauCeti.WedgeSum.Cell`: the cells of the wedge sum.
* `TauCeti.WedgeSum.cwComplex`: the CW structure on the wedge sum.
* `TauCeti.WedgeSum.cellEquiv`: the cells of this structure are `TauCeti.WedgeSum.Cell`.
* `TauCeti.WedgeSum.inclCell`: the cell of the wedge sum containing a cell of a summand.
* `TauCeti.WedgeSum.summandSubcomplex`: a summand, as a subcomplex of the wedge sum.

## Main results

* `TauCeti.WedgeSum.coe_map_inclCell`, `TauCeti.WedgeSum.openCell_inclCell`,
  `TauCeti.WedgeSum.closedCell_inclCell`, `TauCeti.WedgeSum.cellFrontier_inclCell`: the
  characteristic map, open cell, closed cell and frontier of the cell containing a cell of a
  summand are those of the summand cell, followed by the inclusion.
* `TauCeti.WedgeSum.openCell_cellEquiv_symm_base`,
  `TauCeti.WedgeSum.closedCell_cellEquiv_symm_base`: the cell `TauCeti.WedgeSum.Cell.base` is the
  wedge point.
* `TauCeti.WedgeSum.base_mem_skeletonLT_one`: the wedge point is a `0`-cell.
* `TauCeti.WedgeSum.coe_summandSubcomplex`: the subcomplex of a summand is its image.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the wedge sum of cell complexes in "Operations on Spaces" (p. 10).
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace WedgeSum

variable {ι : Type u} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ i, CWComplex (univ : Set (X i))]

variable (x : ∀ i, X i) in
/-- The cells of the wedge sum of the CW complexes `X i` at the `0`-cells `x i`: the wedge point,
which is a `0`-cell, and every cell of a summand whose open cell does not contain the base point,
that is every cell of a summand other than its base point. -/
inductive Cell : ℕ → Type u
  /-- The wedge point, a `0`-cell. -/
  | base : Cell 0
  /-- A cell of the summand `X i` other than its base point. -/
  | incl {n : ℕ} (i : ι) (j : cell (univ : Set (X i)) n) (hj : x i ∉ openCell n j) : Cell n

variable [∀ i, T2Space (X i)] {x : ∀ i, X i}

/-- The CW structure of a summand, carried to its image in the wedge sum. -/
private abbrev summandCW (x : ∀ i, X i) (i : ι) :
    RelCWComplex (incl x i '' univ) (incl x i '' ∅) :=
  (isClosedEmbedding_incl (fun _ => isClosed_singleton) i).relCWComplex rfl rfl

/-- A cell of a summand, as a cell of its image in the wedge sum. -/
private def summandCell (x : ∀ i, X i) (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) :
    @cell _ _ _ _ (summandCW x i) n :=
  ((isClosedEmbedding_incl (fun _ => isClosed_singleton) i).relCWComplexCellEquiv rfl rfl n).symm j

/-- The characteristic map of a cell of the wedge sum. -/
private def cellMap (x : ∀ i, X i) : ∀ {n : ℕ}, Cell x n → PartialEquiv (Fin n → ℝ) (WedgeSum x)
  | _, .base => PartialEquiv.single 0 (base x)
  | n, .incl i j _ => @map _ _ _ _ (summandCW x i) n (summandCell x i j)

private lemma coe_cellMap_incl {n : ℕ} (i : ι) (j : cell (univ : Set (X i)) n)
    (hj : x i ∉ openCell n j) : ⇑(cellMap x (.incl i j hj)) = incl x i ∘ map n j := by
  rw [cellMap, IsClosedEmbedding.coe_map_relCWComplex, summandCell, Equiv.apply_symm_apply]

private lemma image_cellMap_incl {n : ℕ} (i : ι) (j : cell (univ : Set (X i)) n)
    (hj : x i ∉ openCell n j) (S : Set (Fin n → ℝ)) :
    cellMap x (.incl i j hj) '' S = incl x i '' (map n j '' S) := by
  rw [coe_cellMap_incl, image_comp]

private lemma image_cellMap_base {S : Set (Fin 0 → ℝ)} (hS : S.Nonempty) :
    cellMap x .base '' S = {base x} :=
  hS.image_const _

private lemma source_cellMap {n : ℕ} (c : Cell x n) : (cellMap x c).source = ball 0 1 := by
  cases c with
  | base =>
    ext y
    simp [cellMap, Subsingleton.elim y 0]
  | incl i j hj => exact @source_eq _ _ _ _ (summandCW x i) _ (summandCell x i j)

private lemma continuousOn_cellMap {n : ℕ} (c : Cell x n) :
    ContinuousOn (cellMap x c) (closedBall 0 1) := by
  cases c with
  | base => exact continuousOn_const
  | incl i j hj => exact @RelCWComplex.continuousOn _ _ _ _ (summandCW x i) _ (summandCell x i j)

private lemma continuousOn_cellMap_symm {n : ℕ} (c : Cell x n) :
    ContinuousOn (cellMap x c).symm (cellMap x c).target := by
  cases c with
  | base => exact continuousOn_const
  | incl i j hj =>
    exact @RelCWComplex.continuousOn_symm _ _ _ _ (summandCW x i) _ (summandCell x i j)

private lemma pairwiseDisjoint_cellMap :
    (univ : Set (Σ n, Cell x n)).PairwiseDisjoint fun c => cellMap x c.2 '' ball 0 1 := by
  rintro ⟨n, c⟩ - ⟨m, d⟩ - hne
  simp only [Function.onFun]
  cases c with
  | base =>
    cases d with
    | base => exact absurd rfl hne
    | incl i j hj =>
      rw [image_cellMap_base ⟨0, mem_ball_self one_pos⟩, image_cellMap_incl]
      refine disjoint_singleton_left.2 fun ⟨y, hy, hyb⟩ => hj ?_
      exact incl_eq_base_iff.1 hyb ▸ hy
  | incl i j hj =>
    rw [image_cellMap_incl]
    cases d with
    | base =>
      rw [image_cellMap_base ⟨0, mem_ball_self one_pos⟩]
      refine disjoint_singleton_right.2 fun ⟨y, hy, hyb⟩ => hj ?_
      exact incl_eq_base_iff.1 hyb ▸ hy
    | incl i' j' hj' =>
      rw [image_cellMap_incl]
      refine disjoint_left.2 ?_
      rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
      rcases incl_eq_incl_iff.1 hyy' with ⟨rfl, -⟩ | h
      · exact hj' hy'
      · obtain ⟨rfl, h⟩ := Sigma.mk.inj h
        obtain rfl := eq_of_heq h
        obtain h := eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨_, hy, hy'⟩)
        obtain ⟨rfl, h⟩ := Sigma.mk.inj h
        obtain rfl := eq_of_heq h
        exact hne rfl

variable [∀ i, Fact (x i ∈ skeletonLT (univ : Set (X i)) 1)]

variable (x) in
open Classical in
/-- The cell of the wedge sum containing the open cell `j` of the summand `X i`. -/
private def toCell (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) : Cell x n :=
  if h : x i ∈ openCell n j then
    (eq_zero_of_mem_skeletonLT_one_of_mem_openCell Fact.out h).symm ▸ .base
  else .incl i j h

private lemma toCell_of_notMem {i : ι} {n : ℕ} {j : cell (univ : Set (X i)) n}
    (hj : x i ∉ openCell n j) : toCell x i j = .incl i j hj := by
  simp [toCell, hj]

private lemma toCell_of_mem {i : ι} {j : cell (univ : Set (X i)) 0} (hj : x i ∈ openCell 0 j) :
    toCell x i j = .base := by
  simp [toCell, hj]

/-- The characteristic map of a cell of a summand, followed by the inclusion, is the
characteristic map of a cell of the wedge sum; for the base cell, both are constant at the wedge
point. -/
private lemma coe_cellMap_toCell (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) :
    ⇑(cellMap x (toCell x i j)) = incl x i ∘ map n j := by
  by_cases hj : x i ∈ openCell n j
  · obtain rfl := eq_zero_of_mem_skeletonLT_one_of_mem_openCell Fact.out hj
    rw [toCell_of_mem hj]
    rw [openCell_zero_eq_singleton, mem_singleton_iff] at hj
    funext y
    simp [cellMap, Subsingleton.elim y ![], ← hj]
  · rw [toCell_of_notMem hj, coe_cellMap_incl]

private lemma mapsTo_cellMap {n : ℕ} (c : Cell x n) :
    ∃ I : ∀ m, Finset (Cell x m),
      MapsTo (cellMap x c) (sphere 0 1)
        (⋃ (m < n) (d ∈ I m), cellMap x d '' closedBall 0 1) := by
  classical
  cases c with
  | base =>
    exact ⟨fun _ => ∅, fun y hy => ((sphere_eq_empty_of_subsingleton one_ne_zero).subset hy).elim⟩
  | incl i j hj =>
    obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n j
    refine ⟨fun m => (I m).image (toCell x i), fun y hy => ?_⟩
    obtain ⟨m, hmn, k, hk, hyk⟩ :
        ∃ m < n, ∃ k ∈ I m, map n j y ∈ closedCell m k := by
      simpa using hI (mem_image_of_mem _ hy)
    refine mem_iUnion₂.2 ⟨m, hmn, mem_iUnion₂.2 ⟨toCell x i k, Finset.mem_image_of_mem _ hk, ?_⟩⟩
    rw [coe_cellMap_toCell, image_comp, coe_cellMap_incl]
    exact mem_image_of_mem _ hyk

private lemma isClosed_of_cellMap {A : Set (WedgeSum x)}
    (hA : ∀ n (c : Cell x n), IsClosed (A ∩ cellMap x c '' closedBall 0 1)) : IsClosed A := by
  refine isClosed_iff.2 fun i => (CWComplex.closed (univ : Set (X i)) _ (subset_univ _)).2
    fun n j => ?_
  have h := (hA n (toCell x i j)).preimage (incl x i).continuous
  rwa [coe_cellMap_toCell, image_comp, preimage_inter, (incl_injective i).preimage_image] at h

private lemma iUnion_cellMap :
    ⋃ (n : ℕ) (c : Cell x n), cellMap x c '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun w => ?_
  induction w using WedgeSum.ind with
  | base => exact mem_iUnion₂.2 ⟨0, .base, 0, by simp, rfl⟩
  | incl i y =>
    obtain ⟨n, j, hy⟩ := mem_iUnion₂.1 ((CWComplex.union (C := (univ : Set (X i)))).symm ▸
      mem_univ y)
    refine mem_iUnion₂.2 ⟨n, toCell x i j, ?_⟩
    rw [coe_cellMap_toCell, image_comp]
    exact mem_image_of_mem _ hy

/-- **The CW structure on a wedge sum.** When the base point of every CW complex `X i` is a
`0`-cell, the wedge sum `⋁ᵢ X i` is a CW complex whose cells are the wedge point and the cells of
the summands other than their base points (`TauCeti.WedgeSum.Cell`, through
`TauCeti.WedgeSum.cellEquiv`), with the characteristic maps of the summands followed by the
inclusions (`TauCeti.WedgeSum.coe_map_inclCell`). -/
@[instance_reducible]
def cwComplex : CWComplex (univ : Set (WedgeSum x)) where
  cell := Cell x
  map _ := cellMap x
  source_eq _ := source_cellMap
  continuousOn _ := continuousOn_cellMap
  continuousOn_symm _ := continuousOn_cellMap_symm
  pairwiseDisjoint' := pairwiseDisjoint_cellMap
  mapsTo' _ := mapsTo_cellMap
  closed' _ _ := isClosed_of_cellMap
  union' := iUnion_cellMap

attribute [instance] cwComplex

variable (x) in
/-- The `n`-cells of the wedge sum are the wedge point, when `n = 0`, and the `n`-cells of the
summands other than their base points. -/
def cellEquiv (n : ℕ) : cell (univ : Set (WedgeSum x)) n ≃ Cell x n :=
  Equiv.refl _

variable (x) in
/-- The cell of the wedge sum containing the open cell `j` of the summand `X i`: the wedge point
when `j` is the base point of `X i`, and `j` itself otherwise. -/
def inclCell (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) : cell (univ : Set (WedgeSum x)) n :=
  (cellEquiv x n).symm (toCell x i j)

/-- A cell of a summand other than its base point is a cell of the wedge sum. -/
@[simp]
lemma cellEquiv_symm_incl {n : ℕ} (i : ι) (j : cell (univ : Set (X i)) n)
    (hj : x i ∉ openCell n j) : (cellEquiv x n).symm (.incl i j hj) = inclCell x i j :=
  (congrArg _ (toCell_of_notMem hj)).symm

/-- The base cell of a summand is carried to the wedge point. -/
lemma inclCell_of_mem {i : ι} {j : cell (univ : Set (X i)) 0} (hj : x i ∈ openCell 0 j) :
    inclCell x i j = (cellEquiv x 0).symm .base :=
  congrArg _ (toCell_of_mem hj)

/-- **The characteristic maps of the wedge sum.** The characteristic map of the cell of the wedge
sum containing a cell of a summand is the characteristic map of that cell, followed by the
inclusion of the summand. -/
@[simp]
theorem coe_map_inclCell (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) :
    ⇑(map n (inclCell x i j)) = incl x i ∘ map n j :=
  coe_cellMap_toCell i j

/-- The characteristic map of the wedge point is constant. -/
@[simp]
theorem map_cellEquiv_symm_base (y : Fin 0 → ℝ) : map 0 ((cellEquiv x 0).symm .base) y = base x :=
  (rfl)

/-- The open cell containing a cell of a summand is the image of its open cell. -/
@[simp]
theorem openCell_inclCell (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) :
    openCell n (inclCell x i j) = incl x i '' openCell n j := by
  rw [openCell, coe_map_inclCell, image_comp, openCell]

/-- The closed cell containing a cell of a summand is the image of its closed cell. -/
@[simp]
theorem closedCell_inclCell (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) :
    closedCell n (inclCell x i j) = incl x i '' closedCell n j := by
  rw [closedCell, coe_map_inclCell, image_comp, closedCell]

/-- The frontier of the cell containing a cell of a summand is the image of its frontier. -/
@[simp]
theorem cellFrontier_inclCell (i : ι) {n : ℕ} (j : cell (univ : Set (X i)) n) :
    cellFrontier n (inclCell x i j) = incl x i '' cellFrontier n j := by
  rw [cellFrontier, coe_map_inclCell, image_comp, cellFrontier]

/-- The closed cell `TauCeti.WedgeSum.Cell.base` is the wedge point. -/
@[simp]
theorem closedCell_cellEquiv_symm_base : closedCell 0 ((cellEquiv x 0).symm .base) = {base x} := by
  simp [closedCell_zero_eq_singleton]

/-- The open cell `TauCeti.WedgeSum.Cell.base` is the wedge point. -/
@[simp]
theorem openCell_cellEquiv_symm_base : openCell 0 ((cellEquiv x 0).symm .base) = {base x} := by
  simp [openCell_zero_eq_singleton]

/-- The wedge point is a `0`-cell of the wedge sum. -/
theorem base_mem_skeletonLT_one : base x ∈ skeletonLT (univ : Set (WedgeSum x)) 1 :=
  CWComplex.mem_skeletonLT_iff.2 ⟨0, by simp, (cellEquiv x 0).symm .base, by simp⟩

/-- The wedge point is a `0`-cell, so wedge sums of wedge sums carry the CW structure of wedge
sums. -/
instance : Fact (base x ∈ skeletonLT (univ : Set (WedgeSum x)) 1) :=
  ⟨base_mem_skeletonLT_one⟩

variable (x) in
/-- **The summands are subcomplexes.** The `i`-th summand of the wedge sum, as a subcomplex: its
cells are the cells of the wedge sum containing the cells of `X i`. -/
def summandSubcomplex (i : ι) : CWComplex.Subcomplex (univ : Set (WedgeSum x)) :=
  CWComplex.Subcomplex.mk' _ (range (incl x i)) (fun n => range (inclCell x i (n := n)))
    (by
      rintro n ⟨_, j, rfl⟩
      rw [closedCell_inclCell]
      exact image_subset_range _ _)
    (by
      have h := congrArg (incl x i '' ·)
        (CWComplex.iUnion_openCell_eq_complex (C := (univ : Set (X i))))
      simp only [image_iUnion, image_univ] at h
      rw [← h]
      refine iUnion_congr fun n => ?_
      rw [iUnion_subtype, biUnion_range]
      simp)

/-- The subcomplex of the `i`-th summand is its image in the wedge sum. -/
@[simp]
theorem coe_summandSubcomplex (i : ι) :
    (summandSubcomplex x i : Set (WedgeSum x)) = range (incl x i) :=
  (rfl)

/-- The cells of the subcomplex of the `i`-th summand are those containing the cells of `X i`. -/
@[simp]
theorem summandSubcomplex_I (i : ι) (n : ℕ) :
    (summandSubcomplex x i).I n = range (inclCell x i (n := n)) :=
  (rfl)

end WedgeSum

end TauCeti
