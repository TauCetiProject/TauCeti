/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Abstract.Basic
public import Mathlib.Topology.CWComplex.Classical.Basic
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff
public import TauCeti.Topology.CWComplex.Classical.CWType
import TauCeti.Topology.CWComplex.Abstract.ClosureFinite
import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
import TauCeti.Topology.Category.TopCat.RelativeCellComplex

/-!
# Categorical relative CW complexes are classical relative CW complexes

A categorical relative CW complex `c : TopCat.RelativeCWComplex f` induces a classical structure
`c.toRelCWComplex : Topology.RelCWComplex Set.univ (Set.range f)` on its target. No separation
assumptions are needed. The cells in dimension `n` are exactly the cells attached at step `n`.
Their characteristic maps are the original cell inclusions, composed with the inverse of
`TauCeti.diskHomeomorphClosedBall`, the fixed radial comparison between the Euclidean disk and
the max-norm closed unit ball.

The construction uses the embeddings and disjointness of open cells, closure finiteness, and the
weak topology of categorical relative cell complexes. The equations below identify the classical
open and closed cells with the original inclusions, so the classical CW theory applies to spaces
constructed by categorical cell attachment. The stage formula in terms of closed cells needs no
separation assumption; identification with Mathlib's named `skeletonLT` requires a Hausdorff target,
as that classical subcomplex construction itself has this hypothesis.

For an absolute categorical CW complex `c : TopCat.CWComplex X` the base is empty, so `c` gives a
classical CW structure on `Set.univ` (`TopCat.CWComplex.toCWComplex`), and `X` has CW type
(`TopCat.CWComplex.cwType`).

## References

* A. Hatcher, *Algebraic Topology*, Appendix, Propositions A.1 and A.2.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press, 1990.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Metric Set
open HomotopicalAlgebra.RelativeCellComplex

universe u

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f)

private def cellMap (γ : c.Cells) (x : Fin γ.j → ℝ) : Y := by
  classical
  exact if hx : x ∈ closedBall 0 1 then
    γ.ι ((TauCeti.diskHomeomorphClosedBall γ.j).symm ⟨x, hx⟩)
  else γ.ι ((TauCeti.diskHomeomorphClosedBall γ.j).symm ⟨0, by simp⟩)

private lemma cellMap_apply (γ : c.Cells) (x : closedBall (0 : Fin γ.j → ℝ) 1) :
    c.cellMap γ x = γ.ι ((TauCeti.diskHomeomorphClosedBall γ.j).symm x) := by
  simp [cellMap, x.property]

private lemma cellMap_disk (γ : c.Cells) (z : 𝔻 γ.j) :
    c.cellMap γ (TauCeti.diskHomeomorphClosedBall γ.j z) = γ.ι z := by
  rw [c.cellMap_apply, Homeomorph.symm_apply_apply]

private lemma continuousOn_cellMap (γ : c.Cells) :
    ContinuousOn (c.cellMap γ) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (γ.ι.hom.continuous.comp (TauCeti.diskHomeomorphClosedBall γ.j).symm.continuous).congr
    fun x ↦ (c.cellMap_apply γ x).symm

private lemma cellMap_image_closedBall (γ : c.Cells) :
    c.cellMap γ '' closedBall 0 1 = range γ.ι := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (c.cellMap_apply γ ⟨x, hx⟩).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, (TauCeti.diskHomeomorphClosedBall γ.j z).property, c.cellMap_disk γ z⟩

private lemma cellMap_image_sphere (γ : c.Cells) :
    c.cellMap γ '' Metric.sphere 0 1 = range (diskBoundaryInclusion γ.j ≫ γ.ι) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let z := (TauCeti.diskHomeomorphClosedBall γ.j).symm ⟨x, sphere_subset_closedBall hx⟩
    obtain ⟨s, hs⟩ := (TauCeti.norm_diskHomeomorphClosedBall_eq_one_iff z).1
      (by simpa [z] using mem_sphere_zero_iff_norm.1 hx)
    exact ⟨s, by simpa only [ConcreteCategory.comp_apply, hs] using
      (c.cellMap_apply γ ⟨x, sphere_subset_closedBall hx⟩).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨_, mem_sphere_zero_iff_norm.2
      ((TauCeti.norm_diskHomeomorphClosedBall_eq_one_iff _).2 ⟨s, rfl⟩), ?_⟩
    exact c.cellMap_disk γ (diskBoundaryInclusion γ.j s)

private lemma cellMap_image_ball (γ : c.Cells) :
    c.cellMap γ '' Metric.ball 0 1 = γ.ι '' (range (diskBoundaryInclusion γ.j))ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let z := (TauCeti.diskHomeomorphClosedBall γ.j).symm ⟨x, ball_subset_closedBall hx⟩
    refine ⟨z, (TauCeti.diskHomeomorphClosedBall_mem_ball_iff z).1 ?_, (c.cellMap_apply γ _).symm⟩
    simpa [z] using hx
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, (TauCeti.diskHomeomorphClosedBall_mem_ball_iff z).2 hz, c.cellMap_disk γ z⟩

private lemma isEmbedding_cellMap (γ : c.Cells) :
    IsEmbedding ((Metric.ball (0 : Fin γ.j → ℝ) 1).domRestrict (c.cellMap γ)) := by
  let g : Metric.ball (0 : Fin γ.j → ℝ) 1 → ↥((range (diskBoundaryInclusion γ.j))ᶜ) := fun x ↦
    ⟨(TauCeti.diskHomeomorphClosedBall γ.j).symm ⟨x, ball_subset_closedBall x.property⟩,
      (TauCeti.diskHomeomorphClosedBall_mem_ball_iff _).1 (by simp)⟩
  have hg : IsEmbedding g := by
    exact ((TauCeti.diskHomeomorphClosedBall γ.j).symm.isEmbedding.comp
      (IsEmbedding.subtypeVal.codRestrict _ fun x ↦ ball_subset_closedBall x.property)).codRestrict
        _ (fun x ↦ (TauCeti.diskHomeomorphClosedBall_mem_ball_iff _).1 (by simp))
  have heq : (Metric.ball (0 : Fin γ.j → ℝ) 1).domRestrict (c.cellMap γ) =
      (range (diskBoundaryInclusion γ.j))ᶜ.domRestrict γ.ι ∘ g := by
    funext x
    exact c.cellMap_apply γ ⟨x, ball_subset_closedBall x.property⟩
  rw [heq]
  exact (c.isEmbedding_domRestrict_cells_ι γ).comp hg

private def cellPartialEquiv (γ : c.Cells) : PartialEquiv (Fin γ.j → ℝ) Y :=
  Set.InjOn.toPartialEquiv (c.cellMap γ) (Metric.ball 0 1) (by
    intro x hx y hy h
    exact congrArg Subtype.val ((c.isEmbedding_cellMap γ).injective
      (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h))

private lemma coe_cellPartialEquiv (γ : c.Cells) :
    (c.cellPartialEquiv γ : (Fin γ.j → ℝ) → Y) = c.cellMap γ :=
  rfl

private lemma continuousOn_cellPartialEquiv_symm (γ : c.Cells) :
    ContinuousOn (cellPartialEquiv c γ).symm (cellPartialEquiv c γ).target := by
  let e := cellPartialEquiv c γ
  let g : e.target → Metric.ball (0 : Fin γ.j → ℝ) 1 := fun y ↦
    ⟨e.symm y, e.map_target y.property⟩
  have hg : Continuous g := (c.isEmbedding_cellMap γ).continuous_iff.2 (by
    convert continuous_subtype_val using 1
    funext y
    exact e.right_inv y.property)
  exact continuousOn_iff_continuous_domRestrict.2 (continuous_subtype_val.comp hg)

private lemma cellMap_boundary_finite (γ : c.Cells) :
    ∃ I : ∀ n, Finset (c.attachCells n (not_isMax n)).ι,
      MapsTo (c.cellMap γ) (Metric.sphere 0 1)
        (range f ∪ ⋃ (n < γ.j) (i ∈ I n),
          c.cellMap ⟨n, not_isMax n, i⟩ '' closedBall 0 1) := by
  classical
  obtain ⟨s, hs, hsub⟩ := c.exists_finite_cells_boundary γ
  let cell (n : ℕ) (i : (c.attachCells n (not_isMax n)).ι) : c.Cells :=
    ⟨n, not_isMax n, i⟩
  have hi (n : ℕ) : Function.Injective (cell n) := by
    intro i j h
    cases h
    rfl
  refine ⟨fun n ↦ s.preimage (cell n) (hi n).injOn, ?_⟩
  intro x hx
  have hy := hsub ((c.cellMap_image_sphere γ).subset ⟨x, hx, rfl⟩)
  rcases hy with hy | hy
  · exact Or.inl hy
  · obtain ⟨δ, hδ, z, hz⟩ := mem_iUnion₂.1 hy
    obtain ⟨n, hn, i⟩ := δ
    exact Or.inr (mem_iUnion₂_of_mem (hs _ hδ)
      (mem_iUnion₂_of_mem (by simpa [cell] using hδ)
        ((c.cellMap_image_closedBall _).symm.subset ⟨z, hz⟩)))

/-- The classical relative CW structure on the target of a categorical relative CW complex.
The `n`-cells are those attached at step `n`, with their characteristic maps read through the
fixed radial identification of the max-norm ball with the Euclidean disk. -/
@[instance_reducible] def toRelCWComplex : Topology.RelCWComplex (univ : Set Y) (range f) where
  cell n := (c.attachCells n (not_isMax n)).ι
  map n i := cellPartialEquiv c ⟨n, not_isMax n, i⟩
  source_eq _ _ := rfl
  continuousOn n i := continuousOn_cellMap c ⟨n, not_isMax n, i⟩
  continuousOn_symm n i := continuousOn_cellPartialEquiv_symm c ⟨n, not_isMax n, i⟩
  pairwiseDisjoint' := by
    intro ni _ nj _ hne
    simp only [Function.onFun, c.coe_cellPartialEquiv]
    rw [c.cellMap_image_ball, c.cellMap_image_ball]
    exact c.disjoint_image_cells_ι (by
      intro h
      have hj := congrArg Cells.j h
      obtain ⟨n, i⟩ := ni
      obtain ⟨m, j⟩ := nj
      dsimp at hj
      subst m
      have hi : i = j := by cases h; rfl
      exact hne (by cases hi; rfl))
  disjointBase' n i := by
    rw [c.coe_cellPartialEquiv, c.cellMap_image_ball]
    exact (c.disjoint_range_image_cells_ι ⟨n, not_isMax n, i⟩).symm
  mapsTo n i := cellMap_boundary_finite c ⟨n, not_isMax n, i⟩
  closed' A _ h := by
    apply (c.isClosed_iff A).2
    refine ⟨?_, fun γ ↦ ?_⟩
    · have hpre := h.2.preimage f.hom.continuous
      simpa only [preimage_inter, preimage_range, inter_univ] using hpre
    · obtain ⟨n, hn, i⟩ := γ
      have hpre := (h.1 n i).preimage (Cells.ι (c := c) ⟨n, hn, i⟩).hom.continuous
      rw [c.coe_cellPartialEquiv, c.cellMap_image_closedBall] at hpre
      simpa only [preimage_inter, preimage_range, inter_univ] using hpre
  isClosedBase := c.isClosedEmbedding.isClosed_range
  union' := by
    simp only [c.coe_cellPartialEquiv, c.cellMap_image_closedBall]
    apply Set.eq_univ_of_forall
    intro y
    have hy := Set.eq_univ_iff_forall.1 c.range_union_iUnion_image_cells_ι y
    rcases hy with hy | hy
    · exact Or.inl hy
    · obtain ⟨γ, z, _, rfl⟩ := mem_iUnion.1 hy
      exact Or.inr (mem_iUnion_of_mem γ.j (mem_iUnion_of_mem γ.k ⟨z, rfl⟩))

/-- The cells in each dimension of the induced classical structure are the original attachment
indices. This equivalence identifies the carriers without unfolding the CW structure. -/
def toRelCWComplexCellEquiv (n : ℕ) :
    c.toRelCWComplex.cell n ≃ (c.attachCells n (not_isMax n)).ι :=
  Equiv.refl _

/-- The classical characteristic map on the closed ball is the original cell inclusion after
radial identification with the Euclidean disk. -/
@[simp] lemma toRelCWComplex_map_apply (n : ℕ) (i : c.toRelCWComplex.cell n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := c.toRelCWComplex
    Topology.RelCWComplex.map n i x =
      (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells).ι
        ((TauCeti.diskHomeomorphClosedBall n).symm x) :=
  c.cellMap_apply (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells) x

/-- Reading a classical characteristic map on the radially corresponding point of the disk
recovers the categorical cell inclusion. -/
-- Normalize before the coercion to coordinates erases the radial homeomorphism application.
@[simp↓] lemma toRelCWComplex_map_disk (n : ℕ) (i : c.toRelCWComplex.cell n) (z : 𝔻 n) :
    letI := c.toRelCWComplex
    Topology.RelCWComplex.map n i (TauCeti.diskHomeomorphClosedBall n z) =
      (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells).ι z :=
  c.cellMap_disk ⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ z

/-- The open cells of the induced classical structure are the original open cells. -/
lemma toRelCWComplex_openCell (n : ℕ) (i : c.toRelCWComplex.cell n) :
    letI := c.toRelCWComplex
    Topology.RelCWComplex.openCell (C := (univ : Set Y)) n i =
      (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells).ι ''
        (range (diskBoundaryInclusion n))ᶜ :=
  c.cellMap_image_ball (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells)

/-- The closed cells of the induced classical structure are the ranges of the original cell
inclusions. -/
lemma toRelCWComplex_closedCell (n : ℕ) (i : c.toRelCWComplex.cell n) :
    letI := c.toRelCWComplex
    Topology.RelCWComplex.closedCell (C := (univ : Set Y)) n i =
      range (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells).ι :=
  c.cellMap_image_closedBall (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells)

/-- The cell frontiers of the induced classical structure are the original boundary images. -/
lemma toRelCWComplex_cellFrontier (n : ℕ) (i : c.toRelCWComplex.cell n) :
    letI := c.toRelCWComplex
    Topology.RelCWComplex.cellFrontier (C := (univ : Set Y)) n i =
      range (diskBoundaryInclusion n ≫
        (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells).ι) :=
  c.cellMap_image_sphere (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells)

/-- The image of the `n`-th categorical stage is the base together with the induced classical
closed cells of dimension less than `n`. No separation hypothesis is needed. -/
lemma range_incl_app_eq_union_toRelCWComplex_closedCell (n : ℕ) :
    letI := c.toRelCWComplex
    range (c.incl.app n) = range f ∪ ⋃ (m < n) (i : c.toRelCWComplex.cell m),
      Topology.RelCWComplex.closedCell (C := (univ : Set Y)) m i := by
  let _ := c.toRelCWComplex
  rw [c.range_incl_app_eq_union_iUnion_range_cells_ι]
  congr 1
  ext y
  simp only [mem_iUnion, toRelCWComplex_closedCell]
  constructor
  · rintro ⟨⟨m, hm, i⟩, hmn, hy⟩
    refine ⟨m, hmn, (c.toRelCWComplexCellEquiv m).symm i, ?_⟩
    exact hy
  · rintro ⟨m, hmn, i, hy⟩
    exact ⟨⟨m, not_isMax m, c.toRelCWComplexCellEquiv m i⟩, hmn, hy⟩

/-- The image of the `n`-th categorical stage is the classical skeleton below dimension `n`.
The Hausdorff hypothesis is needed only to name Mathlib's classical `skeletonLT`. -/
lemma range_incl_app_eq_toRelCWComplex_skeletonLT [T2Space Y] (n : ℕ) :
    letI := c.toRelCWComplex
    range (c.incl.app n) =
      (Topology.RelCWComplex.skeletonLT (univ : Set Y) n : Set Y) := by
  let _ := c.toRelCWComplex
  rw [c.range_incl_app_eq_union_toRelCWComplex_closedCell,
    Topology.RelCWComplex.coe_skeletonLT]
  simp only [ENat.natCast_lt_natCast]

/-- Below the dimension of its lowest cells, the classical skeleton is the base: if no cells of
dimension less than `n` are attached, then `skeletonLT univ n` is the range of `f`. -/
lemma skeletonLT_toRelCWComplex_eq_range [T2Space Y] {n : ℕ}
    (hc : ∀ m < n, IsEmpty (c.attachCells m (not_isMax m)).ι) :
    letI := c.toRelCWComplex
    (Topology.RelCWComplex.skeletonLT (univ : Set Y) n : Set Y) = range f :=
  letI := c.toRelCWComplex
  TauCeti.skeletonLT_eq_base_of_isEmpty_cell (univ : Set Y) n fun m hm ↦
    (c.toRelCWComplexCellEquiv m).isEmpty_congr.2 (hc m hm)

end TopCat.RelativeCWComplex

namespace TopCat.CWComplex

variable {X : TopCat.{u}}

/-- The classical CW structure on a space with a categorical CW structure: the cells and
characteristic maps of the classical relative structure `c.toRelCWComplex`, whose base, the range
of the map out of the empty space, is empty. -/
@[instance_reducible] def toCWComplex (c : CWComplex X) : Topology.CWComplex (univ : Set X) :=
  letI := RelativeCWComplex.toRelCWComplex c
  have hD : range (initial.to X) = ∅ := range_eq_empty _
  { cell := Topology.RelCWComplex.cell (univ : Set X)
    map := Topology.RelCWComplex.map
    source_eq := Topology.RelCWComplex.source_eq
    continuousOn := Topology.RelCWComplex.continuousOn
    continuousOn_symm := Topology.RelCWComplex.continuousOn_symm
    pairwiseDisjoint' := Topology.RelCWComplex.pairwiseDisjoint'
    mapsTo' n i := by simpa [hD] using Topology.RelCWComplex.mapsTo (C := (univ : Set X)) n i
    closed' A hA h := Topology.RelCWComplex.closed' A hA ⟨h, by simp [hD]⟩
    union' := by simpa [hD] using Topology.RelCWComplex.union' (C := (univ : Set X)) }

/-- **A space with a categorical CW structure has CW type.** -/
theorem cwType (c : CWComplex X) : TauCeti.CWType X :=
  have := c.t2Space
  letI := c.toCWComplex
  TauCeti.CWType.of_cwComplex_univ X

end TopCat.CWComplex
