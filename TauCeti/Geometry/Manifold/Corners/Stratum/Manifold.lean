/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Corners.Stratum.Basic

import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Manifold structure on depth strata of a manifold with corners

Let `M` be a `C^n` manifold (`n ≠ 0`) modelled on a coordinate-region model with corners
`J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H` with
`range J = {z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}` (such as the quadrant `𝓡c m` with
`S = univ`, the half-space `𝓡∂ m` with `S = {0}`, or any finite product of such models via a
continuous linear equivalence).

Near a point `p ∈ J.depthStratum M k` of depth `k`, read through a preferred ambient chart `e` of
`M`, exactly `k` coordinates `i ∈ S` vanish at `e.extend J p` — forming a finite set `Z ⊆ S` of
cardinality `k` — while every other coordinate in `S` is strictly positive. Restricting `e` via
`OpenPartialHomeomorph.restrOpen` to the open slice
`U := {q ∈ e.source | ∀ j ∈ S, e.extend J p j ≠ 0 → 0 < e.extend J q j}`, any point
`q ∈ U ∩ J.depthStratum M k` has the same depth `k` as `p`, so by
`ModelWithCorners.depthAt_eq_iff_of_forall_pos` it vanishes on the exact same `k` coordinates `Z`.
Splitting `EuclideanSpace ℝ ι` along `Z` via `EuclideanSpace.coordSplitEquiv` and applying
`OpenPartialHomeomorph.subtypeCoord` gives a boundaryless chart on `U ∩ J.depthStratum M k` valued
in `EuclideanSpace ℝ (Fin (Fintype.card ι - k))`.

Here `J` ranges over arbitrary coordinate-region models over any finite index type `ι` (including
unordered index types such as `ι₁ ⊕ ι₂` arising from products). Because `hJ : range J = …` is a
propositional hypothesis (and for `J = 𝓡∂ (m + 1)` with `k = 1` the depth-one stratum coincides
with `(𝓡∂ (m + 1)).boundary M`), `ModelWithCorners.depthStratumChartedSpace` is intentionally
defined as an opaque (`@[irreducible]`), non-instance `def`.

## Main definitions

* `ModelWithCorners.depthStratumChartedSpace`: the canonical boundaryless charted-space structure on
  `↥(J.depthStratum M k)` modelled on `EuclideanSpace ℝ (Fin (Fintype.card ι - k))`.

## Main results

* `ModelWithCorners.card_filter_extChartAt_eq_of_mem_depthStratum`: a point `p` of the depth-`k`
  stratum has `k` coordinates in `S` vanishing at `extChartAt J p.val p.val`.
* `ModelWithCorners.depthStratumChartedSpace_atlas`,
  `ModelWithCorners.depthStratumChartedSpace_chartAt_source`,
  `ModelWithCorners.depthStratumChartedSpace_chartAt_target`,
  `ModelWithCorners.depthStratumChartedSpace_chartAt_apply`,
  `ModelWithCorners.depthStratumChartedSpace_chartAt_symm_apply`,
  `ModelWithCorners.extChartAt_depthStratumChartedSpace_chartAt_symm_apply`: characteristic lemmas
  for the atlas and preferred charts of `depthStratumChartedSpace`.
* `ModelWithCorners.isManifold_depthStratum`: `↥(J.depthStratum M k)` is a boundaryless `C^n`
  manifold of dimension `Fintype.card ι - k`.
* `ModelWithCorners.isImmersionOfComplement_subtypeVal_depthStratum`,
  `ModelWithCorners.isImmersion_subtypeVal_depthStratum`,
  `ModelWithCorners.isSmoothEmbedding_subtypeVal_depthStratum`: the inclusion
  `Subtype.val : ↥(J.depthStratum M k) → M` is a `C^n` immersion with complement
  `EuclideanSpace ℝ (Fin k)` and a `C^n` smooth embedding.
* `ModelWithCorners.mem_range_mfderiv_subtypeVal_depthStratum_iff`: characterization of the tangent
  space of `↥(J.depthStratum M k)` inside `TangentSpace J p.val` as the subspace where the
  coordinates in `S` vanishing at `extChartAt J p.val p.val` are zero.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (each depth stratum `S^k(X)` is a manifold without
  boundary of dimension `dim X - k`). [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
* Formal foundations and idioms in this library: `TauCeti.Geometry.Manifold.Corners.Depth`
  (intrinsic `depth` and `depthAt`), `TauCeti.Geometry.Manifold.Boundary.Charts` and
  `TauCeti.Topology.OpenPartialHomeomorph.Constructions` (`OpenPartialHomeomorph.subtypeCoord`
  chart pattern), `TauCeti.Geometry.Manifold.FiberProduct.Manifold` (opaque non-instance
  `ChartedSpace` idiom), and `TauCeti.Analysis.InnerProductSpace.PiL2`
  (`EuclideanSpace.coordSplitEquiv`).
-/

public section

noncomputable section

open Set Function Module Topology
open scoped Manifold ContDiff

namespace ModelWithCorners

section Charts

variable {ι : Type*} [Fintype ι] {H : Type*} [TopologicalSpace H]
  (J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H) {S : Set ι}
  {M : Type*} [TopologicalSpace M]

open Classical in
/-- The finite set of coordinates in `S` vanishing at `e.extend J x`. -/
private def vanishingFinset (S : Set ι) (e : OpenPartialHomeomorph M H) (x : M) : Finset ι :=
  Finset.univ.filter fun i ↦ i ∈ S ∧ e.extend J x i = 0

private theorem mem_vanishingFinset_iff {S : Set ι} {e : OpenPartialHomeomorph M H} {x : M}
    {i : ι} : i ∈ vanishingFinset J S e x ↔ i ∈ S ∧ e.extend J x i = 0 := by
  simp only [vanishingFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Restriction of an ambient chart `e` to the open slice around `x` where every coordinate in `S`
nonzero at `e.extend J x` stays strictly positive. -/
private def posSliceChart (S : Set ι) (e : OpenPartialHomeomorph M H) (x : M) :
    OpenPartialHomeomorph M H :=
  e.restrOpen {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j}
    (isOpen_setOf_forall_extend_pos J S e x)

private theorem posSliceChart_source (S : Set ι) (e : OpenPartialHomeomorph M H) (x : M) :
    (posSliceChart J S e x).source =
      {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} := by
  rw [posSliceChart, OpenPartialHomeomorph.restrOpen_source]
  exact inter_eq_right.2 fun _ hq ↦ hq.1

private theorem mem_posSliceChart_target (S : Set ι) (e : OpenPartialHomeomorph M H) (x : M)
    {h : H} :
    h ∈ (posSliceChart J S e x).target ↔
      h ∈ e.target ∧
        e.symm h ∈ {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} := by
  simp [posSliceChart, PartialEquiv.restr_target]

open Classical in
/-- Coordinatewise clamping onto `{z | ∀ i ∈ S, 0 ≤ z i}`. Because `J.symm` is only a right inverse
of `J` on `range J`, clamping before `J.symm` guarantees that the slice parametrization lands in
`range J` globally (playing the role of `(𝓡c m).symm`'s built-in `max · 0`), while agreeing with
the identity on `range J`. -/
private def coordClamp (S : Set ι) (z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if i ∈ S then max (z i) 0 else z i

private theorem coordClamp_mem_range (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    (z : EuclideanSpace ℝ ι) : coordClamp S z ∈ range J := by
  classical
  rw [hJ]
  intro i hi
  simp [coordClamp, hi]

private theorem coordClamp_eq_self (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {z : EuclideanSpace ℝ ι} (hz : z ∈ range J) : coordClamp S z = z := by
  classical
  rw [hJ] at hz
  ext i
  by_cases hi : i ∈ S
  · simp [coordClamp, hi, hz i hi]
  · simp [coordClamp, hi]

omit [Fintype ι] in
private theorem continuous_coordClamp (S : Set ι) : Continuous (coordClamp S) := by
  classical
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte]
    exact (PiLp.continuous_apply 2 _ i).max continuous_const
  · simp only [hi, ↓reduceIte]
    exact PiLp.continuous_apply 2 _ i

variable [ChartedSpace H M]

private theorem card_vanishingFinset [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.val ∈ e.source) :
    (vanishingFinset J S e p.val).card = k := by
  classical
  have hdepth : J.depthAt (e.extend J p.val) = k := by
    rw [depthAt_extend_eq_depth one_ne_zero he hp]
    exact mem_depthStratum.1 p.property
  have hmem : e.extend J p.val ∈ range J := by
    rw [OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hcard : (vanishingFinset J S e p.val).card =
      Nat.card {i : ι // i ∈ S ∧ e.extend J p.val i = 0} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact congrArg Finset.card (by
      ext i
      simp only [mem_vanishingFinset_iff, Finset.mem_filter, Finset.mem_univ, true_and])
  rw [hcard, ← depthAt_eq_natCard_of_range_eq hJ hmem]
  exact hdepth

open Classical in
/-- Splitting of `EuclideanSpace ℝ ι` tailored to the vanishing coordinates of `e.extend J p`. -/
private def chartSplitEquiv [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.val ∈ e.source) :
    (EuclideanSpace ℝ (Fin (Fintype.card ι - k)) × EuclideanSpace ℝ (Fin k)) ≃L[ℝ]
      EuclideanSpace ℝ ι :=
  EuclideanSpace.coordSplitEquiv ℝ (vanishingFinset J S e p.val)
    (card_vanishingFinset J hJ p he hp)

open Classical in
/-- Insertion of stratum coordinates outside `vanishingFinset J S e p.val`, zeroing those inside. -/
private def chartInsert [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.val ∈ e.source) :
    EuclideanSpace ℝ (Fin (Fintype.card ι - k)) →L[ℝ] EuclideanSpace ℝ ι :=
  EuclideanSpace.coordSplitInsert ℝ (vanishingFinset J S e p.val)
    (card_vanishingFinset J hJ p he hp)

open Classical in
/-- Projection onto the stratum coordinates outside `vanishingFinset J S e p.val`. -/
private def chartProj [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.val ∈ e.source) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι - k)) :=
  EuclideanSpace.coordSplitProj ℝ (vanishingFinset J S e p.val)
    (card_vanishingFinset J hJ p he hp)

/-- Slice parametrization in `H` for `OpenPartialHomeomorph.subtypeCoord`: insert zeros in the
vanishing coordinates, clamp onto `range J`, and apply `J.symm`. On the chart target this agrees
with `J.symm ∘ chartInsert`. -/
private def chartParam [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.val ∈ e.source) :
    EuclideanSpace ℝ (Fin (Fintype.card ι - k)) → H :=
  J.symm ∘ coordClamp S ∘ chartInsert J hJ p e he hp

private theorem chartInsert_pos_and_mem_range_of_mem_posSliceChart_target [IsManifold J 1 M]
    {hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}} {k : ℕ} {p : ↥(J.depthStratum M k)}
    {e : OpenPartialHomeomorph M H} {he : e ∈ IsManifold.maximalAtlas J 1 M}
    {hp : p.val ∈ e.source} {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : chartParam J hJ p e he hp y ∈ (posSliceChart J S e p.val).target) :
    (∀ j ∈ S, j ∉ vanishingFinset J S e p.val → 0 < chartInsert J hJ p e he hp y j) ∧
      chartInsert J hJ p e he hp y ∈ range J := by
  classical
  obtain ⟨hy₁, hy₂⟩ := (mem_posSliceChart_target J S e p.val).1 hy
  have hpos : ∀ j ∈ S, j ∉ vanishingFinset J S e p.val →
      0 < chartInsert J hJ p e he hp y j := fun j hj hjZ ↦ by
    have hne : e.extend J p.val j ≠ 0 := fun h0 ↦ hjZ ((mem_vanishingFinset_iff J).2 ⟨hj, h0⟩)
    have h := hy₂.2 j hj hne
    rw [OpenPartialHomeomorph.extend_coe, comp_apply, e.right_inv hy₁, chartParam, comp_apply,
      comp_apply, J.right_inv (coordClamp_mem_range J hJ _)] at h
    simp only [coordClamp, PiLp.toLp_apply, hj, ↓reduceIte] at h
    exact (lt_max_iff.1 h).resolve_right (lt_irrefl 0)
  refine ⟨hpos, ?_⟩
  rw [hJ]
  intro j hj
  by_cases hjZ : j ∈ vanishingFinset J S e p.val
  · rw [chartInsert, EuclideanSpace.coordSplitInsert_apply_of_mem y hjZ]
  · exact (hpos j hj hjZ).le

private theorem chartParam_eq_of_mem_posSliceChart_target [IsManifold J 1 M]
    {hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}} {k : ℕ} {p : ↥(J.depthStratum M k)}
    {e : OpenPartialHomeomorph M H} {he : e ∈ IsManifold.maximalAtlas J 1 M}
    {hp : p.val ∈ e.source} {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : chartParam J hJ p e he hp y ∈ (posSliceChart J S e p.val).target) :
    chartParam J hJ p e he hp y = J.symm (chartInsert J hJ p e he hp y) := by
  simp only [chartParam, comp_apply,
    coordClamp_eq_self J hJ (chartInsert_pos_and_mem_range_of_mem_posSliceChart_target J hy).2]

private theorem symm_chartParam_mem [IsManifold J 1 M]
    {hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}} {k : ℕ} {p : ↥(J.depthStratum M k)}
    {e : OpenPartialHomeomorph M H} {he : e ∈ IsManifold.maximalAtlas J 1 M}
    {hp : p.val ∈ e.source} {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : chartParam J hJ p e he hp y ∈ (posSliceChart J S e p.val).target) :
    (posSliceChart J S e p.val).symm (chartParam J hJ p e he hp y) ∈ J.depthStratum M k := by
  obtain ⟨hpos, hmem⟩ := chartInsert_pos_and_mem_range_of_mem_posSliceChart_target J hy
  have hy_e : J.symm (chartInsert J hJ p e he hp y) ∈ e.target :=
    chartParam_eq_of_mem_posSliceChart_target J hy ▸
      ((mem_posSliceChart_target J S e p.val).1 hy).1
  rw [posSliceChart, OpenPartialHomeomorph.coe_restrOpen_symm,
    chartParam_eq_of_mem_posSliceChart_target J hy]
  have hq_src : e.symm (J.symm (chartInsert J hJ p e he hp y)) ∈ e.source := e.map_target hy_e
  have hq_ext : e.extend J (e.symm (J.symm (chartInsert J hJ p e he hp y))) =
      chartInsert J hJ p e he hp y := by
    rw [OpenPartialHomeomorph.extend_coe, comp_apply, e.right_inv hy_e, J.right_inv hmem]
  rw [mem_depthStratum, ← depthAt_extend_eq_depth one_ne_zero he hq_src, hq_ext]
  have hdepth_p : J.depthAt (e.extend J p.val) = k := by
    rw [depthAt_extend_eq_depth one_ne_zero he hp]
    exact mem_depthStratum.1 p.property
  refine ((depthAt_eq_iff_of_forall_pos hJ
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _)
    hmem (fun j hj hne ↦ hpos j hj ?_)).2 fun j hj h0 ↦ ?_).trans hdepth_p
  · rw [mem_vanishingFinset_iff]
    exact fun h ↦ hne h.2
  · classical
    exact EuclideanSpace.coordSplitInsert_apply_of_mem y ((mem_vanishingFinset_iff J).2 ⟨hj, h0⟩)

private theorem extend_eq_zero_of_mem_posSlice [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.val ∈ e.source) {q : ↥(J.depthStratum M k)}
    (hq : q.val ∈ {q ∈ e.source | ∀ j ∈ S, e.extend J p.val j ≠ 0 → 0 < e.extend J q j}) :
    ∀ i ∈ vanishingFinset J S e p.val, e.extend J q.val i = 0 := fun i hi ↦ by
  have hi' := (mem_vanishingFinset_iff J).1 hi
  have heq : J.depthAt (e.extend J q.val) = J.depthAt (e.extend J p.val) := by
    rw [depthAt_extend_eq_depth one_ne_zero he hq.1,
      depthAt_extend_eq_depth one_ne_zero he hp,
      mem_depthStratum.1 q.property, mem_depthStratum.1 p.property]
  exact (depthAt_eq_iff_of_forall_pos hJ
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _)
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _) hq.2).1 heq i hi'.1 hi'.2

private theorem chartParam_chartProj [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.val ∈ e.source) {x : M}
    (hx : x ∈ (posSliceChart J S e p.val).source) (hxs : x ∈ J.depthStratum M k) :
    chartParam J hJ p e he hp
        ((chartProj J hJ p e he hp ∘ J) (posSliceChart J S e p.val x)) =
      posSliceChart J S e p.val x := by
  classical
  rw [posSliceChart_source] at hx
  have h_ins_eq : chartInsert J hJ p e he hp (chartProj J hJ p e he hp (e.extend J x)) =
      e.extend J x :=
    EuclideanSpace.coordSplitInsert_proj
      (extend_eq_zero_of_mem_posSlice J hJ p e he hp (q := ⟨x, hxs⟩) hx)
  change J.symm (coordClamp S
      (chartInsert J hJ p e he hp (chartProj J hJ p e he hp (e.extend J x)))) = e x
  rw [h_ins_eq, coordClamp_eq_self J hJ
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _),
    OpenPartialHomeomorph.extend_coe, comp_apply, J.left_inv]

private theorem leftInvOn_chartProj_chartParam [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.val ∈ e.source) :
    LeftInvOn (chartProj J hJ p e he hp ∘ J) (chartParam J hJ p e he hp)
      (chartParam J hJ p e he hp ⁻¹' (posSliceChart J S e p.val).target) := by
  classical
  intro y hy
  rw [mem_preimage] at hy
  rw [comp_apply, chartParam_eq_of_mem_posSliceChart_target J hy,
    J.right_inv (chartInsert_pos_and_mem_range_of_mem_posSliceChart_target J hy).2,
    chartProj, chartInsert, EuclideanSpace.coordSplitProj_insert]

private theorem continuous_chartParam [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.val ∈ e.source) :
    Continuous (chartParam J hJ p e he hp) :=
  J.continuous_symm.comp ((continuous_coordClamp S).comp (chartInsert J hJ p e he hp).continuous)

private theorem continuous_chartProj_comp [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.val ∈ e.source) :
    Continuous (chartProj J hJ p e he hp ∘ J) :=
  (chartProj J hJ p e he hp).continuous.comp J.continuous

/-- On a `C^1` manifold `M` modelled on `range J = {z | ∀ i ∈ S, 0 ≤ z i}`, an ambient chart `e`
containing `p ∈ J.depthStratum M k` induces a chart on `↥(J.depthStratum M k)` valued in
`EuclideanSpace ℝ (Fin (Fintype.card ι - k))` by restricting `e` to the positive slice around `p`
and applying `OpenPartialHomeomorph.subtypeCoord` to delete the `k` coordinates in `S` vanishing at
`e.extend J p`. -/
private def depthStratumChart [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.val ∈ e.source) :
    OpenPartialHomeomorph ↥(J.depthStratum M k) (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) :=
  (posSliceChart J S e p.val).subtypeCoord (J.depthStratum M k) ⟨p⟩
    (chartParam J hJ p e he hp) (chartProj J hJ p e he hp ∘ J)
    (fun hy ↦ symm_chartParam_mem J hy)
    (fun hx hxs ↦ chartParam_chartProj J hJ p e he hp hx hxs)
    (leftInvOn_chartProj_chartParam J hJ p e he hp)
    (continuous_chartParam J hJ p e he hp)
    (continuous_chartProj_comp J hJ p e he hp).continuousOn

section ChartLemmas

variable [IsManifold J 1 M] {hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}} {k : ℕ}
  {p : ↥(J.depthStratum M k)} {e : OpenPartialHomeomorph M H}
  {he : e ∈ IsManifold.maximalAtlas J 1 M} {hp : p.val ∈ e.source}

private theorem depthStratumChart_source :
    (depthStratumChart J hJ p e he hp).source =
      Subtype.val ⁻¹' {q ∈ e.source | ∀ j ∈ S, e.extend J p.val j ≠ 0 → 0 < e.extend J q j} := by
  rw [← posSliceChart_source J S e p.val, depthStratumChart]
  exact OpenPartialHomeomorph.subtypeCoord_source ..

private theorem depthStratumChart_target :
    (depthStratumChart J hJ p e he hp).target =
      chartParam J hJ p e he hp ⁻¹' (posSliceChart J S e p.val).target := by
  rw [depthStratumChart]
  exact OpenPartialHomeomorph.subtypeCoord_target ..

private theorem depthStratumChart_apply (q : ↥(J.depthStratum M k)) :
    depthStratumChart J hJ p e he hp q = chartProj J hJ p e he hp (e.extend J q.val) := by
  change depthStratumChart J hJ p e he hp q =
    (chartProj J hJ p e he hp ∘ J) (posSliceChart J S e p.val q.val)
  rw [depthStratumChart]
  exact OpenPartialHomeomorph.subtypeCoord_apply ..

private theorem chartInsert_mem_of_mem_depthStratumChart_target
    {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : y ∈ (depthStratumChart J hJ p e he hp).target) :
    J.symm (chartInsert J hJ p e he hp y) ∈ e.target ∧
      chartInsert J hJ p e he hp y ∈ range J := by
  rw [depthStratumChart_target, mem_preimage] at hy
  exact ⟨chartParam_eq_of_mem_posSliceChart_target J hy ▸
      ((mem_posSliceChart_target J S e p.val).1 hy).1,
    (chartInsert_pos_and_mem_range_of_mem_posSliceChart_target J hy).2⟩

private theorem coe_depthStratumChart_symm_apply
    {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : y ∈ (depthStratumChart J hJ p e he hp).target) :
    ((depthStratumChart J hJ p e he hp).symm y : M) =
      e.symm (J.symm (chartInsert J hJ p e he hp y)) := by
  rw [depthStratumChart_target, mem_preimage] at hy
  rw [← chartParam_eq_of_mem_posSliceChart_target J hy]
  change ((depthStratumChart J hJ p e he hp).symm y : M) =
    (posSliceChart J S e p.val).symm (chartParam J hJ p e he hp y)
  rw [depthStratumChart]
  exact OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ _ hy

private theorem contDiffOn_depthStratumChart_symm_trans {n : ℕ∞ω} [IsManifold J n M]
    (p q : ↥(J.depthStratum M k))
    {e₁ e₂ : OpenPartialHomeomorph M H}
    (he₁ : e₁ ∈ atlas H M) (he₂ : e₂ ∈ atlas H M)
    (hp : p.val ∈ e₁.source) (hq : q.val ∈ e₂.source) :
    ContDiffOn ℝ n
      ((depthStratumChart J hJ p e₁ (IsManifold.subset_maximalAtlas he₁) hp).symm ≫ₕ
        depthStratumChart J hJ q e₂ (IsManifold.subset_maximalAtlas he₂) hq)
      ((depthStratumChart J hJ p e₁ (IsManifold.subset_maximalAtlas he₁) hp).symm ≫ₕ
        depthStratumChart J hJ q e₂ (IsManifold.subset_maximalAtlas he₂) hq).source := by
  let c₁ := depthStratumChart J hJ p e₁ (IsManifold.subset_maximalAtlas he₁) hp
  let c₂ := depthStratumChart J hJ q e₂ (IsManifold.subset_maximalAtlas he₂) hq
  let ins₁ := chartInsert J hJ p e₁ (IsManifold.subset_maximalAtlas he₁) hp
  let proj₂ := chartProj J hJ q e₂ (IsManifold.subset_maximalAtlas he₂) hq
  have hg : e₁.symm ≫ₕ e₂ ∈ contDiffGroupoid n J :=
    StructureGroupoid.compatible (contDiffGroupoid n J) he₁ he₂
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  have hG : ContDiffOn ℝ n (J ∘ (e₁.symm ≫ₕ e₂) ∘ J.symm)
      (J.symm ⁻¹' (e₁.symm ≫ₕ e₂).source ∩ range J) := hg.1
  have hmap : MapsTo ins₁ (c₁.symm ≫ₕ c₂).source
      (J.symm ⁻¹' (e₁.symm ≫ₕ e₂).source ∩ range J) := fun y hy ↦ by
    have hy₁ : y ∈ c₁.target := hy.1
    obtain ⟨hy_e₁, hmem⟩ := chartInsert_mem_of_mem_depthStratumChart_target J hy₁
    have hy₂ : c₁.symm y ∈ c₂.source := by
      simpa only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
        OpenPartialHomeomorph.symm_symm] using hy.2
    rw [depthStratumChart_source] at hy₂
    refine ⟨⟨hy_e₁, ?_⟩, hmem⟩
    simp only [OpenPartialHomeomorph.symm_symm, mem_preimage]
    rw [← coe_depthStratumChart_symm_apply J hy₁]
    exact hy₂.1
  refine (proj₂.contDiff.comp_contDiffOn (hG.comp ins₁.contDiff.contDiffOn hmap)).congr
    fun y hy ↦ ?_
  have hy₁ : y ∈ c₁.target := hy.1
  simp only [OpenPartialHomeomorph.coe_trans, comp_apply, depthStratumChart_apply, ins₁, proj₂,
    OpenPartialHomeomorph.extend_coe]
  rw [coe_depthStratumChart_symm_apply J hy₁]

end ChartLemmas

end Charts

/-! ### Charted space and smooth manifold structure on depth strata -/

section ManifoldStructure

variable {ι : Type*} [Fintype ι] {H : Type*} [TopologicalSpace H]
  (J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H) {S : Set ι}
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

variable {J M} in
open Classical in
/-- On a `C^1` manifold modelled on `{z | ∀ i ∈ S, 0 ≤ z i}`, a point `p` of the depth-`k` stratum
has `k` coordinates in `S` vanishing at `extChartAt J p.val p.val`. -/
theorem card_filter_extChartAt_eq_of_mem_depthStratum [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k)) :
    (Finset.univ.filter fun i ↦ i ∈ S ∧ extChartAt J p.val p.val i = 0).card = k :=
  card_vanishingFinset J hJ p (IsManifold.chart_mem_maximalAtlas p.val) (mem_chart_source H p.val)

/-- The canonical boundaryless charted-space structure on the depth-`k` stratum
`↥(J.depthStratum M k)` of a `C^1` manifold `M` modelled on a coordinate region
`range J = {z | ∀ i ∈ S, 0 ≤ z i}`. Its atlas consists of the charts induced by the preferred
ambient charts of `M`.

This definition is intentionally not a global `instance` (because `hJ` is a propositional
hypothesis and to avoid typeclass diamonds with `TauCeti.boundaryChartedSpace`) and is marked
`@[irreducible]`; use `depthStratumChartedSpace_atlas`, `depthStratumChartedSpace_chartAt_source`,
`depthStratumChartedSpace_chartAt_target`, `depthStratumChartedSpace_chartAt_apply`, and
`depthStratumChartedSpace_chartAt_symm_apply` to reason about it. -/
@[irreducible]
def depthStratumChartedSpace [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) ↥(J.depthStratum M k) where
  atlas := range fun p : ↥(J.depthStratum M k) ↦
    depthStratumChart J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
      (mem_chart_source H p.val)
  chartAt := fun p ↦
    depthStratumChart J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
      (mem_chart_source H p.val)
  mem_chart_source p := by
    rw [depthStratumChart_source]
    exact mem_setOf_forall_extend_pos_self hJ (mem_chart_source H p.val)
  chart_mem_atlas p := mem_range_self p

private theorem depthStratumChartedSpace_chartAt [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k)) :
    (J.depthStratumChartedSpace M hJ k).chartAt p =
      depthStratumChart J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
        (mem_chart_source H p.val) := by
  unfold depthStratumChartedSpace
  rfl

/-- The atlas of `depthStratumChartedSpace` is the range of its preferred charts. -/
theorem depthStratumChartedSpace_atlas [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    (J.depthStratumChartedSpace M hJ k).atlas =
      range (J.depthStratumChartedSpace M hJ k).chartAt := by
  unfold depthStratumChartedSpace
  rfl

/-- The source of the preferred stratum chart at `p` consists of the depth-`k` points in the ambient
chart source at `p` where every coordinate in `S` nonzero at `p` remains strictly positive. -/
theorem depthStratumChartedSpace_chartAt_source [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k)) :
    ((J.depthStratumChartedSpace M hJ k).chartAt p).source =
      Subtype.val ⁻¹' {q ∈ (chartAt H p.val).source |
        ∀ j ∈ S, extChartAt J p.val p.val j ≠ 0 → 0 < extChartAt J p.val q j} := by
  rw [depthStratumChartedSpace_chartAt, depthStratumChart_source]
  rfl

open Classical in
/-- The target of the preferred chart of `depthStratumChartedSpace` at `p` consists of the vectors
whose zero-insertion outside the `k` coordinates in `S` vanishing at `p` lies in the target of
`extChartAt J p.val` and has strictly positive coordinates on the remaining indices of `S`. -/
theorem depthStratumChartedSpace_chartAt_target [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k)) :
    ((J.depthStratumChartedSpace M hJ k).chartAt p).target =
      {w | EuclideanSpace.coordSplitInsert ℝ
          (Finset.univ.filter fun i ↦ i ∈ S ∧ extChartAt J p.val p.val i = 0)
          (card_filter_extChartAt_eq_of_mem_depthStratum hJ p) w ∈
            (extChartAt J p.val).target ∧
        ∀ j ∈ S, extChartAt J p.val p.val j ≠ 0 →
          0 < EuclideanSpace.coordSplitInsert ℝ
            (Finset.univ.filter fun i ↦ i ∈ S ∧ extChartAt J p.val p.val i = 0)
            (card_filter_extChartAt_eq_of_mem_depthStratum hJ p) w j} := by
  ext w
  rw [depthStratumChartedSpace_chartAt, depthStratumChart_target]
  simp only [mem_preimage, mem_ofPred_eq]
  refine ⟨fun hw ↦ ?_, fun ⟨hw_ext, hpos⟩ ↦ ?_⟩
  · have hw_tgt : w ∈ (depthStratumChart J hJ p (chartAt H p.val)
        (IsManifold.chart_mem_maximalAtlas p.val) (mem_chart_source H p.val)).target := by
      rw [depthStratumChart_target]
      exact hw
    obtain ⟨hy_e, hmem⟩ := chartInsert_mem_of_mem_depthStratumChart_target J hw_tgt
    have hpos := (chartInsert_pos_and_mem_range_of_mem_posSliceChart_target J hw).1
    refine ⟨?_, fun j hj hne ↦ hpos j hj fun hZ ↦ hne ((mem_vanishingFinset_iff J).1 hZ).2⟩
    rw [extChartAt_target]
    exact ⟨hy_e, hmem⟩
  · rw [extChartAt_target] at hw_ext
    have hins : EuclideanSpace.coordSplitInsert ℝ
        (Finset.univ.filter fun i ↦ i ∈ S ∧ extChartAt J p.val p.val i = 0)
        (card_filter_extChartAt_eq_of_mem_depthStratum hJ p) =
          chartInsert J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
            (mem_chart_source H p.val) := rfl
    rw [hins] at hw_ext hpos
    refine (mem_posSliceChart_target J S (chartAt H p.val) p.val).2 ?_
    simp only [chartParam, comp_apply, coordClamp_eq_self J hJ hw_ext.2]
    refine ⟨hw_ext.1, (chartAt H p.val).map_target hw_ext.1, fun j hj hne ↦ ?_⟩
    rw [OpenPartialHomeomorph.extend_coe, comp_apply, (chartAt H p.val).right_inv hw_ext.1,
      J.right_inv hw_ext.2]
    exact hpos j hj hne

open Classical in
/-- The preferred chart of `depthStratumChartedSpace` at `p` reads `q` through `extChartAt J p.val`
and projects off the `k` coordinates in `S` vanishing at `p`. -/
theorem depthStratumChartedSpace_chartAt_apply [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p q : ↥(J.depthStratum M k)) :
    (J.depthStratumChartedSpace M hJ k).chartAt p q =
      EuclideanSpace.coordSplitProj ℝ
        (Finset.univ.filter fun i ↦ i ∈ S ∧ extChartAt J p.val p.val i = 0)
        (card_filter_extChartAt_eq_of_mem_depthStratum hJ p)
        (extChartAt J p.val q.val) := by
  rw [depthStratumChartedSpace_chartAt, depthStratumChart_apply]
  rfl

open Classical in
/-- On its target, the inverse of the preferred chart of `depthStratumChartedSpace` at `p` inserts
zeros in the `k` coordinates in `S` vanishing at `p` and applies `(extChartAt J p.val).symm`. -/
theorem depthStratumChartedSpace_chartAt_symm_apply [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k))
    {w : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hw : w ∈ ((J.depthStratumChartedSpace M hJ k).chartAt p).target) :
    (((J.depthStratumChartedSpace M hJ k).chartAt p).symm w : M) =
      (extChartAt J p.val).symm (EuclideanSpace.coordSplitInsert ℝ
        (Finset.univ.filter fun i ↦ i ∈ S ∧ extChartAt J p.val p.val i = 0)
        (card_filter_extChartAt_eq_of_mem_depthStratum hJ p) w) := by
  rw [depthStratumChartedSpace_chartAt] at hw ⊢
  rw [coe_depthStratumChart_symm_apply J hw, extChartAt_coe_symm, comp_apply]
  rfl

open Classical in
/-- Reading the inverse of the preferred chart of `depthStratumChartedSpace` at `p` through
`extChartAt J p.val` gives the zero-insertion outside the `k` coordinates in `S` vanishing at
`p`. -/
theorem extChartAt_depthStratumChartedSpace_chartAt_symm_apply [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k))
    {w : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hw : w ∈ ((J.depthStratumChartedSpace M hJ k).chartAt p).target) :
    extChartAt J p.val (((J.depthStratumChartedSpace M hJ k).chartAt p).symm w : M) =
      EuclideanSpace.coordSplitInsert ℝ
        (Finset.univ.filter fun i ↦ i ∈ S ∧ extChartAt J p.val p.val i = 0)
        (card_filter_extChartAt_eq_of_mem_depthStratum hJ p) w := by
  have hw' := hw
  rw [depthStratumChartedSpace_chartAt_target, mem_ofPred_eq] at hw'
  rw [depthStratumChartedSpace_chartAt_symm_apply J M hJ k p hw,
    (extChartAt J p.val).right_inv hw'.1]

variable {n : ℕ∞ω} [IsManifold J n M]

/-- **Each depth stratum of a `C^n` manifold with corners (`n ≠ 0`) is a boundaryless `C^n`
manifold** of dimension `Fintype.card ι - k`, modelled on
`EuclideanSpace ℝ (Fin (Fintype.card ι - k))`. -/
theorem isManifold_depthStratum (hn : n ≠ 0) (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) n ↥(J.depthStratum M k) := by
  intro _ _
  refine isManifold_of_contDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) n
    ↥(J.depthStratum M k) ?_
  have hatlas : atlas (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) ↥(J.depthStratum M k) =
      range fun p : ↥(J.depthStratum M k) ↦
        chartAt (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p :=
    depthStratumChartedSpace_atlas J M hJ k
  intro f₁ f₂ hf₁ hf₂
  rw [hatlas] at hf₁ hf₂
  obtain ⟨p, rfl⟩ := hf₁
  obtain ⟨q, rfl⟩ := hf₂
  have hp_ch : chartAt (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p =
      depthStratumChart J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
        (mem_chart_source H p.val) :=
    depthStratumChartedSpace_chartAt J M hJ k p
  have hq_ch : chartAt (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) q =
      depthStratumChart J hJ q (chartAt H q.val) (IsManifold.chart_mem_maximalAtlas q.val)
        (mem_chart_source H q.val) :=
    depthStratumChartedSpace_chartAt J M hJ k q
  dsimp only
  rw [hp_ch, hq_ch]
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id,
    range_id, preimage_id_eq, id_eq, inter_univ] using
    contDiffOn_depthStratumChart_symm_trans J p q (chart_mem_atlas H p.val)
      (chart_mem_atlas H q.val) (mem_chart_source H p.val) (mem_chart_source H q.val)

/-- The inclusion of a depth stratum `↥(J.depthStratum M k) → M` is a `C^n` immersion with
complement `EuclideanSpace ℝ (Fin k)`. -/
theorem isImmersionOfComplement_subtypeVal_depthStratum (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    Manifold.IsImmersionOfComplement (EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J n
      (Subtype.val : ↥(J.depthStratum M k) → M) := by
  intro _ _
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) n ↥(J.depthStratum M k) :=
    J.isManifold_depthStratum M hn hJ k
  intro p
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    continuous_subtypeVal.continuousAt
    (chartSplitEquiv J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
      (mem_chart_source H p.val)) ?_
  intro y hy
  have hy' : y ∈ ((J.depthStratumChartedSpace M hJ k).chartAt p).target := by
    rw [extChartAt_target] at hy
    simpa only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq] using hy.1
  have hsymm : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p).symm y =
      ((J.depthStratumChartedSpace M hJ k).chartAt p).symm y := by
    simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, comp_id]
  simp only [comp_apply, hsymm]
  exact (extChartAt_depthStratumChartedSpace_chartAt_symm_apply J M hJ k p hy').trans
    (by
      classical
      exact EuclideanSpace.coordSplitInsert_apply y)

/-- The inclusion of a depth stratum `↥(J.depthStratum M k) → M` is a `C^n` immersion. -/
theorem isImmersion_subtypeVal_depthStratum (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J n
      (Subtype.val : ↥(J.depthStratum M k) → M) := by
  intro _ _
  exact (J.isImmersionOfComplement_subtypeVal_depthStratum M hn hJ k).isImmersion

/-- The inclusion of a depth stratum `↥(J.depthStratum M k) → M` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_depthStratum (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J n
      (Subtype.val : ↥(J.depthStratum M k) → M) := by
  intro _ _
  exact ⟨J.isImmersion_subtypeVal_depthStratum M hn hJ k, IsEmbedding.subtypeVal⟩

private theorem hasMFDerivAt_subtypeVal_depthStratum [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k)) :
    let _ := J.depthStratumChartedSpace M hJ k
    let E₀ := EuclideanSpace ℝ (Fin (Fintype.card ι - k))
    let L := chartInsert J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
      (mem_chart_source H p.val)
    HasMFDerivAt 𝓘(ℝ, E₀) J (Subtype.val : ↥(J.depthStratum M k) → M) p
      ((tangentSpaceCastModel J p.val).symm.toContinuousLinearMap.comp
        (L.comp (tangentSpaceCastModel 𝓘(ℝ, E₀) p).toContinuousLinearMap)) := by
  intro _
  let E₀ := EuclideanSpace ℝ (Fin (Fintype.card ι - k))
  let L := chartInsert J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
    (mem_chart_source H p.val)
  refine ⟨continuous_subtypeVal.continuousAt, ?_⟩
  have hcast :
      (tangentSpaceCastModel J p.val : _ →L[ℝ] EuclideanSpace ℝ ι) ∘L
        ((tangentSpaceCastModel J p.val).symm.toContinuousLinearMap.comp
          (L.comp (tangentSpaceCastModel 𝓘(ℝ, E₀) p).toContinuousLinearMap)) ∘L
        ((tangentSpaceCastModel 𝓘(ℝ, E₀) p).symm : E₀ →L[ℝ] _) = L := by
    ext u
    simp
  rw [hcast]
  have hp_tgt : extChartAt 𝓘(ℝ, E₀) p p ∈ ((J.depthStratumChartedSpace M hJ k).chartAt p).target :=
    (chartAt E₀ p).map_source (mem_chart_source E₀ p)
  have heq : writtenInExtChartAt 𝓘(ℝ, E₀) J p (Subtype.val : ↥(J.depthStratum M k) → M) =ᶠ[
      𝓝[range 𝓘(ℝ, E₀)] (extChartAt 𝓘(ℝ, E₀) p p)] L := by
    filter_upwards [nhdsWithin_le_nhds ((chartAt E₀ p).open_target.mem_nhds hp_tgt)] with y hy
    have hsymm : (extChartAt 𝓘(ℝ, E₀) p).symm y =
        ((J.depthStratumChartedSpace M hJ k).chartAt p).symm y := by
      simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, comp_id]
    simp only [writtenInExtChartAt, comp_apply, hsymm]
    exact extChartAt_depthStratumChartedSpace_chartAt_symm_apply J M hJ k p hy
  have hx : writtenInExtChartAt 𝓘(ℝ, E₀) J p (Subtype.val : ↥(J.depthStratum M k) → M)
      (extChartAt 𝓘(ℝ, E₀) p p) = L (extChartAt 𝓘(ℝ, E₀) p p) :=
    heq.self_of_nhdsWithin (by simp)
  exact L.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq hx

/-- Tangent space characterization of a depth stratum: a tangent vector `v : TangentSpace J p.val`
lies in the image of the differential of `Subtype.val : ↥(J.depthStratum M k) → M` at `p` exactly
when its model coordinates vanish along every coordinate `i ∈ S` that vanishes at
`extChartAt J p.val p.val`. -/
theorem mem_range_mfderiv_subtypeVal_depthStratum_iff (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k))
    (v : TangentSpace J p.val) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    v ∈ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J
      (Subtype.val : ↥(J.depthStratum M k) → M) p).range ↔
      ∀ i ∈ S, extChartAt J p.val p.val i = 0 → tangentSpaceCastModel J p.val v i = 0 := by
  intro _ _
  classical
  let L := chartInsert J hJ p (chartAt H p.val) (IsManifold.chart_mem_maximalAtlas p.val)
    (mem_chart_source H p.val)
  rw [(hasMFDerivAt_subtypeVal_depthStratum J M hJ k p).mfderiv]
  constructor
  · rintro ⟨w, hw⟩ i hi h0
    have hmem : tangentSpaceCastModel J p.val v ∈ L.range := by
      refine ⟨tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p w, ?_⟩
      rw [← hw]
      simp [L]
    exact (EuclideanSpace.mem_range_coordSplitInsert_iff _).1 hmem i
      ((mem_vanishingFinset_iff J).2 ⟨hi, h0⟩)
  · intro hv
    have hmem : tangentSpaceCastModel J p.val v ∈ L.range :=
      (EuclideanSpace.mem_range_coordSplitInsert_iff _).2 fun i hi ↦
        have hi' := (mem_vanishingFinset_iff J).1 hi
        hv i hi'.1 hi'.2
    obtain ⟨u, hu⟩ := hmem
    refine ⟨(tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p).symm u, ?_⟩
    simpa [L] using (tangentSpaceCastModel J p.val).symm_apply_eq.2 hu

end ManifoldStructure

end ModelWithCorners
