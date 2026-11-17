/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Corners.Stratum.Basic

import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Manifold structure on depth strata of a manifold with corners

Let `M` be a `C^n` manifold (`n ≠ 0`) modelled on a coordinate-region model with corners
`J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H` with
`range J = {z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}` (such as the quadrant `𝓡c m` with
`S = univ`, the half-space `𝓡∂ m` with `S = {0}`, or any finite product of such models via a
continuous linear equivalence).

Near a point `p ∈ J.depthStratum M k` of depth `k`, read through a preferred ambient chart `e` of
`M`, exactly `k` coordinates `i ∈ S` vanish at `e.extend J p` — forming a finite set `Z ⊆ S` of
cardinality `k` — while every other coordinate in `S` is strictly positive. On the open
neighborhood `U := {q ∈ e.source | ∀ j ∈ S, e.extend J p j ≠ 0 → 0 < e.extend J q j}` of `p`, any
point `q ∈ U ∩ J.depthStratum M k` has the same depth `k` as `p`, so by
`ModelWithCorners.depthAt_eq_iff_of_forall_pos` it must vanish on the exact same `k` coordinates
`Z`. Splitting `EuclideanSpace ℝ ι` into the coordinates outside `Z` (dimension
`Fintype.card ι - k`) and the coordinates in `Z` (dimension `k`), projection onto the coordinates
outside `Z` gives a boundaryless chart on `U ∩ J.depthStratum M k` valued in
`EuclideanSpace ℝ (Fin (Fintype.card ι - k))`, with inverse given by inserting zeros in `Z` and
applying `e.symm ∘ J.symm`.

The charted-space structure `ModelWithCorners.depthStratumChartedSpace` is intentionally defined as
an opaque (`@[irreducible]`), non-instance `def` to avoid typeclass diamonds with
`TauCeti.boundaryChartedSpace` and because `hJ : range J = ...` is a propositional hypothesis.

## Main definitions

* `ModelWithCorners.depthStratumChartedSpace`: the canonical boundaryless charted-space structure on
  `↥(J.depthStratum M k)` modelled on `EuclideanSpace ℝ (Fin (Fintype.card ι - k))`.

## Main results

* `ModelWithCorners.depthStratumChartedSpace_atlas`,
  `ModelWithCorners.depthStratumChartedSpace_chartAt_source`: characteristic lemmas for the atlas
  and preferred chart sources of `depthStratumChartedSpace`.
* `ModelWithCorners.isManifold_depthStratum`: `↥(J.depthStratum M k)` is a boundaryless `C^n`
  manifold of dimension `Fintype.card ι - k`.
* `ModelWithCorners.isImmersionOfComplement_subtypeVal_depthStratum`,
  `ModelWithCorners.isImmersion_subtypeVal_depthStratum`,
  `ModelWithCorners.isSmoothEmbedding_subtypeVal_depthStratum`: the inclusion
  `Subtype.val : ↥(J.depthStratum M k) → M` is a `C^n` immersion with complement
  `EuclideanSpace ℝ (Fin k)` and a `C^n` smooth embedding.
* `ModelWithCorners.contMDiff_subtypeVal_depthStratum`,
  `ModelWithCorners.mdifferentiable_subtypeVal_depthStratum`,
  `ModelWithCorners.injective_mfderiv_subtypeVal_depthStratum`: regularity and injectivity of the
  differential of the stratum inclusion.
* `ModelWithCorners.mem_range_mfderiv_subtypeVal_depthStratum_iff`: characterization of the tangent
  space of `↥(J.depthStratum M k)` inside `TangentSpace J p.1` as the subspace where the coordinates
  in `S` vanishing at `extChartAt J p.1 p.1` are zero.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (each depth stratum `S^k(X)` is a manifold without
  boundary of dimension `dim X - k`). [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
* Formal foundations and idioms in this library: `TauCeti.Geometry.Manifold.Corners.Depth`
  (intrinsic `depth` and `depthAt`), `TauCeti.Geometry.Manifold.Boundary.Charts` (local chart
  construction and immersion pattern for boundary manifolds),
  `TauCeti.Geometry.Manifold.FiberProduct.Manifold` (opaque non-instance `ChartedSpace` idiom),
  and `TauCeti.Analysis.InnerProductSpace.PiL2` (`EuclideanSpace.sumComplEquivProd`).
-/

public section

noncomputable section

open Set Function Module Topology
open scoped Manifold ContDiff

namespace ModelWithCorners

section CoordSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- Splitting `EuclideanSpace ℝ ι` into the coordinates outside a `k`-element finset `Z` (indexed
by `Fin (Fintype.card ι - k)`) and the coordinates inside `Z` (indexed by `Fin k`).

Because `Fintype.equivFinOfCardEq` chooses an arbitrary non-canonical bijection, this helper is
intentionally local to `depthStratumChart`: its only role is to give every depth-`k` stratum chart
the uniform model space `EuclideanSpace ℝ (Fin (Fintype.card ι - k))` on top of the canonical
splitting `EuclideanSpace.sumComplEquivProd`. -/
private def coordSplitEquiv (Z : Finset ι) (hcard : Z.card = k) :
    (EuclideanSpace ℝ (Fin (Fintype.card ι - k)) × EuclideanSpace ℝ (Fin k)) ≃L[ℝ]
      EuclideanSpace ℝ ι :=
  let hcardIn : Fintype.card {i : ι // i ∈ Z} = k := by
    rw [Fintype.card_coe, hcard]
  let hcardOut : Fintype.card {i : ι // i ∉ Z} = Fintype.card ι - k := by
    rw [Fintype.card_subtype_compl (· ∈ Z), Fintype.card_coe, hcard]
  let σ : Fin (Fintype.card ι - k) ≃ {i : ι // i ∉ Z} :=
    (Fintype.equivFinOfCardEq hcardOut).symm
  let τ : Fin k ≃ {i : ι // i ∈ Z} :=
    (Fintype.equivFinOfCardEq hcardIn).symm
  let eOut : EuclideanSpace ℝ (Fin (Fintype.card ι - k)) ≃L[ℝ]
      EuclideanSpace ℝ {i : ι // i ∉ Z} :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toContinuousLinearEquiv
  let eIn : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ {i : ι // i ∈ Z} :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ τ).toContinuousLinearEquiv
  ((eOut.prodCongr eIn).trans (ContinuousLinearEquiv.prodComm ℝ _ _)).trans
    (EuclideanSpace.sumComplEquivProd ℝ (· ∈ Z)).symm

/-- Linear insertion of coordinates outside `Z`, setting every coordinate in `Z` to `0`. -/
private def coordSplitInsert (Z : Finset ι) (hcard : Z.card = k) :
    EuclideanSpace ℝ (Fin (Fintype.card ι - k)) →L[ℝ] EuclideanSpace ℝ ι :=
  (coordSplitEquiv Z hcard).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

/-- Linear projection onto the coordinates outside `Z`. -/
private def coordSplitProj (Z : Finset ι) (hcard : Z.card = k) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι - k)) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (coordSplitEquiv Z hcard).symm.toContinuousLinearMap

private theorem coordSplitInsert_apply (Z : Finset ι) (hcard : Z.card = k)
    (y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))) :
    coordSplitInsert Z hcard y = coordSplitEquiv Z hcard (y, 0) :=
  rfl

private theorem coordSplitProj_apply (Z : Finset ι) (hcard : Z.card = k)
    (z : EuclideanSpace ℝ ι) :
    coordSplitProj Z hcard z = ((coordSplitEquiv Z hcard).symm z).1 :=
  rfl

private theorem coordSplitProj_insert (Z : Finset ι) (hcard : Z.card = k)
    (y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))) :
    coordSplitProj Z hcard (coordSplitInsert Z hcard y) = y := by
  simp [coordSplitProj_apply, coordSplitInsert_apply]

private theorem coordSplitInsert_apply_of_mem (Z : Finset ι) (hcard : Z.card = k)
    (y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))) {i : ι} (hi : i ∈ Z) :
    coordSplitInsert Z hcard y i = 0 := by
  simp only [coordSplitInsert_apply, coordSplitEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodComm_apply, ContinuousLinearEquiv.prodCongr_apply, Prod.swap_prod_mk,
    map_zero, EuclideanSpace.sumComplEquivProd_symm_apply, dite_eq_left hi, PiLp.zero_apply]

private theorem coordSplitEquiv_symm_snd_eq_zero_iff (Z : Finset ι) (hcard : Z.card = k)
    (z : EuclideanSpace ℝ ι) :
    ((coordSplitEquiv Z hcard).symm z).2 = 0 ↔ ∀ i ∈ Z, z i = 0 := by
  have hfst : ((coordSplitEquiv Z hcard).symm z).2 = 0 ↔
      (EuclideanSpace.sumComplEquivProd ℝ (· ∈ Z) z).1 = 0 := by
    simp only [coordSplitEquiv, ContinuousLinearEquiv.symm_trans_apply,
      ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.prodComm_symm,
      ContinuousLinearEquiv.prodComm_apply, ContinuousLinearEquiv.prodCongr_symm,
      ContinuousLinearEquiv.prodCongr_apply, Prod.snd_swap,
      ContinuousLinearEquiv.map_eq_zero_iff]
  rw [hfst]
  constructor
  · intro h i hi
    simpa [EuclideanSpace.sumComplEquivProd_apply_fst] using
      congrArg (fun u : EuclideanSpace ℝ {j : ι // j ∈ Z} ↦ u ⟨i, hi⟩) h
  · intro h
    ext ⟨i, hi⟩
    simpa [EuclideanSpace.sumComplEquivProd_apply_fst] using h i hi

private theorem coordSplitInsert_proj (Z : Finset ι) (hcard : Z.card = k)
    {z : EuclideanSpace ℝ ι} (hz : ∀ i ∈ Z, z i = 0) :
    coordSplitInsert Z hcard (coordSplitProj Z hcard z) = z := by
  have h2 : ((coordSplitEquiv Z hcard).symm z).2 = 0 :=
    (coordSplitEquiv_symm_snd_eq_zero_iff Z hcard z).2 hz
  rw [coordSplitInsert_apply, coordSplitProj_apply, ← h2, Prod.mk.eta,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem mem_range_coordSplitInsert_iff (Z : Finset ι) (hcard : Z.card = k)
    (w : EuclideanSpace ℝ ι) :
    w ∈ (coordSplitInsert Z hcard).range ↔ ∀ i ∈ Z, w i = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ i hi
    exact coordSplitInsert_apply_of_mem Z hcard y hi
  · intro hw
    exact ⟨coordSplitProj Z hcard w, coordSplitInsert_proj Z hcard hw⟩

end CoordSplit

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

variable [ChartedSpace H M]

private theorem card_vanishingFinset [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.1 ∈ e.source) :
    (vanishingFinset J S e p.1).card = k := by
  classical
  have hdepth : J.depthAt (e.extend J p.1) = k := by
    rw [depthAt_extend_eq_depth one_ne_zero he hp]
    exact mem_depthStratum_iff.1 p.2
  have hmem : e.extend J p.1 ∈ range J := by
    rw [OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hcard : (vanishingFinset J S e p.1).card =
      Nat.card {i : ι // i ∈ S ∧ e.extend J p.1 i = 0} := by
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
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.1 ∈ e.source) :
    (EuclideanSpace ℝ (Fin (Fintype.card ι - k)) × EuclideanSpace ℝ (Fin k)) ≃L[ℝ]
      EuclideanSpace ℝ ι :=
  coordSplitEquiv (vanishingFinset J S e p.1) (card_vanishingFinset J hJ p he hp)

open Classical in
/-- Insertion of stratum coordinates outside `vanishingFinset J S e p.1`, zeroing those inside. -/
private def chartInsert [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.1 ∈ e.source) :
    EuclideanSpace ℝ (Fin (Fintype.card ι - k)) →L[ℝ] EuclideanSpace ℝ ι :=
  coordSplitInsert (vanishingFinset J S e p.1) (card_vanishingFinset J hJ p he hp)

open Classical in
/-- Projection onto the stratum coordinates outside `vanishingFinset J S e p.1`. -/
private def chartProj [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.1 ∈ e.source) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι - k)) :=
  coordSplitProj (vanishingFinset J S e p.1) (card_vanishingFinset J hJ p he hp)

/-- Target open set of the stratum chart induced by `(p, e)`: coordinates outside the vanishing set
such that the remaining coordinates in `S` are strictly positive and the inserted point lands in
`e.target`. -/
private def depthStratumChartTarget [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.1 ∈ e.source) :
    Set (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) :=
  {y | (∀ j ∈ S, j ∉ vanishingFinset J S e p.1 → 0 < chartInsert J hJ p e he hp y j) ∧
    J.symm (chartInsert J hJ p e he hp y) ∈ e.target}

private theorem chartInsert_mem_range_of_mem_target [IsManifold J 1 M]
    {hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}} {k : ℕ} {p : ↥(J.depthStratum M k)}
    {e : OpenPartialHomeomorph M H} {he : e ∈ IsManifold.maximalAtlas J 1 M}
    {hp : p.1 ∈ e.source} {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : y ∈ depthStratumChartTarget J hJ p e he hp) :
    chartInsert J hJ p e he hp y ∈ range J := by
  classical
  rw [hJ]
  intro j hj
  by_cases hjZ : j ∈ vanishingFinset J S e p.1
  · rw [chartInsert, coordSplitInsert_apply_of_mem _ _ y hjZ]
  · exact (hy.1 j hj hjZ).le

private theorem mem_depthStratum_of_mem_target [IsManifold J 1 M]
    {hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}} {k : ℕ} {p : ↥(J.depthStratum M k)}
    {e : OpenPartialHomeomorph M H} {he : e ∈ IsManifold.maximalAtlas J 1 M}
    {hp : p.1 ∈ e.source} {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : y ∈ depthStratumChartTarget J hJ p e he hp) :
    e.symm (J.symm (chartInsert J hJ p e he hp y)) ∈ J.depthStratum M k := by
  have hmem : chartInsert J hJ p e he hp y ∈ range J :=
    chartInsert_mem_range_of_mem_target J hy
  have hq_src : e.symm (J.symm (chartInsert J hJ p e he hp y)) ∈ e.source := e.map_target hy.2
  have hq_ext : e.extend J (e.symm (J.symm (chartInsert J hJ p e he hp y))) =
      chartInsert J hJ p e he hp y := by
    rw [OpenPartialHomeomorph.extend_coe, comp_apply, e.right_inv hy.2, J.right_inv hmem]
  rw [mem_depthStratum_iff, ← depthAt_extend_eq_depth one_ne_zero he hq_src, hq_ext]
  have hdepth_p : J.depthAt (e.extend J p.1) = k := by
    rw [depthAt_extend_eq_depth one_ne_zero he hp]
    exact mem_depthStratum_iff.1 p.2
  refine ((depthAt_eq_iff_of_forall_pos hJ
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _)
    hmem (fun j hj hne ↦ hy.1 j hj ?_)).2 fun j hj h0 ↦ ?_).trans hdepth_p
  · rw [mem_vanishingFinset_iff]
    exact fun h ↦ hne h.2
  · classical
    exact coordSplitInsert_apply_of_mem _ _ y ((mem_vanishingFinset_iff J).2 ⟨hj, h0⟩)

private theorem extend_eq_zero_of_mem_posSlice [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.1 ∈ e.source) {q : ↥(J.depthStratum M k)}
    (hq : q.1 ∈ {q ∈ e.source | ∀ j ∈ S, e.extend J p.1 j ≠ 0 → 0 < e.extend J q j}) :
    ∀ i ∈ vanishingFinset J S e p.1, e.extend J q.1 i = 0 := fun i hi ↦ by
  have hi' := (mem_vanishingFinset_iff J).1 hi
  have heq : J.depthAt (e.extend J q.1) = J.depthAt (e.extend J p.1) := by
    rw [depthAt_extend_eq_depth one_ne_zero he hq.1,
      depthAt_extend_eq_depth one_ne_zero he hp,
      mem_depthStratum_iff.1 q.2, mem_depthStratum_iff.1 p.2]
  exact (depthAt_eq_iff_of_forall_pos hJ
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _)
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _) hq.2).1 heq i hi'.1 hi'.2

private theorem chartProj_mem_depthStratumChartTarget [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.1 ∈ e.source) {q : ↥(J.depthStratum M k)}
    (hq : q.1 ∈ {q ∈ e.source | ∀ j ∈ S, e.extend J p.1 j ≠ 0 → 0 < e.extend J q j}) :
    chartProj J hJ p e he hp (e.extend J q.1) ∈ depthStratumChartTarget J hJ p e he hp := by
  classical
  have h_ins_eq : chartInsert J hJ p e he hp (chartProj J hJ p e he hp (e.extend J q.1)) =
      e.extend J q.1 :=
    coordSplitInsert_proj _ _ (extend_eq_zero_of_mem_posSlice J hJ p e he hp hq)
  refine ⟨fun j hj hjZ ↦ ?_, ?_⟩
  · rw [h_ins_eq]
    exact hq.2 j hj fun h0 ↦ hjZ ((mem_vanishingFinset_iff J).2 ⟨hj, h0⟩)
  · rw [h_ins_eq, OpenPartialHomeomorph.extend_coe, comp_apply, J.left_inv]
    exact e.map_source hq.1

private theorem isOpen_depthStratumChartTarget [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (p : ↥(J.depthStratum M k))
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas J 1 M)
    (hp : p.1 ∈ e.source) :
    IsOpen (depthStratumChartTarget J hJ p e he hp) := by
  let ins := chartInsert J hJ p e he hp
  have hV : depthStratumChartTarget J hJ p e he hp =
      (⋂ j : {j : ι // j ∈ S ∧ j ∉ vanishingFinset J S e p.1}, (fun y ↦ ins y j.1) ⁻¹' Ioi 0) ∩
        (J.symm ∘ ins) ⁻¹' e.target := by
    ext y
    simp only [depthStratumChartTarget, ins, mem_ofPred_eq, mem_inter_iff, mem_iInter,
      mem_preimage, mem_Ioi, comp_apply, Subtype.forall]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨fun j hj ↦ h1 j hj.1 hj.2, h2⟩,
      fun ⟨h1, h2⟩ ↦ ⟨fun j hj hjZ ↦ h1 j ⟨hj, hjZ⟩, h2⟩⟩
  rw [hV]
  refine (isOpen_iInter_of_finite fun j ↦ ?_).inter
    (e.open_target.preimage (J.continuous_symm.comp ins.continuous))
  exact isOpen_Ioi.preimage
    ((EuclideanSpace.proj j.1 : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.comp ins.continuous)

open Classical in
/-- On a `C^1` manifold `M` modelled on `range J = {z | ∀ i ∈ S, 0 ≤ z i}`, an ambient chart `e`
containing `p ∈ J.depthStratum M k` induces a chart on `↥(J.depthStratum M k)` valued in
`EuclideanSpace ℝ (Fin (Fintype.card ι - k))` by deleting the `k` coordinates in `S` vanishing at
`e.extend J p`. -/
private def depthStratumChart [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {k : ℕ} (p : ↥(J.depthStratum M k)) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas J 1 M) (hp : p.1 ∈ e.source) :
    OpenPartialHomeomorph ↥(J.depthStratum M k) (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) where
  toFun q := chartProj J hJ p e he hp (e.extend J q.1)
  invFun y := if hy : y ∈ depthStratumChartTarget J hJ p e he hp then
    ⟨e.symm (J.symm (chartInsert J hJ p e he hp y)), mem_depthStratum_of_mem_target J hy⟩ else p
  source := Subtype.val ⁻¹' {q ∈ e.source | ∀ j ∈ S, e.extend J p.1 j ≠ 0 → 0 < e.extend J q j}
  target := depthStratumChartTarget J hJ p e he hp
  map_source' _ hq := chartProj_mem_depthStratumChartTarget J hJ p e he hp hq
  map_target' y hy := by
    simp only [dite_eq_left hy, mem_preimage]
    refine ⟨e.map_target hy.2, fun j hj hne ↦ ?_⟩
    rw [OpenPartialHomeomorph.extend_coe, comp_apply, e.right_inv hy.2,
      J.right_inv (chartInsert_mem_range_of_mem_target J hy)]
    exact hy.1 j hj fun h ↦ hne ((mem_vanishingFinset_iff J).1 h).2
  left_inv' q hq := by
    have hmem := chartProj_mem_depthStratumChartTarget J hJ p e he hp hq
    have h_ins_eq : chartInsert J hJ p e he hp (chartProj J hJ p e he hp (e.extend J q.1)) =
        e.extend J q.1 :=
      coordSplitInsert_proj _ _ (extend_eq_zero_of_mem_posSlice J hJ p e he hp hq)
    ext1
    simp only [dite_eq_left hmem]
    rw [h_ins_eq, OpenPartialHomeomorph.extend_coe, comp_apply, J.left_inv, e.left_inv hq.1]
  right_inv' y hy := by
    simp only [dite_eq_left hy]
    rw [OpenPartialHomeomorph.extend_coe, comp_apply, e.right_inv hy.2,
      J.right_inv (chartInsert_mem_range_of_mem_target J hy)]
    exact coordSplitProj_insert _ _ y
  open_source := (isOpen_setOf_forall_extend_pos J S e p.1).preimage continuous_subtype_val
  open_target := isOpen_depthStratumChartTarget J hJ p e he hp
  continuousOn_toFun := by
    have h1 : ContinuousOn (fun q : ↥(J.depthStratum M k) ↦ e q.1)
        (Subtype.val ⁻¹' {q ∈ e.source | ∀ j ∈ S, e.extend J p.1 j ≠ 0 → 0 < e.extend J q j}) :=
      e.continuousOn.comp continuous_subtype_val.continuousOn fun q hq ↦ hq.1
    exact ((chartProj J hJ p e he hp).continuous.comp J.continuous).comp_continuousOn h1
  continuousOn_invFun := by
    have hcont : ContinuousOn (fun y ↦ e.symm (J.symm (chartInsert J hJ p e he hp y)))
        (depthStratumChartTarget J hJ p e he hp) :=
      e.continuousOn_symm.comp
        (J.continuous_symm.comp (chartInsert J hJ p e he hp).continuous).continuousOn
        fun _ hy ↦ hy.2
    refine IsInducing.subtypeVal.continuousOn_iff.2 (hcont.congr fun y hy ↦ ?_)
    simp [dite_eq_left hy]

section ChartLemmas

variable [IsManifold J 1 M] {hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}} {k : ℕ}
  {p : ↥(J.depthStratum M k)} {e : OpenPartialHomeomorph M H}
  {he : e ∈ IsManifold.maximalAtlas J 1 M} {hp : p.1 ∈ e.source}

private theorem depthStratumChart_source :
    (depthStratumChart J hJ p e he hp).source =
      Subtype.val ⁻¹' {q ∈ e.source | ∀ j ∈ S, e.extend J p.1 j ≠ 0 → 0 < e.extend J q j} :=
  rfl

private theorem depthStratumChart_apply (q : ↥(J.depthStratum M k)) :
    depthStratumChart J hJ p e he hp q = chartProj J hJ p e he hp (e.extend J q.1) :=
  rfl

private theorem coe_depthStratumChart_symm_apply
    {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : y ∈ (depthStratumChart J hJ p e he hp).target) :
    ((depthStratumChart J hJ p e he hp).symm y : M) =
      e.symm (J.symm (chartInsert J hJ p e he hp y)) := by
  unfold depthStratumChart
  dsimp only [OpenPartialHomeomorph.coe_toPartialEquiv_symm]
  exact congrArg Subtype.val (dite_eq_left hy)

private theorem extend_depthStratumChart_symm_apply
    {y : EuclideanSpace ℝ (Fin (Fintype.card ι - k))}
    (hy : y ∈ (depthStratumChart J hJ p e he hp).target) :
    e.extend J ((depthStratumChart J hJ p e he hp).symm y : M) =
      chartInsert J hJ p e he hp y := by
  rw [coe_depthStratumChart_symm_apply J hy, OpenPartialHomeomorph.extend_coe, comp_apply,
    e.right_inv hy.2, J.right_inv (chartInsert_mem_range_of_mem_target J hy)]

private theorem contDiffOn_depthStratumChart_symm_trans {n : ℕ∞ω} [IsManifold J n M]
    (p q : ↥(J.depthStratum M k))
    {e₁ e₂ : OpenPartialHomeomorph M H}
    (he₁ : e₁ ∈ atlas H M) (he₂ : e₂ ∈ atlas H M)
    (hp : p.1 ∈ e₁.source) (hq : q.1 ∈ e₂.source) :
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
    have hy₂ : c₁.symm y ∈ c₂.source := by
      simpa only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
        OpenPartialHomeomorph.symm_symm] using hy.2
    refine ⟨⟨hy₁.2, ?_⟩, chartInsert_mem_range_of_mem_target J hy₁⟩
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

/-- The canonical boundaryless charted-space structure on the depth-`k` stratum
`↥(J.depthStratum M k)` of a `C^1` manifold `M` modelled on a coordinate region
`range J = {z | ∀ i ∈ S, 0 ≤ z i}`. Its atlas consists of the charts induced by the preferred
ambient charts of `M`.

This definition is intentionally not a global `instance` (to avoid typeclass diamonds with
`TauCeti.boundaryChartedSpace` and because `hJ` is a propositional hypothesis) and is marked
`@[irreducible]`; use `depthStratumChartedSpace_atlas` and `depthStratumChartedSpace_chartAt_source`
to reason about it. -/
@[irreducible]
def depthStratumChartedSpace [IsManifold J 1 M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) ↥(J.depthStratum M k) where
  atlas := range fun p : ↥(J.depthStratum M k) ↦
    depthStratumChart J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
      (mem_chart_source H p.1)
  chartAt := fun p ↦
    depthStratumChart J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
      (mem_chart_source H p.1)
  mem_chart_source p := by
    rw [depthStratumChart_source]
    exact mem_setOf_forall_extend_pos_self hJ (mem_chart_source H p.1)
  chart_mem_atlas p := mem_range_self p

private theorem depthStratumChartedSpace_chartAt [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k)) :
    (J.depthStratumChartedSpace M hJ k).chartAt p =
      depthStratumChart J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
        (mem_chart_source H p.1) := by
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
      Subtype.val ⁻¹' {q ∈ (chartAt H p.1).source |
        ∀ j ∈ S, extChartAt J p.1 p.1 j ≠ 0 → 0 < extChartAt J p.1 q j} := by
  rw [depthStratumChartedSpace_chartAt]
  rfl

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
      depthStratumChart J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
        (mem_chart_source H p.1) :=
    depthStratumChartedSpace_chartAt J M hJ k p
  have hq_ch : chartAt (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) q =
      depthStratumChart J hJ q (chartAt H q.1) (IsManifold.chart_mem_maximalAtlas q.1)
        (mem_chart_source H q.1) :=
    depthStratumChartedSpace_chartAt J M hJ k q
  dsimp only
  rw [hp_ch, hq_ch]
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id,
    range_id, preimage_id_eq, id_eq, inter_univ] using
    contDiffOn_depthStratumChart_symm_trans J p q (chart_mem_atlas H p.1)
      (chart_mem_atlas H q.1) (mem_chart_source H p.1) (mem_chart_source H q.1)

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
    continuous_subtype_val.continuousAt
    (chartSplitEquiv J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
      (mem_chart_source H p.1)) ?_
  intro y hy
  have hch : chartAt (EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p =
      depthStratumChart J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
        (mem_chart_source H p.1) :=
    depthStratumChartedSpace_chartAt J M hJ k p
  have hy' : y ∈ (depthStratumChart J hJ p (chartAt H p.1)
      (IsManifold.chart_mem_maximalAtlas p.1) (mem_chart_source H p.1)).target := by
    rw [extChartAt_target] at hy
    simpa only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq, hch] using hy.1
  have hsymm : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p).symm y =
      (depthStratumChart J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
        (mem_chart_source H p.1)).symm y := by
    simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, comp_id, hch]
  simp only [comp_apply, hsymm]
  exact extend_depthStratumChart_symm_apply J hy'

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

/-- The inclusion of a depth stratum `↥(J.depthStratum M k) → M` is `C^n`. -/
theorem contMDiff_subtypeVal_depthStratum (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J n
      (Subtype.val : ↥(J.depthStratum M k) → M) := by
  intro _ _
  exact (J.isImmersionOfComplement_subtypeVal_depthStratum M hn hJ k).contMDiff

/-- The inclusion of a depth stratum `↥(J.depthStratum M k) → M` is `MDifferentiable`. -/
theorem mdifferentiable_subtypeVal_depthStratum (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J
      (Subtype.val : ↥(J.depthStratum M k) → M) := by
  intro _ _
  exact (J.contMDiff_subtypeVal_depthStratum M hn hJ k).mdifferentiable hn

/-- The differential of the stratum inclusion `↥(J.depthStratum M k) → M` is injective at every
point. -/
theorem injective_mfderiv_subtypeVal_depthStratum (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k)) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J
      (Subtype.val : ↥(J.depthStratum M k) → M) p) := by
  intro _ _
  exact (J.isImmersionOfComplement_subtypeVal_depthStratum M hn hJ k).mfderiv_injective hn p

private theorem hasMFDerivAt_subtypeVal_depthStratum [IsManifold J 1 M]
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k)) :
    let _ := J.depthStratumChartedSpace M hJ k
    let E₀ := EuclideanSpace ℝ (Fin (Fintype.card ι - k))
    let L := chartInsert J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
      (mem_chart_source H p.1)
    HasMFDerivAt 𝓘(ℝ, E₀) J (Subtype.val : ↥(J.depthStratum M k) → M) p
      ((tangentSpaceCastModel J p.1).symm.toContinuousLinearMap.comp
        (L.comp (tangentSpaceCastModel 𝓘(ℝ, E₀) p).toContinuousLinearMap)) := by
  intro _
  let E₀ := EuclideanSpace ℝ (Fin (Fintype.card ι - k))
  let c := depthStratumChart J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
    (mem_chart_source H p.1)
  have hch : chartAt E₀ p = c := depthStratumChartedSpace_chartAt J M hJ k p
  let L := chartInsert J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
    (mem_chart_source H p.1)
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hcast :
      (tangentSpaceCastModel J p.1 : _ →L[ℝ] EuclideanSpace ℝ ι) ∘L
        ((tangentSpaceCastModel J p.1).symm.toContinuousLinearMap.comp
          (L.comp (tangentSpaceCastModel 𝓘(ℝ, E₀) p).toContinuousLinearMap)) ∘L
        ((tangentSpaceCastModel 𝓘(ℝ, E₀) p).symm : E₀ →L[ℝ] _) = L := by
    ext u
    simp
  rw [hcast]
  have hp_tgt : extChartAt 𝓘(ℝ, E₀) p p ∈ c.target := by
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, id_comp, hch] using
      c.map_source (mem_setOf_forall_extend_pos_self hJ (mem_chart_source H p.1))
  have heq : writtenInExtChartAt 𝓘(ℝ, E₀) J p (Subtype.val : ↥(J.depthStratum M k) → M) =ᶠ[
      𝓝[range 𝓘(ℝ, E₀)] (extChartAt 𝓘(ℝ, E₀) p p)] L := by
    filter_upwards [nhdsWithin_le_nhds (c.open_target.mem_nhds hp_tgt)] with y hy
    have hsymm : (extChartAt 𝓘(ℝ, E₀) p).symm y = c.symm y := by
      simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, comp_id, hch]
    simp only [writtenInExtChartAt, comp_apply, hsymm]
    exact extend_depthStratumChart_symm_apply J hy
  have hx : writtenInExtChartAt 𝓘(ℝ, E₀) J p (Subtype.val : ↥(J.depthStratum M k) → M)
      (extChartAt 𝓘(ℝ, E₀) p p) = L (extChartAt 𝓘(ℝ, E₀) p p) :=
    heq.self_of_nhdsWithin (by simp)
  exact L.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq hx

/-- Tangent space characterization of a depth stratum: a tangent vector `v : TangentSpace J p.1`
lies in the image of the differential of `Subtype.val : ↥(J.depthStratum M k) → M` at `p` exactly
when its model coordinates vanish along every coordinate `i ∈ S` that vanishes at
`extChartAt J p.1 p.1`. -/
theorem mem_range_mfderiv_subtypeVal_depthStratum_iff (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) (p : ↥(J.depthStratum M k))
    (v : TangentSpace J p.1) :
    let _ : IsManifold J 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
    let _ := J.depthStratumChartedSpace M hJ k
    v ∈ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) J
      (Subtype.val : ↥(J.depthStratum M k) → M) p).range ↔
      ∀ i ∈ S, extChartAt J p.1 p.1 i = 0 → tangentSpaceCastModel J p.1 v i = 0 := by
  intro _ _
  classical
  let L := chartInsert J hJ p (chartAt H p.1) (IsManifold.chart_mem_maximalAtlas p.1)
    (mem_chart_source H p.1)
  rw [(hasMFDerivAt_subtypeVal_depthStratum J M hJ k p).mfderiv]
  constructor
  · rintro ⟨w, hw⟩ i hi h0
    have hmem : tangentSpaceCastModel J p.1 v ∈ L.range := by
      refine ⟨tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p w, ?_⟩
      rw [← hw]
      simp [L]
    exact (mem_range_coordSplitInsert_iff _ _ _).1 hmem i ((mem_vanishingFinset_iff J).2 ⟨hi, h0⟩)
  · intro hv
    have hmem : tangentSpaceCastModel J p.1 v ∈ L.range :=
      (mem_range_coordSplitInsert_iff _ _ _).2 fun i hi ↦
        have hi' := (mem_vanishingFinset_iff J).1 hi
        hv i hi'.1 hi'.2
    obtain ⟨u, hu⟩ := hmem
    refine ⟨(tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k))) p).symm u, ?_⟩
    simpa [L] using (tangentSpaceCastModel J p.1).symm_apply_eq.2 hu

end ManifoldStructure

end ModelWithCorners
