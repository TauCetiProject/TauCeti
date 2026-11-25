/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Corners.Depth
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# The depth strata of a manifold with corners

A manifold with corners `M` is partitioned by the depth of its points
(`ModelWithCorners.depth`): its *depth-`k` stratum* `I.depthStratum M k` is the set of points of
depth `k`. The depth-zero stratum is the interior and is open; on a manifold with boundary
modelled on the half-space the depth-one stratum is the boundary, and there are no strata of depth
greater than one. The strata of higher depth are the edges and vertices of the corners: on the
cube `[0, 1]³` the strata of depth `0, 1, 2, 3` are the open cube, the six open faces, the twelve
open edges and the eight vertices.

The main point of this file is that on a manifold modelled on the quadrant `[0, ∞)ⁿ` every stratum
is itself a manifold, without boundary and of the expected dimension: on the quadrant `[0, ∞)²`
the boundary, an L-shaped union of two half-axes, is not a smooth submanifold of `ℝ²` at the
origin, where it has a corner, whereas its strata, the two open half-axes, of depth `1`, and the
origin, of depth `2`, are. The depth-`k` stratum of a `C^1` manifold modelled on `[0, ∞)ⁿ` is a
manifold modelled on `ℝⁿ⁻ᵏ`, of class `C^r` whenever the ambient manifold is
(`TauCeti.isManifold_depthStratum`), and its inclusion is a `C^r` smooth embedding
(`TauCeti.isSmoothEmbedding_subtypeVal_depthStratum`). The ambient `C^1` structure
(`[IsManifold (𝓡c n) 1 M]`) is needed already to form the charts: without it the depth may depend
on the chart. Its topology is the subspace
topology, so it inherits Hausdorffness and second countability from `M`. This is what lets
statements proved for manifolds without boundary, such as Sard's theorem, be applied to manifolds
with corners one stratum at a time.

The charts are read off the ambient charts. A point `p` of depth `k` is sent by the preferred
chart at `p` to a point of the quadrant with exactly `k` vanishing coordinates. Near `p` the other
coordinates stay positive, so there the points of depth `k` are exactly those at which the same
`k` coordinates vanish (`ModelWithCorners.depth_modelWithCornersEuclideanQuadrant`, which uses
the chart independence of the depth). Deleting these coordinates gives a chart of the stratum
at `p`. A transition map between two such charts is an ambient transition map restricted to a
coordinate face and composed with linear coordinate maps, so it is `C^r`.

## Main definitions

* `ModelWithCorners.depthStratum`: the depth-`k` stratum of a manifold with corners.
* `TauCeti.depthStratumChartedSpace`: the charted-space structure on the depth-`k` stratum of a
  `C^1` manifold modelled on `[0, ∞)ⁿ`, modelled on `EuclideanSpace ℝ (Fin (n - k))`.

## Main results

* `ModelWithCorners.iUnion_depthStratum`, `ModelWithCorners.pairwise_disjoint_depthStratum`,
  `ModelWithCorners.depthStratum_eq_empty_of_finrank_lt`: the strata partition the manifold, and
  only the strata of depth at most its dimension are nonempty.
* `ModelWithCorners.depthStratum_zero`: the depth-zero stratum is the interior.
* `ModelWithCorners.depthStratum_modelWithCornersEuclideanHalfSpace_one`,
  `ModelWithCorners.depthStratum_modelWithCornersEuclideanHalfSpace_eq_empty_of_one_lt`: on a
  manifold modelled on the half-space, the depth-one stratum is the boundary and there are no
  strata of higher depth.
* `TauCeti.card_filter_chartAt_eq_of_mem_depthStratum`: on a `C^1` manifold modelled on the
  quadrant, a point of the depth-`k` stratum has exactly `k` vanishing coordinates in its preferred
  chart.
* `TauCeti.depthStratumChartedSpace_atlas`, `TauCeti.depthStratumChartedSpace_chartAt_source` and
  its companions: the atlas of the stratum is the range of its preferred charts, which read the
  ambient preferred charts with the vanishing coordinates deleted.
* `TauCeti.isManifold_depthStratum`: the depth-`k` stratum of a `C^1` manifold modelled on the
  quadrant that is `C^r` is a `C^r` manifold without boundary.
* `TauCeti.isImmersion_subtypeVal_depthStratum`,
  `TauCeti.isSmoothEmbedding_subtypeVal_depthStratum`: under the same hypotheses its inclusion is a
  `C^r` immersion and a `C^r` smooth embedding.

## References

* D. Joyce, *On manifolds with corners*, in Advances in Geometric Analysis, Adv. Lect. Math. 21,
  International Press, 2012, 225–258, §2 (the depth stratification).

The formal construction of the stratum charts follows that of the boundary charts of a manifold
modelled on the half-space, `TauCeti.boundaryChartedSpace` in
`TauCeti.Geometry.Manifold.Boundary.Charts`: an ambient chart is restricted to a coordinate face
with `OpenPartialHomeomorph.subtypeCoord` and composed with the deletion of the vanishing
coordinates, and the transition maps are ambient transition maps precomposed with a coordinate
insertion and followed by a coordinate deletion. Here the face is cut out by the `k` coordinates
vanishing at the base point rather than by the zeroth coordinate of the half-space.
-/

public section

noncomputable section

open Function Set Topology Module

open scoped Manifold ContDiff Finset

namespace ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The **depth-`k` stratum** of a manifold with corners `M`: the set of its points of depth `k`
(`ModelWithCorners.depth`). -/
def depthStratum (k : ℕ) : Set M :=
  {x | I.depth x = k}

variable {I M}

@[simp, grind =]
theorem mem_depthStratum {k : ℕ} {x : M} : x ∈ I.depthStratum M k ↔ I.depth x = k :=
  Iff.rfl

/-- A point of the depth-`k` stratum has depth `k`. -/
@[simp, grind =]
theorem depth_subtypeVal_depthStratum {k : ℕ} (p : I.depthStratum M k) : I.depth (p : M) = k :=
  p.prop

/-- Every point lies in the stratum of its depth. -/
@[simp]
theorem iUnion_depthStratum : ⋃ k, I.depthStratum M k = univ :=
  eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨I.depth x, rfl⟩

/-- Distinct depth strata are disjoint. -/
theorem pairwise_disjoint_depthStratum : Pairwise (Disjoint on I.depthStratum M) :=
  fun _ _ hkl ↦ disjoint_left.2 fun _ hk hl ↦ hkl (hk.symm.trans hl)

/-- There are no points of depth larger than the dimension of the model. -/
theorem depthStratum_eq_empty_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    I.depthStratum M k = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have := depth_le_finrank (I := I) x
    rw [mem_depthStratum] at hx
    omega

variable [FiniteDimensional ℝ E]

/-- The depth-zero stratum is the interior. -/
@[simp]
theorem depthStratum_zero : I.depthStratum M 0 = I.interior M := by
  ext x
  simp [ModelWithCorners.interior]

/-- The depth-zero stratum of a `C^r` manifold, `r ≠ 0`, is open. -/
theorem isOpen_depthStratum_zero {r : WithTop ℕ∞} [IsManifold I r M] (hr : r ≠ 0) :
    IsOpen (I.depthStratum M 0) :=
  depthStratum_zero (I := I) (M := M) ▸ I.isOpen_interior hr

/-- On a manifold modelled on the half-space, the depth-one stratum is the boundary. -/
@[simp]
theorem depthStratum_modelWithCornersEuclideanHalfSpace_one {d : ℕ} [NeZero d] {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M] :
    (𝓡∂ d).depthStratum M 1 = (𝓡∂ d).boundary M := by
  ext x
  simp [ModelWithCorners.boundary]

/-- On a manifold modelled on the half-space, there are no strata of depth larger than one. -/
theorem depthStratum_modelWithCornersEuclideanHalfSpace_eq_empty_of_one_lt {d k : ℕ} [NeZero d]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M] (hk : 1 < k) :
    (𝓡∂ d).depthStratum M k = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have := depth_modelWithCornersEuclideanHalfSpace_le_one (n := d) x
    rw [mem_depthStratum] at hx
    omega

end ModelWithCorners

namespace TauCeti

section Quadrant

open EuclideanSpace (finsetComplEquivProd finsetComplEquivProd_symm_mk_fst_zero
  finsetComplEquivProd_symm_mk_zero_apply_of_mem forall_finsetComplEquivProd_symm_mk_zero_iff)

variable {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

variable (n) in
/-- The coordinates vanishing at the image of `x` in its preferred chart. -/
private def zeroCoords (x : M) : Finset (Fin n) :=
  {i | (chartAt (EuclideanQuadrant n) x x).val i = 0}

variable (n) in
/-- The part of the preferred chart domain at `x` on which the coordinates that do not vanish at
`x` stay positive. -/
private def stratumDomain (x : M) : Set M :=
  (chartAt (EuclideanQuadrant n) x).source ∩
    {y | ∀ i ∉ zeroCoords n x, 0 < (chartAt (EuclideanQuadrant n) x y).val i}

private theorem isOpen_stratumDomain (x : M) : IsOpen (stratumDomain n x) := by
  have : IsOpen {h : EuclideanQuadrant n | ∀ i ∉ zeroCoords n x, 0 < h.val i} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ i).comp continuous_subtypeVal)
  exact (chartAt _ x).continuousOn.isOpen_inter_preimage (chartAt _ x).open_source this

private theorem mem_stratumDomain (x : M) : x ∈ stratumDomain n x := by
  refine ⟨mem_chart_source _ x, fun i hi ↦
    lt_of_le_of_ne ((chartAt (EuclideanQuadrant n) x x).prop i) (Ne.symm ?_)⟩
  simpa [zeroCoords] using hi

variable (n) in
/-- The preferred chart at `x`, restricted to `stratumDomain n x`. -/
private def stratumAmbientChart (x : M) : OpenPartialHomeomorph M (EuclideanQuadrant n) :=
  (chartAt (EuclideanQuadrant n) x).restrOpen _ (isOpen_stratumDomain (n := n) x)

variable (k) in
/-- The parametrization of the stratum through `x` near `x`: insert a vector outside the
coordinates vanishing at `x` and read it in the quadrant. -/
private def stratumParam (x : M) (hx : #(zeroCoords n x) = k)
    (w : EuclideanSpace ℝ (Fin (n - k))) : EuclideanQuadrant n :=
  (𝓡c n).symm ((finsetComplEquivProd ℝ (zeroCoords n x) hx).symm (w, 0))

/-- The coordinates of a point of the quadrant outside those vanishing at `x`. -/
private def stratumProj (x : M) (hx : #(zeroCoords n x) = k) (h : EuclideanQuadrant n) :
    EuclideanSpace ℝ (Fin (n - k)) :=
  (finsetComplEquivProd ℝ (zeroCoords n x) hx ((𝓡c n) h)).1

private theorem stratumParam_eq_of_nonneg {x : M} {hx : #(zeroCoords n x) = k}
    {w : EuclideanSpace ℝ (Fin (n - k))} (hw : ∀ j, 0 ≤ w j) :
    (𝓡c n) (stratumParam k x hx w) = (finsetComplEquivProd ℝ (zeroCoords n x) hx).symm (w, 0) := by
  refine (𝓡c n).right_inv ?_
  rw [range_modelWithCornersEuclideanQuadrant]
  intro i
  by_cases hi : i ∈ zeroCoords n x
  · rw [finsetComplEquivProd_symm_mk_zero_apply_of_mem w hi]
  · exact (forall_finsetComplEquivProd_symm_mk_zero_iff (0 ≤ ·) w).2 hw i hi

private theorem stratumParam_apply_of_mem {x : M} {hx : #(zeroCoords n x) = k}
    (w : EuclideanSpace ℝ (Fin (n - k))) {i : Fin n} (hi : i ∈ zeroCoords n x) :
    (stratumParam k x hx w).val i = 0 := by
  simp [stratumParam, modelWithCornersEuclideanQuadrant_symm_apply,
    finsetComplEquivProd_symm_mk_zero_apply_of_mem w hi]

private theorem coe_stratumAmbientChart (x : M) :
    ⇑(stratumAmbientChart n x) = chartAt (EuclideanQuadrant n) x :=
  OpenPartialHomeomorph.coe_restrOpen _ _

private theorem coe_stratumAmbientChart_symm (x : M) :
    ⇑(stratumAmbientChart n x).symm = (chartAt (EuclideanQuadrant n) x).symm :=
  OpenPartialHomeomorph.coe_restrOpen_symm _ _

private theorem stratumAmbientChart_source (x : M) :
    (stratumAmbientChart n x).source = stratumDomain n x := by
  rw [stratumAmbientChart, OpenPartialHomeomorph.restrOpen_source]
  exact inter_eq_right.2 inter_subset_left

private theorem mem_stratumAmbientChart_target {x : M} {h : EuclideanQuadrant n} :
    h ∈ (stratumAmbientChart n x).target ↔
      h ∈ (chartAt (EuclideanQuadrant n) x).target ∧
        (chartAt (EuclideanQuadrant n) x).symm h ∈ stratumDomain n x := by
  simp [stratumAmbientChart, PartialEquiv.restr_target]

/-- A point of the restricted chart target in the image of the parametrization has positive
inserted coordinates. -/
private theorem pos_of_mem_target {x : M} {hx : #(zeroCoords n x) = k}
    {w : EuclideanSpace ℝ (Fin (n - k))}
    (hw : stratumParam k x hx w ∈ (stratumAmbientChart n x).target) : ∀ j, 0 < w j := by
  obtain ⟨h₁, h₂⟩ := mem_stratumAmbientChart_target.1 hw
  refine (forall_finsetComplEquivProd_symm_mk_zero_iff (hZ := hx) (0 < ·) w).1 fun i hi ↦ ?_
  have h := h₂.2 i hi
  rw [(chartAt (EuclideanQuadrant n) x).right_inv h₁] at h
  simpa [stratumParam, modelWithCornersEuclideanQuadrant_symm_apply] using h

private theorem stratumProj_stratumParam {x : M} {hx : #(zeroCoords n x) = k}
    {w : EuclideanSpace ℝ (Fin (n - k))}
    (hw : stratumParam k x hx w ∈ (stratumAmbientChart n x).target) :
    stratumProj x hx (stratumParam k x hx w) = w := by
  rw [stratumProj, stratumParam_eq_of_nonneg fun j ↦ (pos_of_mem_target hw j).le,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem continuous_stratumParam (x : M) (hx : #(zeroCoords n x) = k) :
    Continuous (stratumParam k x hx) :=
  (𝓡c n).continuous_symm.comp
    ((finsetComplEquivProd ℝ _ _).symm.continuous.comp (Continuous.prodMk_left 0))

private theorem continuous_stratumProj (x : M) (hx : #(zeroCoords n x) = k) :
    Continuous (stratumProj x hx) :=
  continuous_fst.comp ((finsetComplEquivProd ℝ _ _).continuous.comp (𝓡c n).continuous)

private theorem leftInvOn_stratumProj_stratumParam (x : M) (hx : #(zeroCoords n x) = k) :
    LeftInvOn (stratumProj x hx) (stratumParam k x hx)
      (stratumParam k x hx ⁻¹' (stratumAmbientChart n x).target) :=
  fun _ hw ↦ stratumProj_stratumParam hw

variable [IsManifold (𝓡c n) 1 M]

/-- On a `C^1` manifold modelled on the quadrant, a point of the depth-`k` stratum has exactly `k`
coordinates vanishing at its image in its preferred chart. -/
theorem card_filter_chartAt_eq_of_mem_depthStratum {x : M} (hx : x ∈ (𝓡c n).depthStratum M k) :
    #{i | (chartAt (EuclideanQuadrant n) x x).val i = 0} = k :=
  (ModelWithCorners.depth_eq_card_filter_chartAt one_ne_zero (mem_chart_source _ x)).symm.trans hx

private theorem card_zeroCoords (x : M) : #(zeroCoords n x) = (𝓡c n).depth x :=
  (ModelWithCorners.depth_eq_card_filter_chartAt one_ne_zero (mem_chart_source _ x)).symm

/-- On `stratumDomain n x`, the points of the depth of `x` are those whose image in the chart at
`x` vanishes on `zeroCoords n x`. -/
private theorem depth_eq_iff {x y : M} (hy : y ∈ stratumDomain n x) :
    (𝓡c n).depth y = (𝓡c n).depth x ↔
      ∀ i ∈ zeroCoords n x, (chartAt (EuclideanQuadrant n) x y).val i = 0 := by
  rw [ModelWithCorners.depth_eq_card_filter_chartAt one_ne_zero hy.1, ← card_zeroCoords]
  have hsub : ({i | (chartAt (EuclideanQuadrant n) x y).val i = 0} : Finset (Fin n)) ⊆
      zeroCoords n x :=
    fun i hi ↦ by_contra fun h ↦ (hy.2 i h).ne' (by simpa using hi)
  refine ⟨fun h i hi ↦ ?_, fun h ↦ congrArg _ <| hsub.antisymm fun i hi ↦ by simpa using h i hi⟩
  rw [← Finset.eq_of_subset_of_card_le hsub h.ge] at hi
  simpa using hi

private theorem symm_stratumParam_mem {x : M} {hx : #(zeroCoords n x) = k}
    {w : EuclideanSpace ℝ (Fin (n - k))}
    (hw : stratumParam k x hx w ∈ (stratumAmbientChart n x).target) :
    (stratumAmbientChart n x).symm (stratumParam k x hx w) ∈ (𝓡c n).depthStratum M k := by
  obtain ⟨h₁, h₂⟩ := mem_stratumAmbientChart_target.1 hw
  rw [coe_stratumAmbientChart_symm, ModelWithCorners.mem_depthStratum]
  refine ((depth_eq_iff h₂).2 fun i hi ↦ ?_).trans ((card_zeroCoords x).symm.trans hx)
  rw [(chartAt (EuclideanQuadrant n) x).right_inv h₁]
  exact stratumParam_apply_of_mem w hi

private theorem stratumParam_stratumProj {x : M} {hx : #(zeroCoords n x) = k} {y : M}
    (hy : y ∈ (stratumAmbientChart n x).source) (hyk : y ∈ (𝓡c n).depthStratum M k) :
    stratumParam k x hx (stratumProj x hx (stratumAmbientChart n x y)) =
      stratumAmbientChart n x y := by
  rw [stratumAmbientChart_source] at hy
  have hZ := (depth_eq_iff hy).1 (hyk.trans (hx.symm.trans (card_zeroCoords x)))
  rw [coe_stratumAmbientChart, stratumParam, stratumProj,
    finsetComplEquivProd_symm_mk_fst_zero (by simpa using hZ), ModelWithCorners.left_inv]

private theorem card_zeroCoords_eq (p : (𝓡c n).depthStratum M k) : #(zeroCoords n p.val) = k :=
  card_filter_chartAt_eq_of_mem_depthStratum p.prop

/-- The parametrization of the stratum at `p`, with the coordinates vanishing at `p` written out. -/
private theorem stratumParam_eq (p : (𝓡c n).depthStratum M k)
    (w : EuclideanSpace ℝ (Fin (n - k))) :
    stratumParam k p.val (card_zeroCoords_eq p) w =
      (𝓡c n).symm ((finsetComplEquivProd ℝ
        ({i | (chartAt (EuclideanQuadrant n) p.val p.val).val i = 0} : Finset (Fin n))
        (card_filter_chartAt_eq_of_mem_depthStratum p.prop)).symm (w, 0)) := by
  rw [stratumParam]
  dsimp only [zeroCoords]

/-- The chart of the depth-`k` stratum at `p`: the ambient chart at `p`, restricted to the stratum
near `p`, with the coordinates vanishing at `p` deleted. -/
private def stratumChart (p : (𝓡c n).depthStratum M k) :
    OpenPartialHomeomorph ((𝓡c n).depthStratum M k) (EuclideanSpace ℝ (Fin (n - k))) :=
  (stratumAmbientChart n p.val).subtypeCoord _ ⟨p⟩ (stratumParam k p.val (card_zeroCoords_eq p))
    (stratumProj p.val (card_zeroCoords_eq p)) (fun hw ↦ symm_stratumParam_mem hw)
    (fun hy hyk ↦ stratumParam_stratumProj hy hyk) 
    (leftInvOn_stratumProj_stratumParam _ _) (continuous_stratumParam _ _)
    (continuous_stratumProj _ _).continuousOn

private theorem stratumChart_apply (p q : (𝓡c n).depthStratum M k) :
    stratumChart p q =
      stratumProj p.val (card_zeroCoords_eq p) (chartAt (EuclideanQuadrant n) p.val q.val) := by
  rw [← coe_stratumAmbientChart, stratumChart]
  apply OpenPartialHomeomorph.subtypeCoord_apply
  exacts [symm_stratumParam_mem, stratumParam_stratumProj]

private theorem stratumChart_source (p : (𝓡c n).depthStratum M k) :
    (stratumChart p).source = Subtype.val ⁻¹' stratumDomain n p.val := by
  rw [← stratumAmbientChart_source, stratumChart]
  apply OpenPartialHomeomorph.subtypeCoord_source
  exacts [symm_stratumParam_mem, stratumParam_stratumProj]

private theorem stratumChart_target (p : (𝓡c n).depthStratum M k) :
    (stratumChart p).target =
      stratumParam k p.val (card_zeroCoords_eq p) ⁻¹' (stratumAmbientChart n p.val).target := by
  rw [stratumChart]
  apply OpenPartialHomeomorph.subtypeCoord_target
  exacts [symm_stratumParam_mem, stratumParam_stratumProj]

private theorem coe_stratumChart_symm_apply (p : (𝓡c n).depthStratum M k)
    {w : EuclideanSpace ℝ (Fin (n - k))} (hw : w ∈ (stratumChart p).target) :
    ((stratumChart p).symm w : M) =
      (chartAt (EuclideanQuadrant n) p.val).symm
        (stratumParam k p.val (card_zeroCoords_eq p) w) := by
  rw [stratumChart_target] at hw
  rw [← coe_stratumAmbientChart_symm, stratumChart]
  apply OpenPartialHomeomorph.coe_subtypeCoord_symm_apply
  exacts [symm_stratumParam_mem, stratumParam_stratumProj, hw]

/-- A point of the target of the stratum chart at `p` is sent into the target of the ambient
chart at `p`, where the quadrant inclusion reads it as a coordinate insertion. -/
private theorem stratumParam_mem_target_of_mem {p : (𝓡c n).depthStratum M k}
    {w : EuclideanSpace ℝ (Fin (n - k))} (hw : w ∈ (stratumChart p).target) :
    stratumParam k p.val (card_zeroCoords_eq p) w ∈ (chartAt (EuclideanQuadrant n) p.val).target ∧
      (𝓡c n) (stratumParam k p.val (card_zeroCoords_eq p) w) =
        (finsetComplEquivProd ℝ (zeroCoords n p.val) (card_zeroCoords_eq p)).symm (w, 0) := by
  rw [stratumChart_target, mem_preimage] at hw
  exact ⟨(mem_stratumAmbientChart_target.1 hw).1,
    stratumParam_eq_of_nonneg fun j ↦ (pos_of_mem_target hw j).le⟩

/-- The transition maps between stratum charts are `C^r`: through the coordinate splittings at the
two base points they are the ambient transition maps, restricted to a coordinate face. -/
private theorem contDiffOn_stratumChart_symm_trans {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M]
    (p q : (𝓡c n).depthStratum M k) :
    ContDiffOn ℝ r ((stratumChart p).symm ≫ₕ stratumChart q)
      ((stratumChart p).symm ≫ₕ stratumChart q).source := by
  have hg : (chartAt (EuclideanQuadrant n) p.val).symm ≫ₕ chartAt (EuclideanQuadrant n) q.val ∈
      contDiffGroupoid r (𝓡c n) :=
    StructureGroupoid.compatible _ (chart_mem_atlas _ _) (chart_mem_atlas _ _)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  -- The ambient transition map, read between the two coordinate splittings.
  set A := (ContinuousLinearMap.fst ℝ _ _).comp
    (finsetComplEquivProd ℝ (zeroCoords n q.val) (card_zeroCoords_eq q) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - k)) × EuclideanSpace ℝ (Fin k))
  set B := ((finsetComplEquivProd ℝ (zeroCoords n p.val) (card_zeroCoords_eq p)).symm :
      EuclideanSpace ℝ (Fin (n - k)) × EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
    (ContinuousLinearMap.inl ℝ _ _)
  refine ContDiffOn.congr (f := A ∘
      ((𝓡c n) ∘
        ((chartAt (EuclideanQuadrant n) p.val).symm ≫ₕ chartAt (EuclideanQuadrant n) q.val) ∘
          (𝓡c n).symm) ∘ B)
    (A.contDiff.comp_contDiffOn (hg.1.comp B.contDiff.contDiffOn fun w hw ↦ ?_)) fun w hw ↦ ?_
  · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
    obtain ⟨hw₁, hw₂⟩ := hw
    rw [mem_preimage, stratumChart_source, mem_preimage, coe_stratumChart_symm_apply p hw₁] at hw₂
    obtain ⟨hw₃, hw₄⟩ := stratumParam_mem_target_of_mem hw₁
    exact ⟨⟨hw₃, hw₂.1⟩, _, hw₄⟩
  · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
    have hw₁ : w ∈ (stratumChart p).target := hw.1
    rw [OpenPartialHomeomorph.coe_trans, comp_apply, stratumChart_apply,
      coe_stratumChart_symm_apply p hw₁]
    simp [A, B, stratumProj, stratumParam]

/-- The canonical charted-space structure on the depth-`k` stratum of a `C^1` manifold modelled
on the quadrant `[0, ∞)ⁿ`, modelled on `ℝⁿ⁻ᵏ`. The chart at `p` is the preferred ambient chart at
`p`, restricted to the points near `p` where the coordinates positive at `p` stay positive, with
the `k` coordinates vanishing at `p` deleted. The implementation is opaque; use
`TauCeti.depthStratumChartedSpace_atlas`, `TauCeti.depthStratumChartedSpace_chartAt_source` and
its companions, `TauCeti.isManifold_depthStratum` and `TauCeti.isImmersion_subtypeVal_depthStratum`.
-/
@[irreducible, instance] noncomputable def depthStratumChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n - k))) ((𝓡c n).depthStratum M k) where
  atlas := range stratumChart
  chartAt := stratumChart
  mem_chart_source p := by
    rw [stratumChart_source]
    exact mem_stratumDomain p.val
  chart_mem_atlas := mem_range_self

private theorem depthStratumChartedSpace_chartAt (p : (𝓡c n).depthStratum M k) :
    chartAt (EuclideanSpace ℝ (Fin (n - k))) p = stratumChart p := by
  unfold depthStratumChartedSpace
  rfl

variable (M k) in
/-- The atlas of the depth-`k` stratum is the range of its preferred charts. -/
theorem depthStratumChartedSpace_atlas :
    atlas (EuclideanSpace ℝ (Fin (n - k))) ((𝓡c n).depthStratum M k) =
      range (chartAt (EuclideanSpace ℝ (Fin (n - k)))) := by
  unfold atlas chartAt depthStratumChartedSpace
  rfl

/-- The source of the preferred chart of the depth-`k` stratum at `p` is the part of the stratum
that the preferred ambient chart at `p` sees and on which the coordinates not vanishing at `p` stay
positive. -/
theorem depthStratumChartedSpace_chartAt_source (p : (𝓡c n).depthStratum M k) :
    (chartAt (EuclideanSpace ℝ (Fin (n - k))) p).source =
      Subtype.val ⁻¹' ((chartAt (EuclideanQuadrant n) p.val).source ∩
        {y | ∀ i ∉ ({i | (chartAt (EuclideanQuadrant n) p.val p.val).val i = 0} : Finset (Fin n)),
          0 < (chartAt (EuclideanQuadrant n) p.val y).val i}) := by
  rw [depthStratumChartedSpace_chartAt, stratumChart_source, stratumDomain, zeroCoords]

/-- The target of the preferred chart of the depth-`k` stratum at `p`: the vectors with positive
coordinates whose insertion outside the `k` coordinates vanishing at `p` lies in the target of the
preferred ambient chart at `p`. -/
theorem depthStratumChartedSpace_chartAt_target (p : (𝓡c n).depthStratum M k) :
    (chartAt (EuclideanSpace ℝ (Fin (n - k))) p).target =
      {w | (∀ j, 0 < w j) ∧ (𝓡c n).symm ((finsetComplEquivProd ℝ _
        (card_filter_chartAt_eq_of_mem_depthStratum p.prop)).symm (w, 0)) ∈
        (chartAt (EuclideanQuadrant n) p.val).target} := by
  ext w
  rw [depthStratumChartedSpace_chartAt, stratumChart_target, mem_preimage]
  simp only [mem_ofPred_eq, ← stratumParam_eq]
  refine ⟨fun hw ↦ ⟨pos_of_mem_target hw, (mem_stratumAmbientChart_target.1 hw).1⟩,
    fun ⟨hpos, hw⟩ ↦ mem_stratumAmbientChart_target.2
      ⟨hw, (chartAt (EuclideanQuadrant n) p.val).map_target hw, fun i hi ↦ ?_⟩⟩
  rw [(chartAt (EuclideanQuadrant n) p.val).right_inv hw]
  have h := congrFun (congrArg (⇑) (stratumParam_eq_of_nonneg (x := p.val)
    (hx := card_zeroCoords_eq p) fun j ↦ (hpos j).le)) i
  rw [modelWithCornersEuclideanQuadrant_apply] at h
  rw [h]
  exact (forall_finsetComplEquivProd_symm_mk_zero_iff (0 < ·) w).2 hpos i hi

/-- The preferred chart of the depth-`k` stratum at `p` reads a point through the preferred
ambient chart at `p` and deletes the `k` coordinates vanishing at `p`. -/
theorem depthStratumChartedSpace_chartAt_apply (p q : (𝓡c n).depthStratum M k) :
    chartAt (EuclideanSpace ℝ (Fin (n - k))) p q =
      (finsetComplEquivProd ℝ _ (card_filter_chartAt_eq_of_mem_depthStratum p.prop)
        ((𝓡c n) (chartAt (EuclideanQuadrant n) p.val q.val))).1 := by
  rw [depthStratumChartedSpace_chartAt, stratumChart_apply, stratumProj]
  dsimp only [zeroCoords]

/-- On its target, the inverse of the preferred chart of the depth-`k` stratum at `p` inserts zeros
at the `k` coordinates vanishing at `p` and applies the inverse of the preferred ambient chart at
`p`. -/
theorem depthStratumChartedSpace_chartAt_symm_apply (p : (𝓡c n).depthStratum M k)
    {w : EuclideanSpace ℝ (Fin (n - k))}
    (hw : w ∈ (chartAt (EuclideanSpace ℝ (Fin (n - k))) p).target) :
    ((chartAt (EuclideanSpace ℝ (Fin (n - k))) p).symm w : M) =
      (chartAt (EuclideanQuadrant n) p.val).symm
        ((𝓡c n).symm ((finsetComplEquivProd ℝ _
          (card_filter_chartAt_eq_of_mem_depthStratum p.prop)).symm (w, 0))) := by
  rw [depthStratumChartedSpace_chartAt] at hw ⊢
  rw [coe_stratumChart_symm_apply p hw, stratumParam_eq]

/-- **The depth-`k` stratum of a `C^1` manifold modelled on the quadrant `[0, ∞)ⁿ` that is `C^r`
is a `C^r` manifold without boundary**, modelled on `ℝⁿ⁻ᵏ`. Both `[IsManifold (𝓡c n) 1 M]` and
`[IsManifold (𝓡c n) r M]` are assumed. -/
instance isManifold_depthStratum {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) r ((𝓡c n).depthStratum M k) := by
  refine isManifold_of_contDiffOn _ r _ ?_
  rw [depthStratumChartedSpace_atlas]
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
  simpa [depthStratumChartedSpace_chartAt] using contDiffOn_stratumChart_symm_trans p q

/-- The inclusion of the depth-`k` stratum of a `C^1` manifold modelled on the quadrant `[0, ∞)ⁿ`
that is `C^r` is a `C^r` immersion. -/
theorem isImmersion_subtypeVal_depthStratum {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M] :
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) r
      (Subtype.val : (𝓡c n).depthStratum M k → M) := by
  -- In the stratum chart and the ambient chart at a point, the inclusion is the coordinate
  -- insertion `ℝⁿ⁻ᵏ → ℝⁿ`, with complement `ℝᵏ`.
  apply Manifold.IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin k))
  intro p
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtypeVal.continuousAt
    (finsetComplEquivProd ℝ (zeroCoords n p.val) (card_zeroCoords_eq p)).symm (chartAt _ p)
    (chartAt (EuclideanQuadrant n) p.val) (mem_chart_source _ p) (mem_chart_source _ p.val)
    (IsManifold.chart_mem_maximalAtlas p) (IsManifold.chart_mem_maximalAtlas p.val)
  intro w hw
  rw [OpenPartialHomeomorph.extend_target, depthStratumChartedSpace_chartAt] at hw
  have hw₁ : w ∈ (stratumChart p).target := by simpa using hw.1
  obtain ⟨hw₂, hw₃⟩ := stratumParam_mem_target_of_mem hw₁
  simp only [comp_apply, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe_symm, id_eq, depthStratumChartedSpace_chartAt,
    coe_stratumChart_symm_apply p hw₁]
  rw [(chartAt (EuclideanQuadrant n) p.val).right_inv hw₂, hw₃]

/-- The inclusion of the depth-`k` stratum of a `C^1` manifold modelled on the quadrant `[0, ∞)ⁿ`
that is `C^r` is a `C^r` smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_depthStratum {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M] :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) r
      (Subtype.val : (𝓡c n).depthStratum M k → M) :=
  ⟨isImmersion_subtypeVal_depthStratum, IsEmbedding.subtypeVal⟩

end Quadrant

end TauCeti
