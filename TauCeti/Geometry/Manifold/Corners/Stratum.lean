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
modelled on the half-space the depth-one stratum is the boundary, and there are no others. The
strata of higher depth are the edges and vertices of the corners: on the cube `[0, 1]³` the strata
of depth `0, 1, 2, 3` are the open cube, the six open faces, the twelve open edges and the eight
vertices.

The main point of this file is that on a manifold modelled on the quadrant `[0, ∞)ⁿ` every stratum
is itself a manifold, without boundary and of the expected dimension, although the closed faces
are not: on the quadrant `[0, ∞)²` the boundary, an L-shaped union of two half-axes, is not a
manifold at the origin, whereas its strata are the two open half-axes, of depth `1`, and the
origin, of depth `2`. The depth-`k` stratum of a `C^r` manifold modelled on `[0, ∞)ⁿ` is a `C^r`
manifold modelled on `ℝⁿ⁻ᵏ` (`TauCeti.isManifold_depthStratum`) whose inclusion is a smooth
embedding (`TauCeti.isSmoothEmbedding_subtypeVal_depthStratum`). Its topology is the subspace
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
* `ModelWithCorners.depthStratum_modelWithCornersEuclideanHalfSpace_one`: on a manifold modelled
  on the half-space, the depth-one stratum is the boundary.
* `TauCeti.isManifold_depthStratum`: the depth-`k` stratum is a `C^r` manifold without boundary.
* `TauCeti.isImmersion_subtypeVal_depthStratum`,
  `TauCeti.isSmoothEmbedding_subtypeVal_depthStratum`: its inclusion is a `C^r` immersion and a
  `C^r` smooth embedding.

## References

* D. Joyce, *On manifolds with corners*, in Advances in Geometric Analysis, Adv. Lect. Math. 21,
  International Press, 2012, 225–258, §2 (the depth stratification).
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

@[simp]
theorem mem_depthStratum {k : ℕ} {x : M} : x ∈ I.depthStratum M k ↔ I.depth x = k :=
  Iff.rfl

/-- Every point lies in the stratum of its depth. -/
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

end ModelWithCorners

namespace TauCeti

section Split

variable {n k : ℕ} (Z : Finset (Fin n)) (hZ : Z.card = k)

/-- An enumeration of the coordinates outside `Z`. -/
private def outEquiv : {i // i ∉ Z} ≃ Fin (n - k) :=
  Fintype.equivFinOfCardEq (by simp [hZ])

/-- An enumeration of the coordinates in `Z`. -/
private def inEquiv : {i // ¬i ∉ Z} ≃ Fin k :=
  Fintype.equivFinOfCardEq (by simp [hZ])

/-- The splitting of `ℝⁿ` into the coordinates outside a set `Z` of `k` coordinates and those in
`Z`, each enumerated by a `Fin`. -/
private def splitEquiv :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin (n - k)) × EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.sumComplEquivProd ℝ (· ∉ Z)).trans <|
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (outEquiv Z hZ)).toContinuousLinearEquiv.prodCongr
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (inEquiv Z hZ)).toContinuousLinearEquiv

variable {Z hZ}

private theorem forall_fst_splitEquiv_iff (P : ℝ → Prop) (x : EuclideanSpace ℝ (Fin n)) :
    (∀ j, P ((splitEquiv Z hZ x).1 j)) ↔ ∀ i ∉ Z, P (x i) := by
  simp only [splitEquiv, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, EuclideanSpace.sumComplEquivProd_apply_fst]
  exact ⟨fun h i hi ↦ by simpa using h (outEquiv Z hZ ⟨i, hi⟩),
    fun h j ↦ h _ ((outEquiv Z hZ).symm j).2⟩

private theorem forall_snd_splitEquiv_iff (P : ℝ → Prop) (x : EuclideanSpace ℝ (Fin n)) :
    (∀ j, P ((splitEquiv Z hZ x).2 j)) ↔ ∀ i ∈ Z, P (x i) := by
  simp only [splitEquiv, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, EuclideanSpace.sumComplEquivProd_apply_snd]
  exact ⟨fun h i hi ↦ by simpa using h (inEquiv Z hZ ⟨i, not_not.2 hi⟩),
    fun h j ↦ h _ (not_not.1 ((inEquiv Z hZ).symm j).2)⟩

/-- A vector vanishing on `Z` is recovered from its coordinates outside `Z`. -/
private theorem splitEquiv_symm_fst {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i ∈ Z, x i = 0) :
    (splitEquiv Z hZ).symm ((splitEquiv Z hZ x).1, 0) = x := by
  have h2 : (splitEquiv Z hZ x).2 = 0 := by
    ext j
    exact (forall_snd_splitEquiv_iff (· = 0) x).2 hx j
  rw [← h2, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]

/-- Inserting a vector `w` of `ℝⁿ⁻ᵏ` outside `Z` gives a vector vanishing on `Z`. -/
private theorem splitEquiv_symm_apply_of_mem (w : EuclideanSpace ℝ (Fin (n - k))) {i : Fin n}
    (hi : i ∈ Z) : (splitEquiv Z hZ).symm (w, 0) i = 0 :=
  (forall_snd_splitEquiv_iff (hZ := hZ) (· = 0) _).1
    (by simp) i hi

/-- A property holds for every coordinate of `w` exactly when it holds for every coordinate
outside `Z` of its insertion. -/
private theorem forall_splitEquiv_symm_iff (P : ℝ → Prop) (w : EuclideanSpace ℝ (Fin (n - k))) :
    (∀ i ∉ Z, P ((splitEquiv Z hZ).symm (w, 0) i)) ↔ ∀ j, P (w j) := by
  rw [← forall_fst_splitEquiv_iff (hZ := hZ), ContinuousLinearEquiv.apply_symm_apply]

end Split

section Quadrant

variable {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

variable (n) in
/-- The coordinates vanishing at the image of `x` in its preferred chart. -/
private def zeroCoords (x : M) : Finset (Fin n) :=
  {i | (chartAt (EuclideanQuadrant n) x x).1 i = 0}

variable (n) in
/-- The part of the preferred chart domain at `x` on which the coordinates that do not vanish at
`x` stay positive. -/
private def stratumDomain (x : M) : Set M :=
  (chartAt (EuclideanQuadrant n) x).source ∩
    {y | ∀ i ∉ zeroCoords n x, 0 < (chartAt (EuclideanQuadrant n) x y).1 i}

private theorem isOpen_stratumDomain (x : M) : IsOpen (stratumDomain n x) := by
  have : IsOpen {h : EuclideanQuadrant n | ∀ i ∉ zeroCoords n x, 0 < h.1 i} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  exact (chartAt _ x).continuousOn.isOpen_inter_preimage (chartAt _ x).open_source this

private theorem mem_stratumDomain (x : M) : x ∈ stratumDomain n x := by
  refine ⟨mem_chart_source _ x, fun i hi ↦
    lt_of_le_of_ne ((chartAt (EuclideanQuadrant n) x x).2 i) (Ne.symm ?_)⟩
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
  (𝓡c n).symm ((splitEquiv (zeroCoords n x) hx).symm (w, 0))

/-- The coordinates of a point of the quadrant outside those vanishing at `x`. -/
private def stratumProj (x : M) (hx : #(zeroCoords n x) = k) (h : EuclideanQuadrant n) :
    EuclideanSpace ℝ (Fin (n - k)) :=
  (splitEquiv (zeroCoords n x) hx ((𝓡c n) h)).1

private theorem stratumParam_eq_of_nonneg {x : M} {hx : #(zeroCoords n x) = k}
    {w : EuclideanSpace ℝ (Fin (n - k))} (hw : ∀ j, 0 ≤ w j) :
    (𝓡c n) (stratumParam k x hx w) = (splitEquiv (zeroCoords n x) hx).symm (w, 0) := by
  refine (𝓡c n).right_inv ?_
  rw [range_modelWithCornersEuclideanQuadrant]
  intro i
  by_cases hi : i ∈ zeroCoords n x
  · rw [splitEquiv_symm_apply_of_mem w hi]
  · exact (forall_splitEquiv_symm_iff (0 ≤ ·) w).2 hw i hi

private theorem stratumParam_apply_of_mem {x : M} {hx : #(zeroCoords n x) = k}
    (w : EuclideanSpace ℝ (Fin (n - k))) {i : Fin n} (hi : i ∈ zeroCoords n x) :
    (stratumParam k x hx w).1 i = 0 := by
  simp [stratumParam, modelWithCornersEuclideanQuadrant_symm_apply,
    splitEquiv_symm_apply_of_mem w hi]

private theorem coe_stratumAmbientChart (x : M) :
    ⇑(stratumAmbientChart n x) = chartAt (EuclideanQuadrant n) x :=
  (rfl)

private theorem coe_stratumAmbientChart_symm (x : M) :
    ⇑(stratumAmbientChart n x).symm = (chartAt (EuclideanQuadrant n) x).symm :=
  (rfl)

private theorem stratumAmbientChart_source (x : M) :
    (stratumAmbientChart n x).source = stratumDomain n x :=
  inter_eq_right.2 inter_subset_left

private theorem mem_stratumAmbientChart_target {x : M} {h : EuclideanQuadrant n} :
    h ∈ (stratumAmbientChart n x).target ↔
      h ∈ (chartAt (EuclideanQuadrant n) x).target ∧
        (chartAt (EuclideanQuadrant n) x).symm h ∈ stratumDomain n x :=
  Iff.rfl

/-- A point of the restricted chart target in the image of the parametrization has positive
inserted coordinates. -/
private theorem pos_of_mem_target {x : M} {hx : #(zeroCoords n x) = k}
    {w : EuclideanSpace ℝ (Fin (n - k))}
    (hw : stratumParam k x hx w ∈ (stratumAmbientChart n x).target) : ∀ j, 0 < w j := by
  obtain ⟨h₁, h₂⟩ := mem_stratumAmbientChart_target.1 hw
  refine (forall_splitEquiv_symm_iff (hZ := hx) (0 < ·) w).1 fun i hi ↦ ?_
  have h := h₂.2 i hi
  rw [(chartAt (EuclideanQuadrant n) x).right_inv h₁] at h
  simpa [stratumParam, modelWithCornersEuclideanQuadrant_symm_apply] using h

private theorem stratumProj_stratumParam {x : M} {hx : #(zeroCoords n x) = k}
    {w : EuclideanSpace ℝ (Fin (n - k))}
    (hw : stratumParam k x hx w ∈ (stratumAmbientChart n x).target) :
    stratumProj x hx (stratumParam k x hx w) = w := by
  rw [stratumProj, stratumParam_eq_of_nonneg fun j ↦ (pos_of_mem_target hw j).le,
    ContinuousLinearEquiv.apply_symm_apply]

variable [IsManifold (𝓡c n) 1 M]

/-- The depth of a point `y` of the domain of the preferred chart at `x` counts the vanishing
coordinates of its image in that chart. -/
private theorem depth_eq_card {x y : M} (hy : y ∈ (chartAt (EuclideanQuadrant n) x).source) :
    (𝓡c n).depth y = #{i | (chartAt (EuclideanQuadrant n) x y).1 i = 0} := by
  rw [ModelWithCorners.depth_modelWithCornersEuclideanQuadrant one_ne_zero
    (IsManifold.chart_mem_maximalAtlas x) hy, Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem card_zeroCoords (x : M) : #(zeroCoords n x) = (𝓡c n).depth x :=
  (depth_eq_card (mem_chart_source _ x)).symm

/-- On `stratumDomain n x`, the points of the depth of `x` are those whose image in the chart at
`x` vanishes on `zeroCoords n x`. -/
private theorem depth_eq_iff {x y : M} (hy : y ∈ stratumDomain n x) :
    (𝓡c n).depth y = (𝓡c n).depth x ↔
      ∀ i ∈ zeroCoords n x, (chartAt (EuclideanQuadrant n) x y).1 i = 0 := by
  rw [depth_eq_card hy.1, ← card_zeroCoords]
  have hsub : ({i | (chartAt (EuclideanQuadrant n) x y).1 i = 0} : Finset (Fin n)) ⊆
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
    splitEquiv_symm_fst (by simpa using hZ), ModelWithCorners.left_inv]

private theorem card_zeroCoords_eq (p : (𝓡c n).depthStratum M k) : #(zeroCoords n p.1) = k :=
  (card_zeroCoords p.1).trans p.2

/- The two slice conditions of `OpenPartialHomeomorph.subtypeCoord` for the chart at `p`, stated
with the binders of that construction so that its lemmas can be applied to them below. -/

private theorem stratumChart_mapsTo (p : (𝓡c n).depthStratum M k) :
    ∀ {w}, stratumParam k p.1 (card_zeroCoords_eq p) w ∈ (stratumAmbientChart n p.1).target →
      (stratumAmbientChart n p.1).symm (stratumParam k p.1 (card_zeroCoords_eq p) w) ∈
        (𝓡c n).depthStratum M k :=
  fun hw ↦ symm_stratumParam_mem hw

private theorem stratumChart_slice (p : (𝓡c n).depthStratum M k) :
    ∀ {y}, y ∈ (stratumAmbientChart n p.1).source → y ∈ (𝓡c n).depthStratum M k →
      stratumParam k p.1 (card_zeroCoords_eq p)
          (stratumProj p.1 (card_zeroCoords_eq p) (stratumAmbientChart n p.1 y)) =
        stratumAmbientChart n p.1 y :=
  fun hy hyk ↦ stratumParam_stratumProj hy hyk

/-- The chart of the depth-`k` stratum at `p`: the ambient chart at `p`, restricted to the stratum
near `p`, with the coordinates vanishing at `p` deleted. -/
private def stratumChart (p : (𝓡c n).depthStratum M k) :
    OpenPartialHomeomorph ((𝓡c n).depthStratum M k) (EuclideanSpace ℝ (Fin (n - k))) :=
  (stratumAmbientChart n p.1).subtypeCoord _ ⟨p⟩ (stratumParam k p.1 (card_zeroCoords_eq p))
    (stratumProj p.1 (card_zeroCoords_eq p)) (stratumChart_mapsTo p) (stratumChart_slice p)
    (fun _ hw ↦ stratumProj_stratumParam hw)
    ((𝓡c n).continuous_symm.comp ((splitEquiv _ _).symm.continuous.comp
      (Continuous.prodMk_left 0)))
    (Continuous.continuousOn (continuous_fst.comp ((splitEquiv _ _).continuous.comp
      (𝓡c n).continuous)))

/- The lemmas of `OpenPartialHomeomorph.subtypeCoord` are applied with the slice conditions given
in fully explicit form: passed with `_`, or without `@`, their implicit binders are instantiated
and elaboration has to unfold the chart to match them. -/

private theorem stratumChart_apply (p q : (𝓡c n).depthStratum M k) :
    stratumChart p q =
      stratumProj p.1 (card_zeroCoords_eq p) (chartAt (EuclideanQuadrant n) p.1 q.1) := by
  unfold stratumChart
  exact OpenPartialHomeomorph.subtypeCoord_apply (stratumAmbientChart n p.1) _ ⟨p⟩
    (stratumParam k p.1 (card_zeroCoords_eq p)) (stratumProj p.1 (card_zeroCoords_eq p))
    (@stratumChart_mapsTo n k M _ _ _ p) (@stratumChart_slice n k M _ _ _ p) _ _ _ q

private theorem stratumChart_source (p : (𝓡c n).depthStratum M k) :
    (stratumChart p).source = Subtype.val ⁻¹' stratumDomain n p.1 := by
  rw [← stratumAmbientChart_source]
  unfold stratumChart
  exact OpenPartialHomeomorph.subtypeCoord_source (stratumAmbientChart n p.1) _ ⟨p⟩
    (stratumParam k p.1 (card_zeroCoords_eq p)) (stratumProj p.1 (card_zeroCoords_eq p))
    (@stratumChart_mapsTo n k M _ _ _ p) (@stratumChart_slice n k M _ _ _ p) _ _ _

private theorem stratumChart_target (p : (𝓡c n).depthStratum M k) :
    (stratumChart p).target =
      stratumParam k p.1 (card_zeroCoords_eq p) ⁻¹' (stratumAmbientChart n p.1).target := by
  unfold stratumChart
  exact OpenPartialHomeomorph.subtypeCoord_target (stratumAmbientChart n p.1) _ ⟨p⟩
    (stratumParam k p.1 (card_zeroCoords_eq p)) (stratumProj p.1 (card_zeroCoords_eq p))
    (@stratumChart_mapsTo n k M _ _ _ p) (@stratumChart_slice n k M _ _ _ p) _ _ _

private theorem coe_stratumChart_symm_apply (p : (𝓡c n).depthStratum M k)
    {w : EuclideanSpace ℝ (Fin (n - k))} (hw : w ∈ (stratumChart p).target) :
    ((stratumChart p).symm w : M) =
      (chartAt (EuclideanQuadrant n) p.1).symm (stratumParam k p.1 (card_zeroCoords_eq p) w) := by
  rw [stratumChart_target] at hw
  unfold stratumChart
  exact OpenPartialHomeomorph.coe_subtypeCoord_symm_apply (stratumAmbientChart n p.1) _ ⟨p⟩
    (stratumParam k p.1 (card_zeroCoords_eq p)) (stratumProj p.1 (card_zeroCoords_eq p))
    (@stratumChart_mapsTo n k M _ _ _ p) (@stratumChart_slice n k M _ _ _ p) _ _ _ hw

/-- The transition maps between stratum charts are `C^r`: through the coordinate splittings at the
two base points they are the ambient transition maps, restricted to a coordinate face. -/
private theorem contDiffOn_stratumChart_symm_trans {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M]
    (p q : (𝓡c n).depthStratum M k) :
    ContDiffOn ℝ r ((stratumChart p).symm ≫ₕ stratumChart q)
      ((stratumChart p).symm ≫ₕ stratumChart q).source := by
  have hg : (chartAt (EuclideanQuadrant n) p.1).symm ≫ₕ chartAt (EuclideanQuadrant n) q.1 ∈
      contDiffGroupoid r (𝓡c n) :=
    StructureGroupoid.compatible _ (chart_mem_atlas _ _) (chart_mem_atlas _ _)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  -- The ambient transition map, read between the two coordinate splittings.
  set A := (ContinuousLinearMap.fst ℝ _ _).comp
    (splitEquiv (zeroCoords n q.1) (card_zeroCoords_eq q) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - k)) × EuclideanSpace ℝ (Fin k))
  set B := ((splitEquiv (zeroCoords n p.1) (card_zeroCoords_eq p)).symm :
      EuclideanSpace ℝ (Fin (n - k)) × EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
    (ContinuousLinearMap.inl ℝ _ _)
  refine ContDiffOn.congr (f := A ∘
      ((𝓡c n) ∘ ((chartAt (EuclideanQuadrant n) p.1).symm ≫ₕ chartAt (EuclideanQuadrant n) q.1) ∘
        (𝓡c n).symm) ∘ B)
    (A.contDiff.comp_contDiffOn (hg.1.comp B.contDiff.contDiffOn fun w hw ↦ ?_)) fun w hw ↦ ?_
  · obtain ⟨hw₁, hw₂⟩ := hw
    simp only [OpenPartialHomeomorph.symm_symm] at hw₁ hw₂
    rw [stratumChart_source] at hw₂
    have hw₃ : ((stratumChart p).symm w : M) ∈ stratumDomain n q.1 := hw₂
    rw [coe_stratumChart_symm_apply p hw₁] at hw₃
    rw [stratumChart_target] at hw₁
    exact ⟨⟨hw₁.1, hw₃.1⟩, _, stratumParam_eq_of_nonneg fun j ↦ (pos_of_mem_target hw₁ j).le⟩
  · have hw₁ : w ∈ (stratumChart p).target := hw.1
    rw [OpenPartialHomeomorph.coe_trans, comp_apply, stratumChart_apply,
      coe_stratumChart_symm_apply p hw₁]
    simp [A, B, stratumProj, stratumParam]

/-- The canonical charted-space structure on the depth-`k` stratum of a `C^1` manifold modelled
on the quadrant `[0, ∞)ⁿ`, modelled on `ℝⁿ⁻ᵏ`. The chart at `p` is the preferred ambient chart at
`p`, restricted to the points near `p` where the coordinates positive at `p` stay positive, with
the `k` coordinates vanishing at `p` deleted. The implementation is opaque; use
`TauCeti.depthStratumChartedSpace_atlas`, `TauCeti.isManifold_depthStratum` and
`TauCeti.isImmersion_subtypeVal_depthStratum`. -/
@[irreducible, instance] noncomputable def depthStratumChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n - k))) ((𝓡c n).depthStratum M k) where
  atlas := range stratumChart
  chartAt := stratumChart
  mem_chart_source p := by
    rw [stratumChart_source]
    exact mem_stratumDomain p.1
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

/-- **The depth-`k` stratum of a `C^r` manifold modelled on the quadrant `[0, ∞)ⁿ` is a `C^r`
manifold without boundary**, modelled on `ℝⁿ⁻ᵏ`. -/
instance isManifold_depthStratum {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) r ((𝓡c n).depthStratum M k) := by
  refine isManifold_of_contDiffOn _ r _ ?_
  rw [depthStratumChartedSpace_atlas]
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
  simpa [depthStratumChartedSpace_chartAt] using contDiffOn_stratumChart_symm_trans p q

/-- The inclusion of the depth-`k` stratum of a `C^r` manifold modelled on the quadrant `[0, ∞)ⁿ`
is a `C^r` immersion: in the stratum chart and the ambient chart at a point it is a linear
coordinate inclusion `ℝⁿ⁻ᵏ → ℝⁿ`, with complement `ℝᵏ`. -/
theorem isImmersion_subtypeVal_depthStratum {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M] :
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) r
      (Subtype.val : (𝓡c n).depthStratum M k → M) := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin k))
  intro p
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt
    (splitEquiv (zeroCoords n p.1) (card_zeroCoords_eq p)).symm (chartAt _ p)
    (chartAt (EuclideanQuadrant n) p.1) (mem_chart_source _ p) (mem_chart_source _ p.1)
    (IsManifold.chart_mem_maximalAtlas p) (IsManifold.chart_mem_maximalAtlas p.1)
  intro w hw
  rw [OpenPartialHomeomorph.extend_target, depthStratumChartedSpace_chartAt] at hw
  have hw₁ : w ∈ (stratumChart p).target := by simpa using hw.1
  have hw₂ := hw₁
  rw [stratumChart_target] at hw₂
  simp only [comp_apply, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe_symm, id_eq, depthStratumChartedSpace_chartAt,
    coe_stratumChart_symm_apply p hw₁]
  rw [(chartAt (EuclideanQuadrant n) p.1).right_inv hw₂.1,
    stratumParam_eq_of_nonneg fun j ↦ (pos_of_mem_target hw₂ j).le]

/-- The inclusion of the depth-`k` stratum of a `C^r` manifold modelled on the quadrant `[0, ∞)ⁿ`
is a `C^r` smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_depthStratum {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M] :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) r
      (Subtype.val : (𝓡c n).depthStratum M k → M) :=
  ⟨isImmersion_subtypeVal_depthStratum, IsEmbedding.subtypeVal⟩

end Quadrant

end TauCeti
