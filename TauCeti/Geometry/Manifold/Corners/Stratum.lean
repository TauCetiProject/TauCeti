/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.LocallyClosed
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Corners.Depth
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Geometry.Manifold.Corners.LocalQuadrant
import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The depth strata of a manifold with corners

A manifold with corners `M` is partitioned by the depth of its points
(`ModelWithCorners.depth`): its *depth-`k` stratum* `I.depthStratum M k` is the set of points of
depth `k`. When the model vector space `E` is finite-dimensional, the depth-zero stratum is the
interior `I.interior M`, the strata of positive depth partition the boundary `I.boundary M`, on a
product manifold `(I.prod I').depthStratum (M × N) k` decomposes into products of complementary
depth strata, and on a manifold with boundary modelled on the half-space the depth-one stratum is
the boundary and there are no strata of depth greater than one. `C¹` local diffeomorphisms and
diffeomorphisms preserve depth strata, and on any manifold locally `C¹`-diffeomorphic to open
subsets of a Euclidean quadrant (in particular, any `C¹` manifold whose model range is cut out by
nonnegative coordinates in a finite linear coordinate system), every depth stratum is locally closed
(`ModelWithCorners.isLocallyClosed_depthStratum_of_local_quadrant`,
`ModelWithCorners.isLocallyClosed_depthStratum_of_range_eq_equiv`). The strata of higher depth are
the edges and vertices of the corners: on the cube `[0, 1]³` the strata of depth `0, 1, 2, 3` are
the open cube, the six open faces, the twelve open edges and the eight vertices.

The main point of this file is that on a `C¹` manifold modelled on the quadrant `[0, ∞)ⁿ` — and, by
transport along local quadrant charts (`ModelWithCorners.localQuadrantHomeomorph`), on any `C¹`
manifold whose model range is cut out by nonnegative coordinates under a finite linear coordinate
equivalence `L : E ≃L[ℝ] (ι → ℝ)` — every stratum is itself a manifold, without boundary and of
the expected dimension: on the quadrant `[0, ∞)²` the boundary, an L-shaped union of two
half-axes, is not a smooth submanifold of `ℝ²` at the origin, where it has a corner, whereas its
strata, the two open half-axes, of depth `1`, and the origin, of depth `2`, are.

* For `M` modelled on `[0, ∞)ⁿ`, `(𝓡c n).depthStratum M k` carries a canonical charted-space
  instance modelled on `ℝⁿ⁻ᵏ` (`TauCeti.depthStratumChartedSpace`), of class `C^r` whenever `M` is
  (`TauCeti.isManifold_depthStratum`), and its inclusion is a `C^r` smooth embedding
  (`TauCeti.isSmoothEmbedding_subtypeVal_depthStratum`) whose tangent image at `p` consists of the
  vectors vanishing on the `k` coordinates that vanish at `p`
  (`TauCeti.mem_range_mfderiv_subtypeVal_depthStratum_iff`). Consequently smoothness into a depth
  stratum is tested after composing with `Subtype.val`
  (`TauCeti.contMDiff_iff_comp_subtypeVal_depthStratum`), `C^r` diffeomorphisms (`r ≠ 0`) restrict
  to `C^r` diffeomorphisms of depth strata (`Diffeomorph.depthStratum`), and the depth-zero stratum
  is canonically `C^r`-diffeomorphic to the open interior submanifold
  (`TauCeti.depthStratumZeroDiffeomorphInterior`).
* More generally, for any finite coordinate equivalence `L : E ≃L[ℝ] (ι → ℝ)` with
  `range I = {y | ∀ i ∈ S, 0 ≤ L y i}`, `ModelWithCorners.depthStratumChartedSpace` equips
  `I.depthStratum M k` with a boundaryless `C^r` manifold structure of dimension `finrank ℝ E - k`
  (`ModelWithCorners.isManifold_depthStratum`) whose inclusion into `M` is a `C^r` smooth embedding
  (`ModelWithCorners.isSmoothEmbedding_subtypeVal_depthStratum`,
  `ModelWithCorners.contMDiff_iff_comp_subtypeVal_depthStratum`). Any `C^r` diffeomorphism (`r ≠ 0`)
  between two such manifolds induces a `C^r` diffeomorphism between their depth-`k` strata
  (`ModelWithCorners.depthStratumDiffeomorph`, proving independence of `(L, S)`), the depth-zero
  stratum is `C^r`-diffeomorphic to the open interior submanifold
  (`ModelWithCorners.depthStratumZeroDiffeomorphInterior`), the quadrant specialisation is
  `C^r`-diffeomorphic to `TauCeti.depthStratumChartedSpace`
  (`ModelWithCorners.depthStratumQuadrantDiffeomorph`), and on a half-space manifold modelled on
  `𝓡∂ (n + 1)` the depth-one stratum is canonically `C^r`-diffeomorphic to the boundary manifold of
  `TauCeti.boundaryChartedSpace` (`ModelWithCorners.depthStratumOneDiffeomorphBoundary`).

The ambient `C^1` structure is needed already to form the charts: without it the depth may depend on
the chart. Its topology is the subspace topology, so it inherits Hausdorffness and second
countability from `M`. This is what lets statements proved for manifolds without boundary, such as
Sard's theorem, be applied to manifolds with corners one stratum at a time.

## Main definitions

* `ModelWithCorners.depthStratum`: the depth-`k` stratum of a manifold with corners.
* `TauCeti.depthStratumChartedSpace`: the canonical charted-space instance on
  `(𝓡c n).depthStratum M k`, modelled on `EuclideanSpace ℝ (Fin (n - k))`.
* `TauCeti.depthStratumZeroDiffeomorphInterior`, `Diffeomorph.depthStratum`: interior comparison and
  functorial stratum diffeomorphisms (`r ≠ 0`) for quadrant manifolds.
* `ModelWithCorners.depthStratumChartedSpace`: charted-space structure on `I.depthStratum M k` for
  any finite coordinate-nonnegative model `(L, S)`, modelled on
  `EuclideanSpace ℝ (Fin (finrank ℝ E - k))`.
* `ModelWithCorners.depthStratumDiffeomorph`,
  `ModelWithCorners.depthStratumZeroDiffeomorphInterior`,
  `ModelWithCorners.depthStratumQuadrantDiffeomorph`,
  `ModelWithCorners.depthStratumOneDiffeomorphBoundary`: functorial diffeomorphisms (`r ≠ 0`) and
  canonical identifications with the interior, the quadrant stratum instance, and the half-space
  boundary manifold.

## Main results

* `ModelWithCorners.iUnion_depthStratum`, `ModelWithCorners.biUnion_le_finrank_depthStratum`,
  `ModelWithCorners.pairwise_disjoint_depthStratum`,
  `ModelWithCorners.depthStratum_eq_empty_of_finrank_lt`, `ModelWithCorners.depthStratum_prod`: the
  strata partition the manifold, only strata of depth at most its dimension are nonempty, and
  product strata decompose into products of complementary strata.
* `ModelWithCorners.depthStratum_zero`, `ModelWithCorners.biUnion_pos_depthStratum`: the depth-zero
  stratum is the interior and the positive-depth strata cover the boundary.
* `Diffeomorph.image_depthStratum`, `Diffeomorph.preimage_depthStratum`,
  `IsLocalDiffeomorph.preimage_depthStratum`: `C¹` (local) diffeomorphisms preserve depth strata.
* `ModelWithCorners.isLocallyClosed_depthStratum_of_local_quadrant`,
  `ModelWithCorners.isLocallyClosed_depthStratum_of_range_eq_equiv`,
  `ModelWithCorners.isLocallyClosed_depthStratum_modelWithCornersEuclideanQuadrant`: depth strata
  are locally closed.
* `ModelWithCorners.depthStratum_modelWithCornersEuclideanHalfSpace_one`,
  `ModelWithCorners.depthStratum_modelWithCornersEuclideanHalfSpace_eq_empty_of_one_lt`: on a
  manifold modelled on the half-space, the depth-one stratum is the boundary and there are no
  strata of higher depth.
* `TauCeti.card_filter_chartAt_eq_of_mem_depthStratum`,
  `TauCeti.depthStratumChartedSpace_atlas`, `TauCeti.depthStratumChartedSpace_chartAt_source` and
  its companions: preferred charts of `(𝓡c n).depthStratum M k`.
* `TauCeti.isManifold_depthStratum`, `TauCeti.isImmersion_subtypeVal_depthStratum`,
  `TauCeti.isSmoothEmbedding_subtypeVal_depthStratum`,
  `TauCeti.mem_range_mfderiv_subtypeVal_depthStratum_iff`,
  `TauCeti.contMDiffWithinAt_iff_comp_subtypeVal_depthStratum`,
  `TauCeti.contMDiff_iff_comp_subtypeVal_depthStratum`: smooth manifold structure, embedding,
  tangent image, and universal property for quadrant depth strata.
* `ModelWithCorners.depthStratumChartedSpace_atlas`, `ModelWithCorners.isManifold_depthStratum`,
  `ModelWithCorners.isImmersion_subtypeVal_depthStratum`,
  `ModelWithCorners.isSmoothEmbedding_subtypeVal_depthStratum`,
  `ModelWithCorners.contMDiffWithinAt_iff_comp_subtypeVal_depthStratum`,
  `ModelWithCorners.contMDiff_iff_comp_subtypeVal_depthStratum`: smooth manifold structure,
  embedding, and universal property for depth strata of coordinate-nonnegative models.

## References

* D. Joyce, *On manifolds with corners*, in Advances in Geometric Analysis, Adv. Lect. Math. 21,
  International Press, 2012, 225–258, §2 (the depth stratification).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 16, section *Manifolds with Corners*.

The formal construction of the quadrant stratum charts follows that of the boundary charts of a
manifold modelled on the half-space, `TauCeti.boundaryChartedSpace` in
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

theorem depthStratum_def (k : ℕ) : I.depthStratum M k = {x | I.depth x = k} :=
  (rfl)

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

/-- The depth strata of depth at most `finrank ℝ E` cover the manifold. -/
@[simp]
theorem biUnion_le_finrank_depthStratum :
    (⋃ k ≤ finrank ℝ E, I.depthStratum M k) = univ :=
  eq_univ_of_forall fun x ↦ mem_iUnion₂.2 ⟨I.depth x, I.depth_le_finrank x, rfl⟩

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

/-- On a boundaryless manifold, every stratum of positive depth is empty. -/
theorem depthStratum_eq_empty_of_boundaryless [BoundarylessManifold I M] {k : ℕ} (hk : k ≠ 0) :
    I.depthStratum M k = ∅ := by
  by_cases hE : FiniteDimensional ℝ E
  · refine eq_empty_of_forall_notMem fun x hx ↦ hk ?_
    rw [mem_depthStratum] at hx
    exact hx.symm.trans (I.depth_eq_zero_iff.2 BoundarylessManifold.isInteriorPoint)
  · exact depthStratum_eq_empty_of_finrank_lt
      (by rw [finrank_of_infinite_dimensional hE]; exact Nat.pos_of_ne_zero hk)

/-- A `C^m` local diffeomorphism (`m ≠ 0`) pulls back each depth stratum to the corresponding depth
stratum. -/
theorem _root_.IsLocalDiffeomorph.preimage_depthStratum
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m : WithTop ℕ∞} (hm : m ≠ 0) {f : M → N} (hf : IsLocalDiffeomorph I I' m f) (k : ℕ) :
    f ⁻¹' I'.depthStratum N k = I.depthStratum M k := by
  ext x
  simp only [mem_preimage, mem_depthStratum, (hf x).depth_eq hm]

/-- Preimage of a depth stratum under a `C^m` diffeomorphism (`m ≠ 0`). -/
theorem _root_.Diffeomorph.preimage_depthStratum
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m : WithTop ℕ∞} (hm : m ≠ 0) (Φ : M ≃ₘ^m⟮I, I'⟯ N) (k : ℕ) :
    Φ ⁻¹' I'.depthStratum N k = I.depthStratum M k :=
  Φ.isLocalDiffeomorph.preimage_depthStratum hm k

/-- A `C^m` diffeomorphism (`m ≠ 0`) maps each depth stratum onto the corresponding depth
stratum. -/
theorem _root_.Diffeomorph.image_depthStratum
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m : WithTop ℕ∞} (hm : m ≠ 0) (Φ : M ≃ₘ^m⟮I, I'⟯ N) (k : ℕ) :
    Φ '' I.depthStratum M k = I'.depthStratum N k :=
  (Φ.toEquiv.image_eq_preimage_symm _).trans (Φ.symm.preimage_depthStratum hm k)

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

/-- Every stratum of positive depth lies in the boundary of the manifold. -/
theorem depthStratum_subset_boundary {k : ℕ} (hk : k ≠ 0) :
    I.depthStratum M k ⊆ I.boundary M := fun _ hx ↦
  I.depth_pos_iff.1 (hx ▸ Nat.pos_of_ne_zero hk)

/-- The strata of positive depth cover the boundary of the manifold. -/
theorem biUnion_pos_depthStratum : (⋃ k ≥ 1, I.depthStratum M k) = I.boundary M := by
  ext x
  simp only [mem_iUnion, mem_depthStratum, ModelWithCorners.boundary, mem_ofPred_eq,
    ← I.depth_pos_iff]
  exact ⟨fun ⟨_, hk, hkx⟩ ↦ hkx ▸ hk, fun hx ↦ ⟨I.depth x, hx, rfl⟩⟩

/-- Depth strata of a product manifold are unions of products of complementary depth strata. -/
theorem depthStratum_prod
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] (k : ℕ) :
    (I.prod I').depthStratum (M × N) k =
      ⋃ i ≤ k, I.depthStratum M i ×ˢ I'.depthStratum N (k - i) := by
  ext ⟨x, y⟩
  simp only [mem_depthStratum, depth_prod, mem_iUnion, mem_prod]
  exact ⟨fun h ↦ ⟨I.depth x, by omega, rfl, by omega⟩, fun ⟨i, _, h₁, h₂⟩ ↦ by omega⟩

omit [FiniteDimensional ℝ E] in
/-- Every depth stratum of a manifold locally `C¹`-diffeomorphic to open subsets of
`EuclideanQuadrant (finrank ℝ E)` is locally closed. -/
theorem isLocallyClosed_depthStratum_of_local_quadrant
    (hloc : ∀ x : M, ∃ (U : TopologicalSpace.Opens M)
      (V : TopologicalSpace.Opens (EuclideanQuadrant (finrank ℝ E))),
      x ∈ U ∧ Nonempty (U ≃ₘ^1⟮I, 𝓡c (finrank ℝ E)⟯ V))
    (k : ℕ) : IsLocallyClosed (I.depthStratum M k) := by
  have heq : I.depthStratum M k = {x : M | I.depth x ≤ k} ∩ {x : M | k ≤ I.depth x} := by
    ext x
    simp only [mem_depthStratum, mem_inter_iff, mem_ofPred_eq]
    omega
  rw [heq]
  exact (isOpen_setOf_depth_le_of_local_quadrant hloc k).isLocallyClosed.inter
    (isClosed_setOf_le_depth_of_local_quadrant hloc k).isLocallyClosed

omit [FiniteDimensional ℝ E] in
/-- Every depth stratum of a `C¹` manifold whose model range is cut out by nonnegative coordinates
in a linear coordinate system is locally closed. -/
theorem isLocallyClosed_depthStratum_of_range_eq_equiv {ι : Type*} [Finite ι]
    (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι} (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] (k : ℕ) :
    IsLocallyClosed (I.depthStratum M k) :=
  isLocallyClosed_depthStratum_of_local_quadrant
    (exists_opens_diffeomorph_opens_euclideanQuadrant_of_range_eq_equiv L hI) k

omit [FiniteDimensional ℝ E] in
/-- Every depth stratum of a `C¹` manifold modelled on `𝓡c d` is locally closed. -/
theorem isLocallyClosed_depthStratum_modelWithCornersEuclideanQuadrant {d : ℕ}
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanQuadrant d) X]
    [IsManifold (𝓡c d) 1 X] (k : ℕ) :
    IsLocallyClosed ((𝓡c d).depthStratum X k) :=
  isLocallyClosed_depthStratum_of_range_eq_equiv (EuclideanSpace.equiv (Fin d) ℝ)
    (range_modelWithCornersEuclideanQuadrant_eq d) k

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

private theorem isOpen_stratumDomain (x : M) : IsOpen (stratumDomain n x) :=
  (chartAt (EuclideanQuadrant n) x).continuousOn.isOpen_inter_preimage
    (chartAt (EuclideanQuadrant n) x).open_source <|
    isOpen_setOf_forall_pos (· ∉ zeroCoords n x) fun i ↦
      (PiLp.continuous_apply 2 _ i).comp continuous_subtypeVal

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

private theorem writtenInExtChartAt_subtypeVal_depthStratum_apply
    (p : (𝓡c n).depthStratum M k) {w : EuclideanSpace ℝ (Fin (n - k))}
    (hw : w ∈ (stratumChart p).target) :
    writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) p
      (Subtype.val : (𝓡c n).depthStratum M k → M) w =
      (finsetComplEquivProd ℝ (zeroCoords n p.val) (card_zeroCoords_eq p)).symm (w, 0) := by
  obtain ⟨hw₁, hw₂⟩ := stratumParam_mem_target_of_mem hw
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, id_eq, comp_apply,
    depthStratumChartedSpace_chartAt, coe_stratumChart_symm_apply p hw]
  rw [(chartAt (EuclideanQuadrant n) p.val).right_inv hw₁, hw₂]

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
  exact writtenInExtChartAt_subtypeVal_depthStratum_apply p (by simpa using hw.1)

/-- The inclusion of the depth-`k` stratum of a `C^1` manifold modelled on the quadrant `[0, ∞)ⁿ`
that is `C^r` is a `C^r` smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_depthStratum {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M] :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) r
      (Subtype.val : (𝓡c n).depthStratum M k → M) :=
  ⟨isImmersion_subtypeVal_depthStratum, IsEmbedding.subtypeVal⟩

/-- The inclusion of the depth-`k` stratum into the ambient quadrant manifold is `C^r`. -/
theorem contMDiff_subtypeVal_depthStratum {r : ℕ∞ω} [IsManifold (𝓡c n) r M] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) r
      (Subtype.val : (𝓡c n).depthStratum M k → M) :=
  isSmoothEmbedding_subtypeVal_depthStratum.contMDiff

/-- At `p : (𝓡c n).depthStratum M k`, the manifold derivative of `Subtype.val` read through
`tangentSpaceCastModel` inserts zeros at the `k` coordinates vanishing at `p` in its preferred
ambient chart. -/
theorem tangentSpaceCastModel_mfderiv_subtypeVal_depthStratum_apply
    (p : (𝓡c n).depthStratum M k)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) p) :
    tangentSpaceCastModel (𝓡c n) p.val
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n)
          (Subtype.val : (𝓡c n).depthStratum M k → M) p w) =
      (finsetComplEquivProd ℝ _ (card_filter_chartAt_eq_of_mem_depthStratum p.prop)).symm
        (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) p w, 0) := by
  have hdiff : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n)
      (Subtype.val : (𝓡c n).depthStratum M k → M) p :=
    (contMDiff_subtypeVal_depthStratum (r := 1) p).mdifferentiableAt one_ne_zero
  set B : EuclideanSpace ℝ (Fin (n - k)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((finsetComplEquivProd ℝ (zeroCoords n p.val) (card_zeroCoords_eq p)).symm :
      EuclideanSpace ℝ (Fin (n - k)) × EuclideanSpace ℝ (Fin k) →L[ℝ]
        EuclideanSpace ℝ (Fin n)).comp
      (ContinuousLinearMap.inl ℝ _ _)
  have htgt : (stratumChart p).target ∈
      𝓝 (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) p p) := by
    refine (stratumChart p).open_target.mem_nhds ?_
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, id_comp,
      depthStratumChartedSpace_chartAt]
    exact (stratumChart p).map_source (by rw [stratumChart_source]; exact mem_stratumDomain p.val)
  have hev : writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n) p
      (Subtype.val : (𝓡c n).depthStratum M k → M) =ᶠ[
        𝓝 (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) p p)] B := by
    filter_upwards [htgt] with z hz
    rw [writtenInExtChartAt_subtypeVal_depthStratum_apply p hz]
    simp only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearEquiv.coe_coe]
  rw [hdiff.mfderiv]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ,
    ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.coe_coe, hev.fderiv_eq, B.fderiv]
  simp only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearEquiv.coe_coe, zeroCoords]

/-- A tangent vector `v` at `p.val` lies in the tangent image of the depth-`k` stratum at `p`
if and only if `v` vanishes on every coordinate that vanishes at `p` in its preferred ambient
chart. -/
theorem mem_range_mfderiv_subtypeVal_depthStratum_iff (p : (𝓡c n).depthStratum M k)
    (v : TangentSpace (𝓡c n) p.val) :
    v ∈ LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) (𝓡c n)
        (Subtype.val : (𝓡c n).depthStratum M k → M) p).toLinearMap ↔
      ∀ i : Fin n, (chartAt (EuclideanQuadrant n) p.val p.val).val i = 0 →
        tangentSpaceCastModel (𝓡c n) p.val v i = 0 := by
  rw [LinearMap.mem_range]
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨w, rfl⟩ i hi
    rw [ContinuousLinearMap.coe_coe,
      tangentSpaceCastModel_mfderiv_subtypeVal_depthStratum_apply]
    exact finsetComplEquivProd_symm_mk_zero_apply_of_mem _ (by simpa using hi)
  · refine ⟨(tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) p).symm
      (finsetComplEquivProd ℝ _ (card_filter_chartAt_eq_of_mem_depthStratum p.prop)
        (tangentSpaceCastModel (𝓡c n) p.val v)).1, ?_⟩
    apply (tangentSpaceCastModel (𝓡c n) p.val).injective
    rw [ContinuousLinearMap.coe_coe,
      tangentSpaceCastModel_mfderiv_subtypeVal_depthStratum_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    exact finsetComplEquivProd_symm_mk_fst_zero (by simpa using hv)

section Universal

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  {r : ℕ∞ω} [IsManifold (𝓡c n) r M]

/-- **Universal property of a depth stratum:** a map into `(𝓡c n).depthStratum M k` is `C^r` within
a set at a point if and only if its composite with `Subtype.val` is `C^r` within that set. -/
theorem contMDiffWithinAt_iff_comp_subtypeVal_depthStratum
    {f : X → (𝓡c n).depthStratum M k} {s : Set X} {x : X} :
    ContMDiffWithinAt IX 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) r f s x ↔
      ContMDiffWithinAt IX (𝓡c n) r (Subtype.val ∘ f) s x :=
  (isSmoothEmbedding_subtypeVal_depthStratum (r := r)).contMDiffWithinAt_iff_comp

/-- A map into `(𝓡c n).depthStratum M k` is `C^r` if and only if its composite with `Subtype.val`
is `C^r`. -/
theorem contMDiff_iff_comp_subtypeVal_depthStratum {f : X → (𝓡c n).depthStratum M k} :
    ContMDiff IX 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) r f ↔
      ContMDiff IX (𝓡c n) r (Subtype.val ∘ f) :=
  (isSmoothEmbedding_subtypeVal_depthStratum (r := r)).contMDiff_iff_comp

end Universal

/-- **Comparison with the interior:** the depth-zero stratum `(𝓡c n).depthStratum M 0` is
canonically `C^r`-diffeomorphic to the open interior submanifold
`⟨(𝓡c n).interior M, (𝓡c n).isOpen_interior one_ne_zero⟩`. -/
def depthStratumZeroDiffeomorphInterior {r : ℕ∞ω} [IsManifold (𝓡c n) r M] :
    (𝓡c n).depthStratum M 0 ≃ₘ^r⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 0))), 𝓡c n⟯
      (⟨(𝓡c n).interior M, (𝓡c n).isOpen_interior one_ne_zero⟩ : TopologicalSpace.Opens M) :=
  let U : TopologicalSpace.Opens M := ⟨(𝓡c n).interior M, (𝓡c n).isOpen_interior one_ne_zero⟩
  Homeomorph.diffeomorphOfImmersions
    { toFun := fun x ↦ ⟨x.val, (𝓡c n).depth_eq_zero_iff.1 x.prop⟩
      invFun := fun x ↦ ⟨x.val, (𝓡c n).depth_eq_zero_iff.2 x.prop⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_subtypeVal.subtype_mk _
      continuous_invFun := continuous_subtypeVal.subtype_mk _ }
    isImmersion_subtypeVal_depthStratum
    (Manifold.IsImmersion.of_opens U)
    rfl

@[simp]
theorem coe_depthStratumZeroDiffeomorphInterior_apply {r : ℕ∞ω} [IsManifold (𝓡c n) r M]
    (x : (𝓡c n).depthStratum M 0) :
    ((depthStratumZeroDiffeomorphInterior (r := r) x :
      (⟨(𝓡c n).interior M, (𝓡c n).isOpen_interior one_ne_zero⟩ :
        TopologicalSpace.Opens M)) : M) = x.val := by
  simp [depthStratumZeroDiffeomorphInterior]

@[simp]
theorem coe_depthStratumZeroDiffeomorphInterior_symm_apply {r : ℕ∞ω} [IsManifold (𝓡c n) r M]
    (x : (⟨(𝓡c n).interior M, (𝓡c n).isOpen_interior one_ne_zero⟩ :
      TopologicalSpace.Opens M)) :
    (((depthStratumZeroDiffeomorphInterior (n := n) (M := M) (r := r)).symm x :
      (𝓡c n).depthStratum M 0) : M) = x.val := by
  simp [depthStratumZeroDiffeomorphInterior]

end Quadrant

end TauCeti

namespace Diffeomorph

section DepthStratum

variable {n m l : ℕ} {r : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (𝓡c n) 1 M] [IsManifold (𝓡c n) r M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant m) N]
  [IsManifold (𝓡c m) 1 N] [IsManifold (𝓡c m) r N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace (EuclideanQuadrant l) P]
  [IsManifold (𝓡c l) 1 P] [IsManifold (𝓡c l) r P]

/-- A `C^r` diffeomorphism (`r ≠ 0`) between manifolds modelled on Euclidean quadrants restricts to
a `C^r` diffeomorphism between their depth-`k` strata. -/
def depthStratum (hr : r ≠ 0) (Φ : M ≃ₘ^r⟮𝓡c n, 𝓡c m⟯ N) (k : ℕ) :
    (𝓡c n).depthStratum M k ≃ₘ^r⟮
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))),
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m - k)))⟯
      (𝓡c m).depthStratum N k where
  toFun x := ⟨Φ x.val, (Φ.depth_eq hr x.val).trans x.prop⟩
  invFun y := ⟨Φ.symm y.val, (Φ.symm.depth_eq hr y.val).trans y.prop⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x.val)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y.val)
  contMDiff_toFun :=
    TauCeti.contMDiff_iff_comp_subtypeVal_depthStratum.2
      (Φ.contMDiff.comp TauCeti.contMDiff_subtypeVal_depthStratum)
  contMDiff_invFun :=
    TauCeti.contMDiff_iff_comp_subtypeVal_depthStratum.2
      (Φ.symm.contMDiff.comp TauCeti.contMDiff_subtypeVal_depthStratum)

@[simp]
theorem coe_depthStratum_apply (hr : r ≠ 0) (Φ : M ≃ₘ^r⟮𝓡c n, 𝓡c m⟯ N) (k : ℕ)
    (x : (𝓡c n).depthStratum M k) :
    ((Φ.depthStratum hr k x : (𝓡c m).depthStratum N k) : N) = Φ x.val :=
  (rfl)

theorem coe_depthStratum_symm_apply (hr : r ≠ 0) (Φ : M ≃ₘ^r⟮𝓡c n, 𝓡c m⟯ N) (k : ℕ)
    (y : (𝓡c m).depthStratum N k) :
    (((Φ.depthStratum hr k).symm y : (𝓡c n).depthStratum M k) : M) = Φ.symm y.val :=
  (rfl)

@[simp]
theorem depthStratum_refl (hr : r ≠ 0) (k : ℕ) :
    (Diffeomorph.refl (𝓡c n) M r).depthStratum hr k =
      Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))) ((𝓡c n).depthStratum M k) r := by
  ext x
  rfl

@[simp]
theorem depthStratum_symm (hr : r ≠ 0) (Φ : M ≃ₘ^r⟮𝓡c n, 𝓡c m⟯ N) (k : ℕ) :
    (Φ.depthStratum hr k).symm = Φ.symm.depthStratum hr k := by
  ext y
  rfl

@[simp]
theorem depthStratum_trans (hr : r ≠ 0) (Φ : M ≃ₘ^r⟮𝓡c n, 𝓡c m⟯ N)
    (Ψ : N ≃ₘ^r⟮𝓡c m, 𝓡c l⟯ P) (k : ℕ) :
    (Φ.trans Ψ).depthStratum hr k = (Φ.depthStratum hr k).trans (Ψ.depthStratum hr k) := by
  ext x
  rfl

end DepthStratum

end Diffeomorph

namespace ModelWithCorners

section CoordManifold

open EuclideanSpace (finsetComplEquivProd finsetComplEquivProd_symm_mk_fst_zero)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Finite ι]

private def stratumLocalDomain (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (L : E ≃L[ℝ] (ι → ℝ)) (S : Set ι) {k : ℕ} (p : I.depthStratum M k) :
    TopologicalSpace.Opens (I.depthStratum M k) :=
  ⟨Subtype.val ⁻¹' (I.localQuadrantSource L S p.val : Set M),
    (I.localQuadrantSource L S p.val).isOpen.preimage continuous_subtypeVal⟩

private theorem mem_stratumLocalDomain (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι} {k : ℕ}
    (p : I.depthStratum M k) :
    p ∈ stratumLocalDomain I M L S p :=
  I.mem_localQuadrantSource L S p.val

private theorem mem_depthStratum_localQuadrantHomeomorph (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {k : ℕ}
    (p : I.depthStratum M k) (q : stratumLocalDomain I M L S p) :
    localQuadrantHomeomorph L hI p.val ⟨q.val.val, q.property⟩ ∈
      (𝓡c (finrank ℝ E)).depthStratum (I.localQuadrantTarget L S p.val) k := by
  rw [mem_depthStratum, ← coe_localQuadrantDiffeomorph L hI (r := 1) p.val,
    (localQuadrantDiffeomorph L hI (r := 1) p.val).depth_eq one_ne_zero, I.depth_opens]
  exact q.val.property

private theorem mem_depthStratum_localQuadrantHomeomorph_symm (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {k : ℕ}
    (p : I.depthStratum M k)
    (v : (𝓡c (finrank ℝ E)).depthStratum (I.localQuadrantTarget L S p.val) k) :
    (((localQuadrantHomeomorph L hI p.val).symm v.val).val : M) ∈ I.depthStratum M k := by
  rw [mem_depthStratum, ← I.depth_opens,
    ← coe_localQuadrantDiffeomorph_symm L hI (r := 1) p.val,
    (localQuadrantDiffeomorph L hI (r := 1) p.val).symm.depth_eq one_ne_zero]
  exact v.property

private def stratumLocalHomeomorph (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {k : ℕ}
    (p : I.depthStratum M k) :
    stratumLocalDomain I M L S p ≃ₜ
      (𝓡c (finrank ℝ E)).depthStratum (I.localQuadrantTarget L S p.val) k :=
  { toFun := fun q ↦ ⟨localQuadrantHomeomorph L hI p.val ⟨q.val.val, q.property⟩,
      mem_depthStratum_localQuadrantHomeomorph L hI p q⟩
    invFun := fun v ↦ ⟨⟨((localQuadrantHomeomorph L hI p.val).symm v.val).val,
        mem_depthStratum_localQuadrantHomeomorph_symm L hI p v⟩,
      ((localQuadrantHomeomorph L hI p.val).symm v.val).property⟩
    left_inv := fun q ↦ Subtype.ext <| Subtype.ext <|
      congrArg (Subtype.val : I.localQuadrantSource L S p.val → M)
        ((localQuadrantHomeomorph L hI p.val).symm_apply_apply ⟨q.val.val, q.property⟩)
    right_inv := fun v ↦
      Subtype.ext <| (localQuadrantHomeomorph L hI p.val).apply_symm_apply v.val
    continuous_toFun :=
      ((localQuadrantHomeomorph L hI p.val).continuous.comp
        ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _)).subtype_mk _
    continuous_invFun :=
      ((continuous_subtypeVal.comp
        ((localQuadrantHomeomorph L hI p.val).symm.continuous.comp
          continuous_subtypeVal)).subtype_mk _).subtype_mk _ }

private def coordStratumBase (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {k : ℕ}
    (p : I.depthStratum M k) :
    (𝓡c (finrank ℝ E)).depthStratum (I.localQuadrantTarget L S p.val) k :=
  stratumLocalHomeomorph L hI p ⟨p, mem_stratumLocalDomain L p⟩

private def coordStratumOpenChart (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {k : ℕ}
    (p : I.depthStratum M k) :
    OpenPartialHomeomorph (stratumLocalDomain I M L S p)
      (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) :=
  (stratumLocalHomeomorph L hI p).transOpenPartialHomeomorph
    (chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) (coordStratumBase L hI p))

private def coordStratumChart (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {k : ℕ}
    (p : I.depthStratum M k) :
    OpenPartialHomeomorph (I.depthStratum M k) (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) :=
  (coordStratumOpenChart L hI p).lift_openEmbedding
    (stratumLocalDomain I M L S p).isOpen.isOpenEmbedding_subtypeVal

private theorem mem_coordStratumChart_source (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {k : ℕ}
    (p : I.depthStratum M k) :
    p ∈ (coordStratumChart L hI p).source := by
  rw [coordStratumChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨⟨p, mem_stratumLocalDomain L p⟩, mem_chart_source _ (coordStratumBase L hI p), rfl⟩

private def coordStratumOverlapDomain (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) {k : ℕ}
    (p₁ p₂ : I.depthStratum M k) :
    TopologicalSpace.Opens
      ((𝓡c (finrank ℝ E)).depthStratum (I.localQuadrantTarget L S p₁.val) k) :=
  ⟨{v | (((localQuadrantHomeomorph L hI p₁.val).symm v.val).val : M) ∈
      I.localQuadrantSource L S p₂.val},
    (I.localQuadrantSource L S p₂.val).isOpen.preimage
      (continuous_subtypeVal.comp
        ((localQuadrantHomeomorph L hI p₁.val).symm.continuous.comp continuous_subtypeVal))⟩

private theorem contMDiff_coordStratumOverlapMap (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {r : ℕ∞ω} [IsManifold I r M]
    {k : ℕ} (p₁ p₂ : I.depthStratum M k) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r
      (fun o : coordStratumOverlapDomain L hI p₁ p₂ ↦
        stratumLocalHomeomorph L hI p₂
          ⟨((stratumLocalHomeomorph L hI p₁).symm o.val).val, o.property⟩) := by
  rw [TauCeti.contMDiff_iff_comp_subtypeVal_depthStratum]
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I r
      (fun o : coordStratumOverlapDomain L hI p₁ p₂ ↦
        (((localQuadrantHomeomorph L hI p₁.val).symm o.val.val).val : M)) := by
    simp_rw [← coe_localQuadrantDiffeomorph_symm L hI (r := r) p₁.val]
    exact contMDiff_subtypeVal.comp
      ((localQuadrantDiffeomorph L hI (r := r) p₁.val).symm.contMDiff.comp
        (TauCeti.contMDiff_subtypeVal_depthStratum.comp contMDiff_subtypeVal))
  have hlift : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I r
      (fun o : coordStratumOverlapDomain L hI p₁ p₂ ↦
        (⟨((localQuadrantHomeomorph L hI p₁.val).symm o.val.val).val,
          o.property⟩ : I.localQuadrantSource L S p₂.val)) :=
    fun o ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ univ o).1
      (hg o).contMDiffWithinAt
  convert (localQuadrantDiffeomorph L hI (r := r) p₂.val).contMDiff.comp hlift using 1
  ext o
  simp [stratumLocalHomeomorph]

private theorem contDiffOn_coordStratumChart_symm_trans (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] {r : ℕ∞ω} [IsManifold I r M]
    {k : ℕ} (p₁ p₂ : I.depthStratum M k) :
    ContDiffOn ℝ r ((coordStratumChart L hI p₁).symm ≫ₕ coordStratumChart L hI p₂)
      ((coordStratumChart L hI p₁).symm ≫ₕ coordStratumChart L hI p₂).source := by
  classical
  let d := finrank ℝ E
  let c₁ := chartAt (EuclideanSpace ℝ (Fin (d - k))) (coordStratumBase L hI p₁)
  let c₂ := chartAt (EuclideanSpace ℝ (Fin (d - k))) (coordStratumBase L hI p₂)
  let O := coordStratumOverlapDomain L hI p₁ p₂
  let ψ : O → (𝓡c d).depthStratum (I.localQuadrantTarget L S p₂.val) k := fun o ↦
    stratumLocalHomeomorph L hI p₂ ⟨((stratumLocalHomeomorph L hI p₁).symm o.val).val, o.property⟩
  have hψ := contMDiff_coordStratumOverlapMap L hI (r := r) p₁ p₂
  set S₁₂ := ((coordStratumChart L hI p₁).symm ≫ₕ coordStratumChart L hI p₂).source
  have hmemO (w : EuclideanSpace ℝ (Fin (d - k))) (hw : w ∈ S₁₂) :
      w ∈ c₁.target ∧ c₁.symm w ∈ O := by
    obtain ⟨hw₁, q', _, hq'eq⟩ := hw
    have hval : (q'.val : M) =
        (((localQuadrantHomeomorph L hI p₁.val).symm (c₁.symm w).val).val : M) :=
      congrArg (Subtype.val : I.depthStratum M k → M) hq'eq
    exact ⟨hw₁, by simpa only [O, coordStratumOverlapDomain, TopologicalSpace.Opens.mem_mk,
      mem_ofPred_eq] using hval ▸ q'.property⟩
  have hmemc₂ (w : EuclideanSpace ℝ (Fin (d - k))) (hw : w ∈ S₁₂) :
      ψ ⟨c₁.symm w, (hmemO w hw).2⟩ ∈ c₂.source := by
    rcases id hw with ⟨_, q', hq'src, hq'eq⟩
    have hq' : (⟨((stratumLocalHomeomorph L hI p₁).symm (c₁.symm w)).val, (hmemO w hw).2⟩ :
        stratumLocalDomain I M L S p₂) = q' := Subtype.ext hq'eq.symm
    simpa [ψ, hq', coordStratumOpenChart] using hq'src
  rw [← contMDiffOn_iff_contDiffOn]
  refine ContMDiffOn.congr (f := fun w ↦
      if hw : w ∈ S₁₂ then c₂ (ψ ⟨c₁.symm w, (hmemO w hw).2⟩) else 0) (fun w₀ hw₀ ↦ ?_)
      fun w hw ↦ ?_
  · let fO : EuclideanSpace ℝ (Fin (d - k)) → O := fun w ↦
      if h : c₁.symm w ∈ O then ⟨c₁.symm w, h⟩ else ⟨c₁.symm w₀, (hmemO w₀ hw₀).2⟩
    refine (ContMDiffAt.congr_of_eventuallyEq (f := fun w ↦ c₂ (ψ (fO w))) ?_ ?_).contMDiffWithinAt
    · have hc₁ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k))) r c₁.symm w₀ :=
        (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) _
          (hmemO w₀ hw₀).1).contMDiffAt (c₁.open_target.mem_nhds (hmemO w₀ hw₀).1)
      have hfO : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k))) r fO w₀ := by
        refine (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ univ w₀).1
          (hc₁.contMDiffWithinAt.congr_of_eventuallyEq ?_ (by simp [fO, (hmemO w₀ hw₀).2]))
        filter_upwards [nhdsWithin_le_nhds
          (hc₁.continuousAt.preimage_mem_nhds (O.isOpen.mem_nhds (hmemO w₀ hw₀).2))] with w _
        simp_all [fO]
      have hfO₀ : fO w₀ = ⟨c₁.symm w₀, (hmemO w₀ hw₀).2⟩ := by simp [fO, (hmemO w₀ hw₀).2]
      have hc₂ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k))) r c₂ (ψ (fO w₀)) := by
        rw [hfO₀]
        exact (contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) _
          (hmemc₂ w₀ hw₀)).contMDiffAt (c₂.open_source.mem_nhds (hmemc₂ w₀ hw₀))
      exact hc₂.comp w₀ ((hψ (fO w₀)).comp w₀ hfO)
    · filter_upwards [((coordStratumChart L hI p₁).symm ≫ₕ
          coordStratumChart L hI p₂).open_source.mem_nhds hw₀] with w hw
      have hwS : w ∈ S₁₂ := hw
      simp [fO, hwS, (hmemO w hwS).2]
  · simp only [hw, ↓reduceDIte, OpenPartialHomeomorph.coe_trans, comp_apply]
    change coordStratumChart L hI p₂
      (((stratumLocalHomeomorph L hI p₁).symm (c₁.symm w)).val) = _
    set u₂ : stratumLocalDomain I M L S p₂ :=
      ⟨((stratumLocalHomeomorph L hI p₁).symm (c₁.symm w)).val, (hmemO w hw).2⟩
    exact OpenPartialHomeomorph.lift_openEmbedding_apply (coordStratumOpenChart L hI p₂)
      (stratumLocalDomain I M L S p₂).isOpen.isOpenEmbedding_subtypeVal (x := u₂)

/-- **Charted-space structure on depth strata of coordinate-nonnegative models:** for a `C¹`
manifold `M` whose model range is cut out by nonnegative coordinates under a finite continuous
linear coordinate equivalence `L : E ≃L[ℝ] (ι → ℝ)`, `I.depthStratum M k` carries a charted-space
structure modelled on `EuclideanSpace ℝ (Fin (finrank ℝ E - k))`, obtained by pulling back the
quadrant stratum charts along `ModelWithCorners.localQuadrantHomeomorph`. -/
@[irreducible] def depthStratumChartedSpace (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) (I.depthStratum M k) :=
  { atlas := range (coordStratumChart L hI)
    chartAt := coordStratumChart L hI
    mem_chart_source := mem_coordStratumChart_source L hI
    chart_mem_atlas := mem_range_self }

variable (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
  (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M]

private theorem depthStratumChartedSpace_chartAt {k : ℕ} (p : I.depthStratum M k) :
    letI := I.depthStratumChartedSpace M L hI k
    chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) p = coordStratumChart L hI p := by
  unfold depthStratumChartedSpace
  rfl

/-- The atlas of `ModelWithCorners.depthStratumChartedSpace` is the range of its preferred
charts. -/
theorem depthStratumChartedSpace_atlas (k : ℕ) :
    letI := I.depthStratumChartedSpace M L hI k
    atlas (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) (I.depthStratum M k) =
      range fun p : I.depthStratum M k ↦
        chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) p := by
  unfold atlas chartAt depthStratumChartedSpace
  rfl

/-- **Each depth stratum of a `C¹` manifold over a coordinate-nonnegative model that is `C^r` is a
boundaryless `C^r` manifold** of dimension `finrank ℝ E - k`. -/
theorem isManifold_depthStratum {r : ℕ∞ω} [IsManifold I r M] (k : ℕ) :
    letI := I.depthStratumChartedSpace M L hI k
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r (I.depthStratum M k) := by
  let _ := I.depthStratumChartedSpace M L hI k
  refine isManifold_of_contDiffOn _ r _ ?_
  rw [depthStratumChartedSpace_atlas (M := M) L hI k]
  rintro _ _ ⟨p₁, rfl⟩ ⟨p₂, rfl⟩
  simpa [depthStratumChartedSpace_chartAt L hI] using
    contDiffOn_coordStratumChart_symm_trans L hI p₁ p₂

private theorem transHomeomorph_subRight_chart_mem_maximalAtlas {d k : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (d - k))) X] {r : ℕ∞ω}
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k))) r X] (p : X)
    (c₀ : EuclideanSpace ℝ (Fin (d - k))) :
    (chartAt (EuclideanSpace ℝ (Fin (d - k))) p).transHomeomorph (Homeomorph.subRight c₀) ∈
      IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k))) r X := by
  have hch := IsManifold.chart_mem_maximalAtlas
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d - k)))) (n := r) p
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · exact (contDiff_id.sub contDiff_const).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hch)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hch).comp
      (contDiff_id.add contDiff_const).contMDiff.contMDiffOn fun _ hu ↦ hu

/-- **The inclusion of a depth stratum of a coordinate-nonnegative model into `M` is a `C^r`
immersion.** -/
theorem isImmersion_subtypeVal_depthStratum {r : ℕ∞ω} [IsManifold I r M] (k : ℕ) :
    letI := I.depthStratumChartedSpace M L hI k
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I r
      (Subtype.val : I.depthStratum M k → M) := by
  let _ := I.depthStratumChartedSpace M L hI k
  let _ := I.isManifold_depthStratum (M := M) L hI (r := r) k
  let d := finrank ℝ E
  apply Manifold.IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin k))
  intro p
  let q₀ := coordStratumBase L hI p
  let Z : Finset (Fin d) :=
    {i | (chartAt (EuclideanQuadrant d) q₀.val q₀.val).val i = 0}
  have hZ : #Z = k := TauCeti.card_filter_chartAt_eq_of_mem_depthStratum q₀.prop
  set c := I.localQuadrantOffset L S p.val
  have hcZ : ∀ i ∈ Z, c i = 0 := fun i hi ↦
    localQuadrantOffset_eq_zero_of_apply_eq_zero L hI p.val
      (by simpa [Z, q₀, coordStratumBase, stratumLocalHomeomorph,
        TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
        OpenPartialHomeomorph.refl_apply (EuclideanQuadrant d)] using hi)
  let c₀ : EuclideanSpace ℝ (Fin (d - k)) := (finsetComplEquivProd ℝ Z hZ c).1
  have hc : (finsetComplEquivProd ℝ Z hZ).symm (c₀, 0) = I.localQuadrantOffset L S p.val :=
    finsetComplEquivProd_symm_mk_fst_zero hcZ
  let domChart :=
    (chartAt (EuclideanSpace ℝ (Fin (d - k))) p).transHomeomorph (Homeomorph.subRight c₀)
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtypeVal.continuousAt
    ((finsetComplEquivProd ℝ Z hZ).symm.trans (coordToEuclidean L).symm)
    domChart (chartAt H p.val) (mem_chart_source _ p) (mem_chart_source H p.val)
    (transHomeomorph_subRight_chart_mem_maximalAtlas p c₀)
    (IsManifold.chart_mem_maximalAtlas p.val) fun u hu ↦ ?_
  have hu' : u + c₀ ∈ (chartAt (EuclideanSpace ℝ (Fin (d - k))) q₀).target := by
    rw [OpenPartialHomeomorph.extend_target] at hu
    simpa [domChart, depthStratumChartedSpace_chartAt L hI p, coordStratumChart,
      coordStratumOpenChart, Homeomorph.subRight] using hu.1
  let s := (chartAt (EuclideanSpace ℝ (Fin (d - k))) q₀).symm (u + c₀)
  have hs_symm : (((domChart.extend 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k)))).symm u :
      I.depthStratum M k) : M) =
      (((localQuadrantHomeomorph L hI p.val).symm s.val).val : M) := by
    simp only [domChart, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      id_eq, comp_apply, OpenPartialHomeomorph.transHomeomorph_symm_apply,
      depthStratumChartedSpace_chartAt L hI p]
    rfl
  obtain ⟨hpos, hs_tgt⟩ :=
    (TauCeti.depthStratumChartedSpace_chartAt_target q₀).subset hu'
  have hs_val : s.val.val.val = (finsetComplEquivProd ℝ Z hZ).symm (u + c₀, 0) := by
    have h2 : (s.val : EuclideanQuadrant d) =
        (𝓡c d).symm ((finsetComplEquivProd ℝ Z hZ).symm (u + c₀, 0)) := by
      have hcs : chartAt (EuclideanQuadrant d) q₀.val s.val = (s.val : EuclideanQuadrant d) := by
        simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
          OpenPartialHomeomorph.refl_apply (EuclideanQuadrant d)]
      have hsymm := congrArg (chartAt (EuclideanQuadrant d) q₀.val)
        (TauCeti.depthStratumChartedSpace_chartAt_symm_apply q₀ hu')
      rw [hcs, (chartAt (EuclideanQuadrant d) q₀.val).right_inv hs_tgt] at hsymm
      exact hsymm
    rw [congrArg Subtype.val h2, ← modelWithCornersEuclideanQuadrant_apply]
    refine (𝓡c d).right_inv <| range_modelWithCornersEuclideanQuadrant d ▸ fun i ↦ ?_
    by_cases hi : i ∈ Z
    · exact (EuclideanSpace.finsetComplEquivProd_symm_mk_zero_apply_of_mem _ hi).ge
    · exact (EuclideanSpace.forall_finsetComplEquivProd_symm_mk_zero_iff (0 ≤ ·) _).2
        (fun j ↦ (hpos j).le) i hi
  have hext := (mem_chart_source_and_extChartAt_localQuadrantHomeomorph_symm L hI p.val s.val).2
  simp only [comp_apply, OpenPartialHomeomorph.extend_coe]
  rw [hs_symm, ← Function.comp_apply (f := I) (g := chartAt H p.val), ← extChartAt_coe,
    hext, hs_val, ← hc, ← map_sub]
  simp

/-- **The inclusion of a depth stratum of a coordinate-nonnegative model into `M` is a `C^r` smooth
embedding.** -/
theorem isSmoothEmbedding_subtypeVal_depthStratum {r : ℕ∞ω} [IsManifold I r M] (k : ℕ) :
    letI := I.depthStratumChartedSpace M L hI k
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I r
      (Subtype.val : I.depthStratum M k → M) :=
  letI := I.depthStratumChartedSpace M L hI k
  letI := I.isManifold_depthStratum (M := M) L hI (r := r) k
  ⟨I.isImmersion_subtypeVal_depthStratum (M := M) L hI k, IsEmbedding.subtypeVal⟩

/-- The inclusion of `I.depthStratum M k` into `M` is `C^r`. -/
theorem contMDiff_subtypeVal_depthStratum {r : ℕ∞ω} [IsManifold I r M] (k : ℕ) :
    letI := I.depthStratumChartedSpace M L hI k
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I r
      (Subtype.val : I.depthStratum M k → M) :=
  letI := I.depthStratumChartedSpace M L hI k
  letI := I.isManifold_depthStratum (M := M) L hI (r := r) k
  (I.isSmoothEmbedding_subtypeVal_depthStratum (M := M) L hI k).contMDiff

section Universal

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  {r : ℕ∞ω} [IsManifold I r M]

/-- **Universal property of a depth stratum:** a map into `I.depthStratum M k` is `C^r` within a set
at a point if and only if its composite with `Subtype.val` is `C^r` within that set. -/
theorem contMDiffWithinAt_iff_comp_subtypeVal_depthStratum
    (k : ℕ) {f : X → I.depthStratum M k} {s : Set X} {x : X} :
    letI := I.depthStratumChartedSpace M L hI k
    ContMDiffWithinAt IX 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r f s x ↔
      ContMDiffWithinAt IX I r (Subtype.val ∘ f) s x :=
  letI := I.depthStratumChartedSpace M L hI k
  letI := I.isManifold_depthStratum (M := M) L hI (r := r) k
  (I.isSmoothEmbedding_subtypeVal_depthStratum (M := M) L hI (r := r) k).contMDiffWithinAt_iff_comp

/-- Smoothness of a map into `I.depthStratum M k` can be checked after composing with
`Subtype.val`. -/
theorem contMDiff_iff_comp_subtypeVal_depthStratum (k : ℕ) {f : X → I.depthStratum M k} :
    letI := I.depthStratumChartedSpace M L hI k
    ContMDiff IX 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r f ↔
      ContMDiff IX I r (Subtype.val ∘ f) :=
  letI := I.depthStratumChartedSpace M L hI k
  letI := I.isManifold_depthStratum (M := M) L hI (r := r) k
  (I.isSmoothEmbedding_subtypeVal_depthStratum (M := M) L hI (r := r) k).contMDiff_iff_comp

end Universal

/-- **Functoriality and independence of `(L, S)`:** a `C^r` diffeomorphism `Φ : M ≃ₘ^r⟮I, I'⟯ N`
(`r ≠ 0`) between manifolds over coordinate-nonnegative models restricts to a `C^r` diffeomorphism
between their depth-`k` strata. Taking `Φ = Diffeomorph.refl I M r` shows that the smooth structure
on `I.depthStratum M k` is independent of the coordinate presentation `(L, S)`. -/
def depthStratumDiffeomorph
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {ι' : Type*} [Finite ι'] (L' : E' ≃L[ℝ] (ι' → ℝ)) {S' : Set ι'}
    (hI' : range I' = {y | ∀ i ∈ S', 0 ≤ L' y i})
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
    {r : ℕ∞ω} (hr : r ≠ 0) [IsManifold I r M] [IsManifold I' r N]
    (Φ : M ≃ₘ^r⟮I, I'⟯ N) (k : ℕ) :
    letI := I.depthStratumChartedSpace M L hI k
    letI := I'.depthStratumChartedSpace N L' hI' k
    I.depthStratum M k ≃ₘ^r⟮
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))),
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E' - k)))⟯
      I'.depthStratum N k :=
  letI := I.depthStratumChartedSpace M L hI k
  letI := I'.depthStratumChartedSpace N L' hI' k
  letI := I.isManifold_depthStratum (M := M) L hI (r := r) k
  letI := I'.isManifold_depthStratum (M := N) L' hI' (r := r) k
  { toFun := fun x ↦ ⟨Φ x.val, (Φ.depth_eq hr x.val).trans x.prop⟩
    invFun := fun y ↦ ⟨Φ.symm y.val, (Φ.symm.depth_eq hr y.val).trans y.prop⟩
    left_inv := fun x ↦ Subtype.ext (Φ.symm_apply_apply x.val)
    right_inv := fun y ↦ Subtype.ext (Φ.apply_symm_apply y.val)
    contMDiff_toFun :=
      (I'.contMDiff_iff_comp_subtypeVal_depthStratum (M := N) L' hI' k).2
        (Φ.contMDiff.comp (I.contMDiff_subtypeVal_depthStratum (M := M) L hI k))
    contMDiff_invFun :=
      (I.contMDiff_iff_comp_subtypeVal_depthStratum (M := M) L hI k).2
        (Φ.symm.contMDiff.comp (I'.contMDiff_subtypeVal_depthStratum (M := N) L' hI' k)) }

@[simp]
theorem coe_depthStratumDiffeomorph_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {ι' : Type*} [Finite ι'] (L' : E' ≃L[ℝ] (ι' → ℝ)) {S' : Set ι'}
    (hI' : range I' = {y | ∀ i ∈ S', 0 ≤ L' y i})
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
    {r : ℕ∞ω} (hr : r ≠ 0) [IsManifold I r M] [IsManifold I' r N]
    (Φ : M ≃ₘ^r⟮I, I'⟯ N) (k : ℕ) (x : I.depthStratum M k) :
    ((depthStratumDiffeomorph L hI L' hI' hr Φ k x : I'.depthStratum N k) : N) = Φ x.val :=
  (rfl)

@[simp]
theorem coe_depthStratumDiffeomorph_symm_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {ι' : Type*} [Finite ι'] (L' : E' ≃L[ℝ] (ι' → ℝ)) {S' : Set ι'}
    (hI' : range I' = {y | ∀ i ∈ S', 0 ≤ L' y i})
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
    {r : ℕ∞ω} (hr : r ≠ 0) [IsManifold I r M] [IsManifold I' r N]
    (Φ : M ≃ₘ^r⟮I, I'⟯ N) (k : ℕ) (y : I'.depthStratum N k) :
    letI := I.depthStratumChartedSpace M L hI k
    letI := I'.depthStratumChartedSpace N L' hI' k
    (((depthStratumDiffeomorph L hI L' hI' hr Φ k).symm y : I.depthStratum M k) : M) =
      Φ.symm y.val :=
  (rfl)

/-- **Comparison with the interior:** the depth-zero stratum `I.depthStratum M 0` of a
coordinate-nonnegative model is canonically `C^r`-diffeomorphic to the open interior submanifold
`⟨I.interior M, I.isOpen_interior one_ne_zero⟩`. -/
def depthStratumZeroDiffeomorphInterior {r : ℕ∞ω} [IsManifold I r M] :
    letI := I.depthStratumChartedSpace M L hI 0
    I.depthStratum M 0 ≃ₘ^r⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - 0))), I⟯
      (⟨I.interior M, I.isOpen_interior one_ne_zero⟩ : TopologicalSpace.Opens M) :=
  haveI : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  letI := I.depthStratumChartedSpace M L hI 0
  letI := I.isManifold_depthStratum (M := M) L hI (r := r) 0
  let U : TopologicalSpace.Opens M := ⟨I.interior M, I.isOpen_interior one_ne_zero⟩
  Homeomorph.diffeomorphOfImmersions
    { toFun := fun x ↦ ⟨x.val, I.depth_eq_zero_iff.1 x.prop⟩
      invFun := fun x ↦ ⟨x.val, I.depth_eq_zero_iff.2 x.prop⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_subtypeVal.subtype_mk _
      continuous_invFun := continuous_subtypeVal.subtype_mk _ }
    (I.isImmersion_subtypeVal_depthStratum (M := M) L hI 0)
    (Manifold.IsImmersion.of_opens U)
    rfl

@[simp]
theorem coe_depthStratumZeroDiffeomorphInterior_apply {r : ℕ∞ω} [IsManifold I r M]
    (x : I.depthStratum M 0) :
    ((depthStratumZeroDiffeomorphInterior L hI (r := r) x :
      (⟨I.interior M, I.isOpen_interior one_ne_zero⟩ :
        TopologicalSpace.Opens M)) : M) = x.val := by
  simp [depthStratumZeroDiffeomorphInterior]

@[simp]
theorem coe_depthStratumZeroDiffeomorphInterior_symm_apply {r : ℕ∞ω} [IsManifold I r M]
    (x : (⟨I.interior M, I.isOpen_interior one_ne_zero⟩ : TopologicalSpace.Opens M)) :
    letI := I.depthStratumChartedSpace M L hI 0
    (((depthStratumZeroDiffeomorphInterior L hI (r := r)).symm x :
      I.depthStratum M 0) : M) = x.val := by
  simp [depthStratumZeroDiffeomorphInterior]

end CoordManifold

section Comparisons

/-- **Comparison with the quadrant stratum instance:** on a `C¹` manifold `X` modelled on `𝓡c n`
that is `C^r`, the coordinate-nonnegative smooth structure on `(𝓡c n).depthStratum X k` is
canonically `C^r`-diffeomorphic via the identity to `TauCeti.depthStratumChartedSpace`. -/
def depthStratumQuadrantDiffeomorph {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanQuadrant n) X] [IsManifold (𝓡c n) 1 X] {r : ℕ∞ω}
    [IsManifold (𝓡c n) r X] (k : ℕ) :
    letI := (𝓡c n).depthStratumChartedSpace X (EuclideanSpace.equiv (Fin n) ℝ)
      (range_modelWithCornersEuclideanQuadrant_eq n) k
    @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ (EuclideanSpace ℝ (Fin n)) - k)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k)))
      ((𝓡c n).depthStratum X k) _
      ((𝓡c n).depthStratumChartedSpace X (EuclideanSpace.equiv (Fin n) ℝ)
        (range_modelWithCornersEuclideanQuadrant_eq n) k)
      ((𝓡c n).depthStratum X k) _ TauCeti.depthStratumChartedSpace r :=
  Homeomorph.diffeomorphOfImmersions
    (cM := (𝓡c n).depthStratumChartedSpace X (EuclideanSpace.equiv (Fin n) ℝ)
      (range_modelWithCornersEuclideanQuadrant_eq n) k)
    (cN := TauCeti.depthStratumChartedSpace)
    (Homeomorph.refl _)
    ((𝓡c n).isImmersion_subtypeVal_depthStratum (M := X) (EuclideanSpace.equiv (Fin n) ℝ)
      (range_modelWithCornersEuclideanQuadrant_eq n) k)
    TauCeti.isImmersion_subtypeVal_depthStratum
    rfl

/-- **Comparison with the half-space boundary:** on a `C¹` manifold `X` modelled on `𝓡∂ (n + 1)`
that is `C^r`, the depth-one stratum `(𝓡∂ (n + 1)).depthStratum X 1` equipped with
`ModelWithCorners.depthStratumChartedSpace` is canonically `C^r`-diffeomorphic to the boundary
manifold `(𝓡∂ (n + 1)).boundary X` of `TauCeti.boundaryChartedSpace`. -/
def depthStratumOneDiffeomorphBoundary {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X] [IsManifold (𝓡∂ (n + 1)) 1 X]
    {r : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) r X] :
    letI := (𝓡∂ (n + 1)).depthStratumChartedSpace X (EuclideanSpace.equiv (Fin (n + 1)) ℝ)
      (range_modelWithCornersEuclideanHalfSpace_eq (n + 1)) 1
    (𝓡∂ (n + 1)).depthStratum X 1 ≃ₘ^r⟮
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) - 1))),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      ↥((𝓡∂ (n + 1)).boundary X) :=
  let _ := (𝓡∂ (n + 1)).depthStratumChartedSpace X (EuclideanSpace.equiv (Fin (n + 1)) ℝ)
    (range_modelWithCornersEuclideanHalfSpace_eq (n + 1)) 1
  Homeomorph.diffeomorphOfImmersions
    { toFun := fun x ↦ ⟨x.val, depth_modelWithCornersEuclideanHalfSpace_eq_one_iff.1 x.prop⟩
      invFun := fun x ↦ ⟨x.val, depth_modelWithCornersEuclideanHalfSpace_eq_one_iff.2 x.prop⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_subtypeVal.subtype_mk _
      continuous_invFun := continuous_subtypeVal.subtype_mk _ }
    ((𝓡∂ (n + 1)).isImmersion_subtypeVal_depthStratum (M := X)
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ)
      (range_modelWithCornersEuclideanHalfSpace_eq (n + 1)) 1)
    (TauCeti.isImmersion_subtypeVal_boundary X)
    rfl

@[simp]
theorem coe_depthStratumOneDiffeomorphBoundary_apply {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X] [IsManifold (𝓡∂ (n + 1)) 1 X]
    {r : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) r X]
    (x : (𝓡∂ (n + 1)).depthStratum X 1) :
    ((depthStratumOneDiffeomorphBoundary (r := r) x :
      (𝓡∂ (n + 1)).boundary X) : X) = x.val := by
  simp [depthStratumOneDiffeomorphBoundary]

@[simp]
theorem coe_depthStratumOneDiffeomorphBoundary_symm_apply {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X] [IsManifold (𝓡∂ (n + 1)) 1 X]
    {r : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) r X]
    (x : (𝓡∂ (n + 1)).boundary X) :
    letI := (𝓡∂ (n + 1)).depthStratumChartedSpace X (EuclideanSpace.equiv (Fin (n + 1)) ℝ)
      (range_modelWithCornersEuclideanHalfSpace_eq (n + 1)) 1
    (((depthStratumOneDiffeomorphBoundary (n := n) (X := X) (r := r)).symm x :
      (𝓡∂ (n + 1)).depthStratum X 1) : X) = x.val := by
  simp [depthStratumOneDiffeomorphBoundary]

end Comparisons

end ModelWithCorners
