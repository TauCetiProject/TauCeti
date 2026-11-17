/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyClosed
public import TauCeti.Geometry.Manifold.Corners.Depth

/-!
# Depth strata of manifolds with corners: basic and topological properties

The depth `ModelWithCorners.depth` of a point of a real manifold with corners `M` partitions `M`
into its **depth strata** `ModelWithCorners.depthStratum I M k = {x | I.depth x = k}` for
`0 ≤ k ≤ dim E`. The depth-zero stratum is the interior `I.interior M`, the higher strata stratify
the boundary, and on a manifold modelled on the Euclidean half-space `𝓡∂ n` the depth-one stratum
is the boundary `(𝓡∂ n).boundary M`.

When the model range `range I` is cut out by the nonnegativity of a set `S` of coordinates in a
linear coordinate system `L : E ≃L[ℝ] (ι → ℝ)`, i.e. `range I = {y | ∀ i ∈ S, 0 ≤ L y i}` — which
simultaneously covers boundaryless models (`S = ∅`), the half-space `𝓡∂ n` (`S = {0}`), the
quadrant `𝓡c n` (`S = univ`), and all finite products of such models — the depth of a point counts
its vanishing coordinates in `S` (`ModelWithCorners.depthAt_eq_natCard_of_range_eq_equiv`). Near a
point `p` of depth `k`, the coordinates in `S` strictly positive at `p` remain strictly positive on
an open neighbourhood of `p`, so `depth ≤ k` on that neighbourhood
(`ModelWithCorners.isOpen_setOf_depth_le`). Consequently `{x | k ≤ I.depth x}` is closed and every
depth stratum is locally closed (`ModelWithCorners.isLocallyClosed_depthStratum`).

For the smooth manifold structure on depth strata, see
`TauCeti.Geometry.Manifold.Corners.Strata.Manifold`.

## Main definitions

* `ModelWithCorners.depthStratum I M k`: the set `{x : M | I.depth x = k}` of points of depth `k`.
* `TauCeti.prodCoordEquiv`: product of two linear coordinate equivalences into a disjoint-sum
  coordinate space.

## Main results

* `ModelWithCorners.depthStratum_zero`, `ModelWithCorners.iUnion_depthStratum`,
  `ModelWithCorners.pairwise_disjoint_depthStratum`, `ModelWithCorners.depthStratum_prod`: basic
  partition and product formulas for depth strata.
* `Diffeomorph.image_depthStratum`: diffeomorphisms preserve depth strata.
* `ModelWithCorners.depthAt_eq_natCard_of_range_eq_equiv`: depth as the count of vanishing
  nonnegative coordinates in any linear coordinate system `L : E ≃L[ℝ] (ι → ℝ)`.
* `ModelWithCorners.range_prod_eq_of_range_eq_equiv`,
  `ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq_equiv`,
  `ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq_equiv`,
  `ModelWithCorners.range_eq_equiv_of_boundaryless`: linear coordinate descriptions for standard
  models and their products.
* `ModelWithCorners.isOpen_setOf_depth_le`, `ModelWithCorners.isClosed_setOf_le_depth`,
  `ModelWithCorners.isLocallyClosed_depthStratum`: upper semicontinuity of depth and local
  closedness of depth strata.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (depth strata of manifolds with corners).
  [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
-/

public section

noncomputable section

open Set Filter Function Module Topology
open scoped Manifold ContDiff

/-! ### Product coordinate equivalences -/

namespace TauCeti

/-- The product of two continuous linear coordinate equivalences `L₁ : E₁ ≃L[𝕜] (ι₁ → 𝕜)` and
`L₂ : E₂ ≃L[𝕜] (ι₂ → 𝕜)` into the disjoint-sum coordinate space `ι₁ ⊕ ι₂ → 𝕜`. -/
def prodCoordEquiv {𝕜 E₁ E₂ ι₁ ι₂ : Type*}
    [Semiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
    [AddCommMonoid E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
    (L₁ : E₁ ≃L[𝕜] (ι₁ → 𝕜)) (L₂ : E₂ ≃L[𝕜] (ι₂ → 𝕜)) :
    (E₁ × E₂) ≃L[𝕜] (ι₁ ⊕ ι₂ → 𝕜) :=
  (L₁.prodCongr L₂).trans
    { toLinearEquiv := (LinearEquiv.sumArrowLequivProdArrow ι₁ ι₂ 𝕜 𝕜).symm
      continuous_toFun := Homeomorph.sumArrowHomeomorphProdArrow.continuous_invFun
      continuous_invFun := Homeomorph.sumArrowHomeomorphProdArrow.continuous_toFun }

@[simp]
theorem prodCoordEquiv_apply_inl {𝕜 E₁ E₂ ι₁ ι₂ : Type*}
    [Semiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
    [AddCommMonoid E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
    (L₁ : E₁ ≃L[𝕜] (ι₁ → 𝕜)) (L₂ : E₂ ≃L[𝕜] (ι₂ → 𝕜)) (p : E₁ × E₂) (i : ι₁) :
    prodCoordEquiv L₁ L₂ p (Sum.inl i) = L₁ p.1 i :=
  (rfl)

@[simp]
theorem prodCoordEquiv_apply_inr {𝕜 E₁ E₂ ι₁ ι₂ : Type*}
    [Semiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
    [AddCommMonoid E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
    (L₁ : E₁ ≃L[𝕜] (ι₁ → 𝕜)) (L₂ : E₂ ≃L[𝕜] (ι₂ → 𝕜)) (p : E₁ × E₂) (j : ι₂) :
    prodCoordEquiv L₁ L₂ p (Sum.inr j) = L₂ p.2 j :=
  (rfl)

end TauCeti

/-! ### Basic properties of depth strata -/

namespace ModelWithCorners

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The **depth-`k` stratum** of a charted space `M` modelled on `I`: the set of points of `M`
whose depth equals `k`. -/
def depthStratum (k : ℕ) : Set M :=
  {x : M | I.depth x = k}

variable {I M}

@[simp]
theorem mem_depthStratum {k : ℕ} {x : M} : x ∈ I.depthStratum M k ↔ I.depth x = k :=
  Iff.rfl

/-- Distinct depth strata are disjoint. -/
theorem pairwise_disjoint_depthStratum : Pairwise (Disjoint on I.depthStratum M) := by
  intro k₁ k₂ hne
  refine disjoint_left.2 fun x hx₁ hx₂ ↦ hne ?_
  rw [mem_depthStratum] at hx₁ hx₂
  exact hx₁.symm.trans hx₂

/-- Every stratum of depth strictly exceeding the ambient model dimension is empty. -/
theorem depthStratum_eq_empty_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    I.depthStratum M k = ∅ :=
  eq_empty_iff_forall_notMem.2 fun x hx ↦ (I.depth_le_finrank x).not_gt (hx ▸ hk)

/-- The depth strata for `k ≤ finrank ℝ E` cover the manifold. -/
theorem iUnion_depthStratum : (⋃ k ≤ finrank ℝ E, I.depthStratum M k) = univ := by
  ext x
  simp only [mem_iUnion, mem_depthStratum, mem_univ, iff_true]
  exact ⟨I.depth x, I.depth_le_finrank x, rfl⟩

/-- All depth strata cover the manifold. -/
theorem iUnion_depthStratum_eq_univ : (⋃ k : ℕ, I.depthStratum M k) = univ := by
  ext x
  simp only [mem_iUnion, mem_depthStratum, mem_univ, iff_true]
  exact ⟨I.depth x, rfl⟩

/-- The depth-zero stratum is the interior of the manifold. -/
@[simp]
theorem depthStratum_zero [FiniteDimensional ℝ E] : I.depthStratum M 0 = I.interior M := by
  ext x
  exact I.depth_eq_zero_iff

/-- On a boundaryless manifold, every stratum of positive depth is empty. -/
theorem depthStratum_eq_empty_of_boundaryless [FiniteDimensional ℝ E] [BoundarylessManifold I M]
    {k : ℕ} (hk : k ≠ 0) : I.depthStratum M k = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ hk ?_
  rw [mem_depthStratum] at hx
  exact hx.symm.trans (I.depth_eq_zero_iff.2 BoundarylessManifold.isInteriorPoint)

/-- Depth strata of a product manifold are unions of products of complementary depth strata. -/
theorem depthStratum_prod [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] (k : ℕ) :
    (I.prod I').depthStratum (M × N) k =
      ⋃ i ≤ k, I.depthStratum M i ×ˢ I'.depthStratum N (k - i) := by
  ext ⟨x, y⟩
  simp only [mem_depthStratum, depth_prod, mem_iUnion, mem_prod]
  constructor
  · intro h
    exact ⟨I.depth x, by omega, rfl, by omega⟩
  · rintro ⟨i, hi, rfl, h⟩
    omega

/-- On a manifold modelled on the half-space `𝓡∂ n`, the depth-one stratum is the boundary. -/
@[simp]
theorem depthStratum_modelWithCornersEuclideanHalfSpace_one {n : ℕ} [NeZero n]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace n) X] :
    (𝓡∂ n).depthStratum X 1 = (𝓡∂ n).boundary X := by
  ext x
  exact depth_modelWithCornersEuclideanHalfSpace_eq_one_iff

/-- On a manifold modelled on the half-space `𝓡∂ n`, every stratum of depth at least two is
empty. -/
theorem depthStratum_modelWithCornersEuclideanHalfSpace_eq_empty {n : ℕ} [NeZero n]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace n) X]
    {k : ℕ} (hk : 1 < k) : (𝓡∂ n).depthStratum X k = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  have := depth_modelWithCornersEuclideanHalfSpace_le_one (n := n) x
  rw [mem_depthStratum] at hx
  omega

/-- A diffeomorphism of class `C^m` (`m ≠ 0`) carries each depth stratum onto the corresponding
depth stratum. -/
theorem _root_.Diffeomorph.image_depthStratum [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m : WithTop ℕ∞} (hm : m ≠ 0) (Φ : M ≃ₘ^m⟮I, I'⟯ N) (k : ℕ) :
    Φ '' I.depthStratum M k = I'.depthStratum N k := by
  ext y
  simp only [mem_image, mem_depthStratum]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [Φ.depth_eq hm]
  · intro hy
    refine ⟨Φ.symm y, ?_, Φ.apply_symm_apply y⟩
    rw [← Φ.depth_eq hm, Φ.apply_symm_apply]
    exact hy

end Basic

/-! ### Linear coordinate descriptions of model ranges -/

section CoordModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- Pushing a real model with corners forward along a continuous linear equivalence of the model
vector space produces a model with corners with range `e '' range I`. -/
private def mapLinearEquiv {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (I : ModelWithCorners ℝ E H) (e : E ≃L[ℝ] E') : ModelWithCorners ℝ E' H where
  toFun := e ∘ I
  invFun := I.symm ∘ e.symm
  source := univ
  target := e '' range I
  map_source' x _ := ⟨I x, mem_range_self x, rfl⟩
  map_target' _ _ := mem_univ _
  left_inv' x _ := by simp
  right_inv' _ hy := by
    rcases hy with ⟨_, ⟨x, rfl⟩, rfl⟩
    simp
  source_eq := rfl
  convex_range' := by
    simp only [instIsRCLikeNormedField, ↓reduceDIte, range_comp]
    exact (I.convex_range.linear_image e.toLinearMap).convex_isRCLikeNormedField
  nonempty_interior' := by
    have hr : range (e ∘ I) = e.toHomeomorph '' range I := range_comp e I
    obtain ⟨y, hy⟩ := I.nonempty_interior
    refine ⟨e y, ?_⟩
    rw [hr, ← e.toHomeomorph.image_interior]
    exact mem_image_of_mem e.toHomeomorph hy
  continuous_toFun := e.continuous.comp I.continuous
  continuous_invFun := I.continuous_symm.comp e.symm.continuous

variable {I : ModelWithCorners ℝ E H}

/-- A continuous linear equivalence carrying `range I` onto `range I'` preserves `depthAt`. -/
theorem depthAt_eq_of_image_range [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    (e : E ≃L[ℝ] E') (he : e '' range I = range I') {y : E} (hy : y ∈ range I) :
    I.depthAt y = I'.depthAt (e y) := by
  have hmaps₁ : MapsTo e (range I) (range I') := fun z hz ↦ he ▸ mem_image_of_mem e hz
  have hmaps₂ : MapsTo e.symm (range I') (range I) := fun w hw ↦ by
    rw [← he] at hw
    rcases hw with ⟨z, hz, rfl⟩
    simpa using hz
  have h₁ := finrank_sub_depthAt_le_of_hasFDerivWithinAt (I := I) (I' := I') hy
    self_mem_nhdsWithin hmaps₁ e.hasFDerivAt.hasFDerivWithinAt e.injective
  have h₂ := finrank_sub_depthAt_le_of_hasFDerivWithinAt (I := I') (I' := I) (hmaps₁ hy)
    self_mem_nhdsWithin hmaps₂ e.symm.hasFDerivAt.hasFDerivWithinAt e.symm.injective
  rw [e.symm_apply_apply] at h₂
  have hdim : finrank ℝ E = finrank ℝ E' := e.toLinearEquiv.finrank_eq
  have hle₁ := I.depthAt_le_finrank y
  have hle₂ := I'.depthAt_le_finrank (e y)
  omega

/-- For a model with corners whose range is cut out by the nonnegativity of the coordinates in `S`
under a linear coordinate equivalence `L : E ≃L[ℝ] (ι → ℝ)`, the depth of a point of `range I` is
the number of coordinates in `S` that vanish there. -/
theorem depthAt_eq_natCard_of_range_eq_equiv {ι : Type*} [Finite ι]
    (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι} (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {y : E} (hy : y ∈ range I) :
    I.depthAt y = Nat.card {i // i ∈ S ∧ L y i = 0} := by
  cases nonempty_fintype ι
  have : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    L.trans (EuclideanSpace.equiv ι ℝ).toContinuousLinearEquiv.symm
  let J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H := mapLinearEquiv I e
  have hJrange : range J = e '' range I := range_comp e I
  have hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i} := by
    rw [hJrange, hI]
    ext z
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩ i hi
      simpa [e] using hw i hi
    · intro hz
      refine ⟨e.symm z, fun i hi ↦ ?_, e.apply_symm_apply z⟩
      simpa [e] using hz i hi
  rw [depthAt_eq_of_image_range e hJrange.symm hy,
    depthAt_eq_natCard_of_range_eq hJ (hJrange ▸ mem_image_of_mem e hy)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_)
  simp [e]

/-- The product of two models whose ranges are cut out by nonnegative coordinates has range cut out
by the corresponding nonnegative coordinates under `TauCeti.prodCoordEquiv`. -/
theorem range_prod_eq_of_range_eq_equiv {E₁ E₂ H₁ H₂ ι₁ ι₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {L₁ : E₁ ≃L[ℝ] (ι₁ → ℝ)} {L₂ : E₂ ≃L[ℝ] (ι₂ → ℝ)} {S₁ : Set ι₁} {S₂ : Set ι₂}
    (hI₁ : range I₁ = {y | ∀ i ∈ S₁, 0 ≤ L₁ y i})
    (hI₂ : range I₂ = {y | ∀ j ∈ S₂, 0 ≤ L₂ y j}) :
    range (I₁.prod I₂) =
      {p | ∀ k ∈ Sum.inl '' S₁ ∪ Sum.inr '' S₂, 0 ≤ TauCeti.prodCoordEquiv L₁ L₂ p k} := by
  rw [range_prod, hI₁, hI₂]
  ext ⟨y₁, y₂⟩
  simp only [mem_prod, mem_ofPred_eq, mem_union, mem_image]
  constructor
  · rintro ⟨h₁, h₂⟩ k (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · simpa using h₁ i hi
    · simpa using h₂ j hj
  · intro h
    refine ⟨fun i hi ↦ ?_, fun j hj ↦ ?_⟩
    · simpa using h (Sum.inl i) (Or.inl ⟨i, hi, rfl⟩)
    · simpa using h (Sum.inr j) (Or.inr ⟨j, hj, rfl⟩)

/-- A model on `EuclideanSpace ℝ ι` whose range is cut out by nonnegative coordinates is described
by `(EuclideanSpace.equiv ι ℝ).toContinuousLinearEquiv`. -/
theorem range_eq_equiv_of_euclideanSpace {ι : Type*} [Fintype ι]
    {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) :
    range J = {z | ∀ i ∈ S, 0 ≤ (EuclideanSpace.equiv ι ℝ).toContinuousLinearEquiv z i} :=
  hJ

/-- The half-space model `𝓡∂ n` is cut out by the nonnegativity of coordinate `0`. -/
theorem range_modelWithCornersEuclideanHalfSpace_eq_equiv (n : ℕ) [NeZero n] :
    range (𝓡∂ n) =
      {z | ∀ i ∈ ({0} : Set (Fin n)),
        0 ≤ (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearEquiv z i} :=
  range_modelWithCornersEuclideanHalfSpace_eq n

/-- The quadrant model `𝓡c n` is cut out by the nonnegativity of every coordinate. -/
theorem range_modelWithCornersEuclideanQuadrant_eq_equiv (n : ℕ) :
    range (𝓡c n) =
      {z | ∀ i ∈ (univ : Set (Fin n)),
        0 ≤ (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearEquiv z i} :=
  range_modelWithCornersEuclideanQuadrant_eq n

/-- A boundaryless finite-dimensional model has range cut out by the empty set of coordinate
inequalities. -/
theorem range_eq_equiv_of_boundaryless [FiniteDimensional ℝ E] [I.Boundaryless] :
    range I = {y | ∀ i ∈ (∅ : Set (Fin (finrank ℝ E))), 0 ≤ (finBasis ℝ E).equivFunL y i} := by
  simp [I.range_eq_univ]

/-! ### Semicontinuity of depth and local closedness of depth strata -/

/-- **Upper semicontinuity of depth:** on a `C¹` manifold whose model range is cut out by
nonnegative coordinates in a linear coordinate system, `{x | I.depth x ≤ k}` is open for every
`k`. -/
theorem isOpen_setOf_depth_le {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ) :
    IsOpen {x : M | I.depth x ≤ k} := by
  let _ := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  classical
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  let e := chartAt H p
  let P : Finset ι := Finset.univ.filter fun i ↦ i ∈ S ∧ 0 < L (e.extend I p) i
  refine ⟨{q ∈ e.source | ∀ i ∈ P, 0 < L (e.extend I q) i}, ?_, ?_,
    ⟨mem_chart_source H p, fun _ hi ↦ (Finset.mem_filter.1 hi).2.2⟩⟩
  · rintro q ⟨hq, hpos⟩
    let hsub : {i // i ∈ S ∧ L (e.extend I q) i = 0} →
        {i // i ∈ S ∧ L (e.extend I p) i = 0} := fun ⟨i, hiS, hqi⟩ ↦ ⟨i, hiS, by
      by_contra hne
      have hmem : e.extend I p ∈ range I := by
        rw [e.extend_coe]
        exact mem_range_self _
      have hlt : 0 < L (e.extend I p) i := lt_of_le_of_ne ((hI ▸ hmem) i hiS) (Ne.symm hne)
      exact (hpos i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hiS, hlt⟩)).ne' hqi⟩
    have hinj : Injective hsub := fun ⟨_, _⟩ ⟨_, _⟩ h ↦ Subtype.ext (Subtype.mk.inj h)
    have hle : I.depth q ≤ I.depth p := by
      rw [← depthAt_extend_eq_depth one_ne_zero (IsManifold.chart_mem_maximalAtlas p) hq,
        ← depthAt_extend_eq_depth one_ne_zero (IsManifold.chart_mem_maximalAtlas p)
          (mem_chart_source H p),
        depthAt_eq_natCard_of_range_eq_equiv L hI (by rw [e.extend_coe]; exact mem_range_self _),
        depthAt_eq_natCard_of_range_eq_equiv L hI (by rw [e.extend_coe]; exact mem_range_self _)]
      exact Nat.card_le_card_of_injective hsub hinj
    exact hle.trans hp
  · have hopen : IsOpen {y : E | ∀ i ∈ P, 0 < L y i} := by
      convert isOpen_biInter_finset (s := P) fun i _ ↦
        isOpen_lt (continuous_const : Continuous fun _ : E ↦ (0 : ℝ))
          ((continuous_apply i).comp L.continuous) using 1
      ext y
      simp
    simpa only [OpenPartialHomeomorph.extend_source, inter_def, mem_preimage,
      mem_ofPred_eq] using (e.continuousOn_extend (I := I)).isOpen_inter_preimage
        (e.isOpen_extend_source (I := I)) hopen

/-- On a `C¹` manifold whose model range is cut out by nonnegative coordinates in a linear
coordinate system, `{x | k ≤ I.depth x}` is closed for every `k`. -/
theorem isClosed_setOf_le_depth {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ) :
    IsClosed {x : M | k ≤ I.depth x} := by
  cases k with
  | zero => simp
  | succ k =>
    have heq : {x : M | k + 1 ≤ I.depth x} = {x : M | I.depth x ≤ k}ᶜ := by
      ext x
      simp only [mem_ofPred_eq, mem_compl_iff, not_le]
      omega
    rw [heq]
    exact (isOpen_setOf_depth_le L hI k).isClosed_compl

/-- Every depth stratum of a `C¹` manifold whose model range is cut out by nonnegative coordinates
is locally closed. -/
theorem isLocallyClosed_depthStratum {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ) :
    IsLocallyClosed (I.depthStratum M k) := by
  have heq : I.depthStratum M k = {x : M | I.depth x ≤ k} ∩ {x : M | k ≤ I.depth x} := by
    ext x
    simp only [mem_depthStratum, mem_inter_iff, mem_ofPred_eq]
    omega
  rw [heq]
  exact (isOpen_setOf_depth_le L hI k).isLocallyClosed.inter
    (isClosed_setOf_le_depth L hI k).isLocallyClosed

end CoordModel

end ModelWithCorners
