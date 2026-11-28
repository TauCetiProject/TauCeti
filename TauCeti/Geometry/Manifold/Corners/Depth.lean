/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Analysis.Calculus.TangentCone.Basic
public import TauCeti.Analysis.Calculus.TangentCone.Prod

/-!
# The depth of a point of a manifold with corners

A point of the quadrant `[0, ∞)ⁿ` lies on as many boundary faces as it has vanishing
coordinates; this number is its *depth*. On a manifold with corners the depth of a point is the
depth of its image in a chart, and the point of this file is that it does not depend on the chart.
The points of depth `0` are the interior points, and those of positive depth are the boundary
points; the points of depth at least two are the corners. For the quadrant model the depth is the
number of local boundary faces through a point, so it is the multiplicity with which a point of
the boundary is covered by the faces along which manifolds with corners are cut and glued.

The depth is defined for every real model with corners `I`, without reference to coordinates. The
*depth* `I.depthAt y` of a point `y` of the model vector space `E` is, when `E` is
finite-dimensional, the codimension of the largest linear subspace contained in the positive
tangent cone of `range I` at `y`. If `E` is infinite-dimensional then `finrank ℝ E = 0` and the
depth is identically `0`, so the results below assume finite dimensionality. For the
quadrant model `𝓡c n` it is the number of vanishing coordinates of `y`
(`ModelWithCorners.depthAt_modelWithCornersEuclideanQuadrant`), and for the half-space model
`𝓡∂ n` it is `1` on the boundary hyperplane and `0` elsewhere
(`ModelWithCorners.depthAt_modelWithCornersEuclideanHalfSpace`).

The depth `I.depth x` of a point `x` of a manifold is the depth of its image in the preferred
extended chart. On a `C¹` manifold the image in any chart of the maximal atlas has the same depth
(`ModelWithCorners.depthAt_extend_eq_depth`). The reason is that the differential of a map carries
positive tangent cones into positive tangent cones, so an injective differential cannot decrease
the dimension of the largest linear subspace in the cone
(`ModelWithCorners.finrank_sub_depthAt_le_of_hasFDerivWithinAt`). Applied to chart transitions in
both directions this gives chart independence, and applied to a map with injective differential
it shows that local diffeomorphisms and diffeomorphisms preserve the depth
(`IsLocalDiffeomorphAt.depth_eq`, `Diffeomorph.depth_eq`).

The depth is additive on products (`ModelWithCorners.depthAt_prod`, `ModelWithCorners.depth_prod`):
the range of a product model is the product of the ranges, both are convex, and the positive tangent
cone of a product of convex sets is the product of the cones (`Convex.posTangentConeAt_prod`). So a
product of manifolds with boundary has corners of depth two exactly over pairs of boundary points
(`ModelWithCorners.depth_prod_eq_two_iff`). For instance, a handle `Dᵏ × Dⁿ⁻ᵏ` has its corners
along `Sᵏ⁻¹ × Sⁿ⁻ᵏ⁻¹`, and `M × [0, 1]` along `∂M × {0, 1}`.

## Main definitions

* `ModelWithCorners.depthAt`: the depth of a point of the model vector space.
* `ModelWithCorners.depth`: the depth of a point of a manifold, read in its preferred chart.

## Main results

* `ModelWithCorners.depthAt_eq_iff`: the depth is the codimension of the largest linear subspace
  in the positive tangent cone.
* `ModelWithCorners.depthAt_eq_zero_iff`, `ModelWithCorners.depth_eq_zero_iff`: depth zero means
  interior point.
* `ModelWithCorners.image_range_prod_eq`,
  `ModelWithCorners.exists_equiv_image_range_eq_of_boundaryless`: coordinate nonnegativity regions
  are closed under products and include all finite-dimensional boundaryless models up to continuous
  linear equivalence.
* `ModelWithCorners.depthAt_eq_natCard_of_range_eq`,
  `ModelWithCorners.depthAt_le_natCard_of_range_eq`,
  `ModelWithCorners.depthAt_le_of_forall_pos`, `ModelWithCorners.depthAt_eq_iff_of_forall_pos`: for
  a model whose range is cut out by the nonnegativity of some coordinates, the depth counts the
  vanishing ones among them, is at most the cardinality of that coordinate set, and is monotone
  under preservation of positive coordinates.
* `ModelWithCorners.depthAt_transContinuousLinearEquiv`,
  `ModelWithCorners.depth_transContinuousLinearEquiv`: continuous linear changes of model
  coordinates preserve the depth.
* `ModelWithCorners.depthAt_extend_eq_depth`: the depth does not depend on the chart.
* `ModelWithCorners.isOpen_setOf_depth_le_of_range_eq`,
  `ModelWithCorners.isClosed_setOf_le_depth_of_range_eq` (and `*_of_image_range_eq`): upper
  semicontinuity of the depth on coordinate-region models.
* `ModelWithCorners.depth_modelWithCornersEuclideanQuadrant`: on a manifold modelled on the
  quadrant, the depth of a point counts the vanishing coordinates of its image in any chart.
* `ModelWithCorners.depth_eq_card_filter_chartAt`: the same count in a preferred chart, as the
  cardinality of a finset.
* `MDifferentiableAt.finrank_sub_depth_le`: a map with injective differential does not decrease
  the dimension of the largest linear subspace in the cone.
* `IsLocalDiffeomorphAt.depth_eq`, `Diffeomorph.depth_eq`: (local) diffeomorphisms preserve the
  depth.
* `ModelWithCorners.depthAt_prod`, `ModelWithCorners.depth_prod`: the depth of a point of a
  product is the sum of the depths of its coordinates.
* `ModelWithCorners.depth_modelWithCornersEuclideanHalfSpace_eq_one_iff`: on a manifold modelled on
  the half-space, the points of depth one are the boundary points.
* `ModelWithCorners.depth_prod_eq_two_iff`: in a product of two such manifolds, the points of
  depth two are the pairs of boundary points.

## Implementation notes

The comparison of charts and the passage to maps follow Mathlib's proofs that interior points do
not depend on the chart, `ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas`
and `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`, with the transport of positive
tangent cones by the differential in place of their separation argument. At a point outside
`range I` the definition gives the junk value `finrank ℝ E`.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (the depth of a point and its independence of
  the chart). [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
-/

public section

noncomputable section

open Set Filter Function Module
open scoped Manifold Topology

namespace ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners ℝ E' H')

section Model

open Classical in
/-- The **depth** of a point `y` of the model vector space of a real model with corners `I`: when
the model vector space is finite-dimensional, the codimension of the largest linear subspace
contained in the positive tangent cone of `range I` at `y` (see `ModelWithCorners.depthAt_eq_iff`).
Interior points of `range I` have depth `0`, and a point of the quadrant `[0, ∞)ⁿ` has as depth its
number of vanishing coordinates. In an infinite-dimensional model vector space `finrank ℝ E = 0`,
so the depth is identically `0`. -/
def depthAt (y : E) : ℕ :=
  finrank ℝ E - Nat.findGreatest
    (fun d ↦ ∃ V : Submodule ℝ E, (V : Set E) ⊆ posTangentConeAt (range I) y ∧ finrank ℝ V = d)
    (finrank ℝ E)

variable {I I'}

/-- The depth is at most the dimension of the model vector space. -/
theorem depthAt_le_finrank (y : E) : I.depthAt y ≤ finrank ℝ E := by
  simp only [depthAt]
  exact Nat.sub_le _ _

variable {y : E}

open Classical in
/-- At a point of `range I`, some linear subspace in the positive tangent cone has the dimension
complementary to the depth. -/
theorem exists_finrank_add_depthAt_eq (hy : y ∈ range I) :
    ∃ V : Submodule ℝ E, (V : Set E) ⊆ posTangentConeAt (range I) y ∧
      finrank ℝ V + I.depthAt y = finrank ℝ E := by
  have h0 : ∃ V : Submodule ℝ E, (V : Set E) ⊆ posTangentConeAt (range I) y ∧ finrank ℝ V = 0 :=
    ⟨⊥, by simpa using (zero_mem_tangentConeAt (subset_closure hy) :
      (0 : E) ∈ posTangentConeAt (range I) y), finrank_bot ℝ E⟩
  obtain ⟨V, hV, hVd⟩ := Nat.findGreatest_spec (P := fun d ↦ ∃ V : Submodule ℝ E,
    (V : Set E) ⊆ posTangentConeAt (range I) y ∧ finrank ℝ V = d) (Nat.zero_le (finrank ℝ E)) h0
  refine ⟨V, hV, ?_⟩
  have h' := Nat.findGreatest_le
    (P := fun d ↦ ∃ V : Submodule ℝ E, (V : Set E) ⊆ posTangentConeAt (range I) y ∧
      finrank ℝ V = d) (finrank ℝ E)
  simp only [depthAt]
  omega

variable [FiniteDimensional ℝ E]

open Classical in
/-- Every linear subspace in the positive tangent cone has dimension at most the dimension
complementary to the depth. -/
theorem finrank_add_depthAt_le (V : Submodule ℝ E)
    (hV : (V : Set E) ⊆ posTangentConeAt (range I) y) :
    finrank ℝ V + I.depthAt y ≤ finrank ℝ E := by
  have h := Nat.le_findGreatest (P := fun d ↦ ∃ V : Submodule ℝ E,
    (V : Set E) ⊆ posTangentConeAt (range I) y ∧ finrank ℝ V = d) (Submodule.finrank_le V)
    ⟨V, hV, rfl⟩
  have h' := Nat.findGreatest_le
    (P := fun d ↦ ∃ V : Submodule ℝ E, (V : Set E) ⊆ posTangentConeAt (range I) y ∧
      finrank ℝ V = d) (finrank ℝ E)
  simp only [depthAt]
  omega

/-- The depth of a point of `range I` is the codimension of the largest linear subspace contained
in the positive tangent cone of `range I` at that point. -/
theorem depthAt_eq_iff (hy : y ∈ range I) {d : ℕ} :
    I.depthAt y = d ↔
      (∃ V : Submodule ℝ E, (V : Set E) ⊆ posTangentConeAt (range I) y ∧
        finrank ℝ V + d = finrank ℝ E) ∧
      ∀ V : Submodule ℝ E, (V : Set E) ⊆ posTangentConeAt (range I) y →
        finrank ℝ V + d ≤ finrank ℝ E := by
  refine ⟨?_, fun ⟨⟨V, hV, hVd⟩, hle⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨exists_finrank_add_depthAt_eq hy, finrank_add_depthAt_le⟩
  · obtain ⟨W, hW, hWd⟩ := exists_finrank_add_depthAt_eq hy
    have h₁ := finrank_add_depthAt_le V hV
    have h₂ := hle W hW
    omega

/-- A point of `range I` has depth zero exactly when it lies in the interior of `range I`. -/
@[simp]
theorem depthAt_eq_zero_iff (hy : y ∈ range I) : I.depthAt y = 0 ↔ y ∈ interior (range I) := by
  rw [depthAt_eq_iff hy]
  refine ⟨fun ⟨⟨V, hV, hVd⟩, _⟩ ↦ ?_, fun hint ↦ ⟨⟨⊤, fun v _ ↦ ?_, by simp⟩, fun V _ ↦ by
    simpa using Submodule.finrank_le V⟩⟩
  · -- A full-dimensional subspace in the cone makes the cone everything, which a supporting
    -- functional at a point outside the interior rules out.
    have hV' : V = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hVd)
    by_contra hy'
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (I.convex_range.interior) isOpen_interior hy'
    have hmax : IsLocalMaxOn f (range I) y := by
      refine eventually_mem_nhdsWithin.mono fun z hz ↦ ?_
      have hcl : range I ⊆ closure (interior (range I)) := by
        rw [I.convex_range.closure_interior_eq_closure_of_nonempty_interior I.nonempty_interior,
          I.isClosed_range.closure_eq]
      exact closure_lt_subset_le f.continuous continuous_const
        (closure_mono (fun a ha ↦ hf a ha) (hcl hz))
    have hle (v : E) : f v ≤ 0 :=
      hmax.hasFDerivWithinAt_nonpos f.hasFDerivAt.hasFDerivWithinAt (hV (by simp [hV']))
    obtain ⟨a, ha⟩ := I.nonempty_interior
    have h₁ := hle (y - a)
    have h₂ := hf a ha
    rw [map_sub] at h₁
    linarith
  · simp [tangentConeAt_of_mem_nhds (mem_interior_iff_mem_nhds.mp hint)]

variable [FiniteDimensional ℝ E']

omit [FiniteDimensional ℝ E] in
/-- An injective linear map carrying the positive tangent cone of `range I` at `y` into that of
`range I'` at `y'` cannot decrease the dimension of the largest linear subspace in the cone. -/
theorem finrank_sub_depthAt_le_of_mapsTo (hy : y ∈ range I) {y' : E'} {D : E →ₗ[ℝ] E'}
    (hD : Injective D)
    (hmaps : MapsTo D (posTangentConeAt (range I) y) (posTangentConeAt (range I') y')) :
    finrank ℝ E - I.depthAt y ≤ finrank ℝ E' - I'.depthAt y' := by
  obtain ⟨V, hV, hVd⟩ := exists_finrank_add_depthAt_eq hy
  have hW := finrank_add_depthAt_le (I := I') (y := y') (V.map D) <| by
    rintro _ ⟨v, hv, rfl⟩
    exact hmaps (hV hv)
  rw [← (Submodule.equivMapOfInjective D hD V).finrank_eq] at hW
  have := depthAt_le_finrank (I := I) y
  omega

omit [FiniteDimensional ℝ E] in
/-- Let `φ` be differentiable within `s` at `y`, with injective differential, where `s` is a
neighbourhood of `y` within `range I` which `φ` maps into `range I'`. Then the largest linear
subspace in the positive tangent cone at `φ y` has at least the dimension of the one at `y`. -/
theorem finrank_sub_depthAt_le_of_hasFDerivWithinAt (hy : y ∈ range I) {φ : E → E'}
    {D : E →L[ℝ] E'} {s : Set E} (hs : s ∈ 𝓝[range I] y) (hφ : MapsTo φ s (range I'))
    (hφD : HasFDerivWithinAt φ D s y) (hD : Injective D) :
    finrank ℝ E - I.depthAt y ≤ finrank ℝ E' - I'.depthAt (φ y) := by
  refine finrank_sub_depthAt_le_of_mapsTo hy (D := (D : E →ₗ[ℝ] E')) hD fun v hv ↦ ?_
  have hv' : v ∈ posTangentConeAt s y := tangentConeAt_mono_nhds (nhdsWithin_le_iff.mpr hs) hv
  exact posTangentConeAt_mono (image_subset_iff.mpr hφ) (hφD.mapsTo_posTangentConeAt hv')

/-- **The depth is additive on product models**: the depth of a point of the range of `I.prod I'`
is the sum of the depths of its two coordinates. -/
@[simp]
theorem depthAt_prod (hy : y ∈ range I) {y' : E'} (hy' : y' ∈ range I') :
    (I.prod I').depthAt (y, y') = I.depthAt y + I'.depthAt y' := by
  have hcone : posTangentConeAt (range (I.prod I')) (y, y') =
      posTangentConeAt (range I) y ×ˢ posTangentConeAt (range I') y' := by
    rw [range_prod]
    exact I.convex_range.posTangentConeAt_prod I'.convex_range
  have hfin (V : Submodule ℝ E) (V' : Submodule ℝ E') :
      finrank ℝ (V.prod V') = finrank ℝ V + finrank ℝ V' := by
    rw [(Submodule.prodEquiv V V').finrank_eq, finrank_prod]
  obtain ⟨V, hV, hVd⟩ := exists_finrank_add_depthAt_eq hy
  obtain ⟨V', hV', hV'd⟩ := exists_finrank_add_depthAt_eq hy'
  rw [depthAt_eq_iff (by rw [range_prod]; exact ⟨hy, hy'⟩), finrank_prod]
  refine ⟨⟨V.prod V', ?_, by rw [hfin]; omega⟩, fun U hU ↦ ?_⟩
  · rw [Submodule.prod_coe, hcone]
    exact prod_mono hV hV'
  · -- The two projections of `U` are linear subspaces in the cones of the factors, and `U` lies
    -- in their product.
    have h₁ := finrank_add_depthAt_le (I := I) (y := y) (U.map (LinearMap.fst ℝ E E'))
      (by rintro _ ⟨u, hu, rfl⟩; exact (hcone ▸ hU hu).1)
    have h₂ := finrank_add_depthAt_le (I := I') (y := y') (U.map (LinearMap.snd ℝ E E'))
      (by rintro _ ⟨u, hu, rfl⟩; exact (hcone ▸ hU hu).2)
    have hle : U ≤ (U.map (LinearMap.fst ℝ E E')).prod (U.map (LinearMap.snd ℝ E E')) :=
      fun u hu ↦ ⟨⟨u, hu, rfl⟩, ⟨u, hu, rfl⟩⟩
    have hU' := Submodule.finrank_mono hle
    rw [hfin] at hU'
    omega

omit [FiniteDimensional ℝ E'] in
/-- A continuous linear change of model coordinates preserves the depth of points in the range
of the model. -/
@[simp]
theorem depthAt_transContinuousLinearEquiv (e : E ≃L[ℝ] E') (hy : y ∈ range I) :
    (I.transContinuousLinearEquiv e).depthAt (e y) = I.depthAt y := by
  have : FiniteDimensional ℝ E' := e.toLinearEquiv.finiteDimensional
  have h1 : finrank ℝ E - I.depthAt y ≤
      finrank ℝ E' - (I.transContinuousLinearEquiv e).depthAt (e y) :=
    finrank_sub_depthAt_le_of_hasFDerivWithinAt (I := I) (I' := I.transContinuousLinearEquiv e)
      hy self_mem_nhdsWithin
      (fun z hz ↦ by rw [I.transContinuousLinearEquiv_range]; exact mem_image_of_mem e hz)
      e.hasFDerivAt.hasFDerivWithinAt e.injective
  have hey : e y ∈ range (I.transContinuousLinearEquiv e) := by
    rw [I.transContinuousLinearEquiv_range]
    exact mem_image_of_mem e hy
  have h2 : finrank ℝ E' - (I.transContinuousLinearEquiv e).depthAt (e y) ≤
      finrank ℝ E - I.depthAt y := by
    simpa using finrank_sub_depthAt_le_of_hasFDerivWithinAt
      (I := I.transContinuousLinearEquiv e) (I' := I) hey self_mem_nhdsWithin
      (fun z hz ↦ by
        rw [I.transContinuousLinearEquiv_range] at hz
        rcases hz with ⟨w, hw, rfl⟩
        simpa using hw)
      e.symm.hasFDerivAt.hasFDerivWithinAt e.symm.injective
  have hdim : finrank ℝ E = finrank ℝ E' := e.toLinearEquiv.finrank_eq
  have h3 := depthAt_le_finrank (I := I) y
  have h4 := depthAt_le_finrank (I := I.transContinuousLinearEquiv e) (e y)
  omega

end Model

section Coordinates

variable {ι : Type*} [Fintype ι] {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}

/-- For a region `{z | ∀ i ∈ S, 0 ≤ z i}`, the coordinates which are nonnegative on the whole
region are exactly those of `S`. -/
theorem forall_mem_range_nonneg_iff (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {i : ι} :
    (∀ z ∈ range J, 0 ≤ z i) ↔ i ∈ S := by
  classical
  refine ⟨fun h ↦ ?_, fun hi z hz ↦ by rw [hJ] at hz; exact hz i hi⟩
  by_contra hiS
  -- The point with `i`-th coordinate `-1` and all others `0` lies in the region.
  set z : EuclideanSpace ℝ ι := WithLp.toLp 2 fun j ↦ if j = i then -1 else 0
  have hz : z ∈ range J := by
    rw [hJ]
    intro k hk
    have hki : k ≠ i := fun h ↦ hiS (h ▸ hk)
    simp [z, hki]
  have := h z hz
  norm_num [z] at this

/-- The quadrant is the region of `EuclideanSpace ℝ (Fin n)` cut out by the nonnegativity of
every coordinate. -/
theorem range_modelWithCornersEuclideanQuadrant_eq (n : ℕ) :
    range (𝓡c n) = {z | ∀ i ∈ (univ : Set (Fin n)), 0 ≤ z i} := by
  simp [range_modelWithCornersEuclideanQuadrant]

/-- The half-space is the region of `EuclideanSpace ℝ (Fin n)` cut out by the nonnegativity of the
coordinate `0`. -/
theorem range_modelWithCornersEuclideanHalfSpace_eq (n : ℕ) [NeZero n] :
    range (𝓡∂ n) = {z | ∀ i ∈ ({0} : Set (Fin n)), 0 ≤ z i} := by
  simp [range_modelWithCornersEuclideanHalfSpace]

/-- If two models with corners have ranges linearly equivalent to coordinate nonnegativity regions,
their product model has range linearly equivalent to the product coordinate region. -/
theorem image_range_prod_eq {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {S₁ : Set ι₁} {S₂ : Set ι₂}
    {e₁ : E ≃L[ℝ] EuclideanSpace ℝ ι₁} {e₂ : E' ≃L[ℝ] EuclideanSpace ℝ ι₂}
    (h₁ : e₁ '' range I = {z | ∀ i ∈ S₁, 0 ≤ z i})
    (h₂ : e₂ '' range I' = {z | ∀ j ∈ S₂, 0 ≤ z j}) :
    ((e₁.prodCongr e₂).trans EuclideanSpace.sumEquivProd.symm) '' range (I.prod I') =
      {z : EuclideanSpace ℝ (ι₁ ⊕ ι₂) |
        ∀ k ∈ Sum.inl '' S₁ ∪ Sum.inr '' S₂, 0 ≤ z k} := by
  ext z
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  simp only [ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
    mem_preimage, range_prod, mem_prod, mem_ofPred_eq]
  have hmem₁ : e₁.symm (EuclideanSpace.sumEquivProd z).1 ∈ range I ↔
      ∀ i ∈ S₁, 0 ≤ z (Sum.inl i) := by
    have : e₁.symm (EuclideanSpace.sumEquivProd z).1 ∈ range I ↔
        (EuclideanSpace.sumEquivProd z).1 ∈ e₁ '' range I := by
      rw [e₁.image_eq_preimage_symm, mem_preimage]
    rw [this, h₁]
    simp [EuclideanSpace.sumEquivProd]
  have hmem₂ : e₂.symm (EuclideanSpace.sumEquivProd z).2 ∈ range I' ↔
      ∀ j ∈ S₂, 0 ≤ z (Sum.inr j) := by
    have : e₂.symm (EuclideanSpace.sumEquivProd z).2 ∈ range I' ↔
        (EuclideanSpace.sumEquivProd z).2 ∈ e₂ '' range I' := by
      rw [e₂.image_eq_preimage_symm, mem_preimage]
    rw [this, h₂]
    simp [EuclideanSpace.sumEquivProd]
  rw [hmem₁, hmem₂]
  constructor
  · rintro ⟨hz₁, hz₂⟩ k (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact hz₁ i hi
    · exact hz₂ j hj
  · intro hz
    exact ⟨fun i hi ↦ hz (Sum.inl i) (Or.inl ⟨i, hi, rfl⟩),
      fun j hj ↦ hz (Sum.inr j) (Or.inr ⟨j, hj, rfl⟩)⟩

/-- Every boundaryless finite-dimensional real model with corners is linearly equivalent to a
coordinate-region model with empty constraint set. -/
theorem exists_equiv_image_range_eq_of_boundaryless [FiniteDimensional ℝ E] [I.Boundaryless] :
    ∃ e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)),
      e '' range I = {z | ∀ i ∈ (∅ : Set (Fin (finrank ℝ E))), 0 ≤ z i} := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ((Module.finBasis ℝ E).equivFun.trans
      (EuclideanSpace.equiv (Fin (finrank ℝ E)) ℝ).symm.toLinearEquiv).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  rw [I.range_eq_univ, Set.image_univ, e.surjective.range_eq]
  ext z
  simp

/-- For a model with corners whose range is cut out by the nonnegativity of the coordinates
indexed by `S`, the depth of a point of the range is the number of those coordinates that vanish
there. -/
theorem depthAt_eq_natCard_of_range_eq (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {y : EuclideanSpace ℝ ι} (hy : y ∈ range J) :
    J.depthAt y = Nat.card {i // i ∈ S ∧ y i = 0} := by
  classical
  have hy' : ∀ i ∈ S, 0 ≤ y i := by rwa [hJ] at hy
  -- `K` is the subspace of vectors vanishing on the coordinates of `S` that vanish at `y`.
  let π : EuclideanSpace ℝ ι →ₗ[ℝ] ({i // i ∈ S ∧ y i = 0} → ℝ) :=
    LinearMap.pi fun j ↦ (EuclideanSpace.proj (j : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ)
  have hπ : Surjective π := fun w ↦
    ⟨(EuclideanSpace.equiv ι ℝ).symm fun i ↦ if h : i ∈ S ∧ y i = 0 then w ⟨i, h⟩ else 0, by
      ext j; simp [π, j.property]⟩
  have hK : finrank ℝ (LinearMap.ker π) + Nat.card {i // i ∈ S ∧ y i = 0} =
      finrank ℝ (EuclideanSpace ℝ ι) := by
    rw [← LinearMap.finrank_range_add_finrank_ker π, LinearMap.range_eq_top.mpr hπ,
      finrank_top, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card, add_comm]
  -- The positive tangent cone only sees the vanishing coordinates in `S`, through Fermat's rule.
  have hcone {v : EuclideanSpace ℝ ι} (hv : v ∈ posTangentConeAt (range J) y) {i : ι} (hi : i ∈ S)
      (hyi : y i = 0) : 0 ≤ v i := by
    have hmin : IsLocalMinOn (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ) (range J) y :=
      eventually_mem_nhdsWithin.mono fun z hz ↦ by
        rw [hJ] at hz
        simpa [hyi] using hz i hi
    simpa using hmin.hasFDerivWithinAt_nonneg
      (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).hasFDerivWithinAt hv
  rw [depthAt_eq_iff hy]
  refine ⟨⟨LinearMap.ker π, fun v hv ↦ ?_, hK⟩, fun V hV ↦ ?_⟩
  · -- Moving from `y` along a vector of `K` keeps the coordinates of `S` nonnegative for a while.
    have hv' (i : ι) (h : i ∈ S ∧ y i = 0) : v i = 0 := by
      simpa [π] using congr_fun (LinearMap.mem_ker.mp hv) ⟨i, h⟩
    apply mem_posTangentConeAt_of_frequently_mem
    refine Eventually.frequently ?_
    simp only [hJ, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [Filter.eventually_all_finite (Set.toFinite S)]
    intro i hi
    by_cases hyi : y i = 0
    · exact Eventually.of_forall fun t ↦ by simp [hyi, hv' i ⟨hi, hyi⟩]
    · have hpos : 0 < y i := lt_of_le_of_ne (hy' i hi) (Ne.symm hyi)
      have hcont : Tendsto (fun t : ℝ ↦ y i + t * v i) (𝓝[>] 0) (𝓝 (y i)) := by
        have : Tendsto (fun t : ℝ ↦ y i + t * v i) (𝓝 0) (𝓝 (y i + 0 * v i)) :=
          (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      filter_upwards [hcont.eventually (lt_mem_nhds hpos)] with t ht
      simpa using ht.le
  · -- A subspace in the cone contains `-v` with `v`, so it vanishes on those coordinates.
    have hVK : V ≤ LinearMap.ker π := fun v hv ↦ by
      refine LinearMap.mem_ker.mpr (funext fun j ↦ ?_)
      have h₁ := hcone (hV hv) j.property.1 j.property.2
      have h₂ := hcone (hV (V.neg_mem hv)) j.property.1 j.property.2
      simp only [PiLp.neg_apply] at h₂
      simp [π]
      linarith
    have := Submodule.finrank_mono hVK
    omega

/-- For a model with corners whose range is cut out by the nonnegativity of the coordinates
indexed by `S`, the depth of a point of the range is at most the cardinality of `S`. -/
theorem depthAt_le_natCard_of_range_eq (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {y : EuclideanSpace ℝ ι} (hy : y ∈ range J) :
    J.depthAt y ≤ Nat.card S := by
  rw [depthAt_eq_natCard_of_range_eq hJ hy]
  exact Nat.card_le_card_of_injective (fun j : {i // i ∈ S ∧ y i = 0} ↦ (⟨j.val, j.property.1⟩ : S))
    (fun _ _ h ↦ Subtype.ext (congrArg (Subtype.val : S → ι) h))

/-- At a point `z` of `{w | ∀ i ∈ S, 0 ≤ w i}` where every coordinate of `S` positive at `y`
remains positive, the depth at `z` is at most the depth at `y`. -/
theorem depthAt_le_of_forall_pos (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {y z : EuclideanSpace ℝ ι} (hy : y ∈ range J) (hz : z ∈ range J)
    (hpos : ∀ i ∈ S, y i ≠ 0 → 0 < z i) :
    J.depthAt z ≤ J.depthAt y := by
  rw [depthAt_eq_natCard_of_range_eq hJ hy, depthAt_eq_natCard_of_range_eq hJ hz]
  refine Nat.card_le_card_of_injective
    (fun j : {i // i ∈ S ∧ z i = 0} ↦
      (⟨j.val, j.property.1, by_contra fun hy0 ↦ (hpos j.val j.property.1 hy0).ne' j.property.2⟩ :
        {i // i ∈ S ∧ y i = 0}))
    (fun _ _ h ↦ Subtype.ext (congrArg (Subtype.val : {i // i ∈ S ∧ y i = 0} → ι) h))

/-- Under the positivity condition of `depthAt_le_of_forall_pos`, equality of depths holds exactly
when every coordinate of `S` vanishing at `y` also vanishes at `z`. -/
theorem depthAt_eq_iff_of_forall_pos (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {y z : EuclideanSpace ℝ ι} (hy : y ∈ range J) (hz : z ∈ range J)
    (hpos : ∀ i ∈ S, y i ≠ 0 → 0 < z i) :
    J.depthAt z = J.depthAt y ↔ ∀ i ∈ S, y i = 0 → z i = 0 := by
  classical
  let A : Finset ι := Finset.univ.filter fun i ↦ i ∈ S ∧ z i = 0
  let B : Finset ι := Finset.univ.filter fun i ↦ i ∈ S ∧ y i = 0
  have hAB : A ⊆ B := fun i hi ↦ by
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, by_contra fun hy0 ↦ (hpos i hi.1 hy0).ne' hi.2⟩
  have hcardA : J.depthAt z = A.card := by
    rw [depthAt_eq_natCard_of_range_eq hJ hz, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardB : J.depthAt y = B.card := by
    rw [depthAt_eq_natCard_of_range_eq hJ hy, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcardA, hcardB]
  constructor
  · intro h i hiS hyi
    have hBA : A = B := Finset.eq_of_subset_of_card_le hAB h.ge
    have hiA : i ∈ A := hBA ▸ (by simp [B, hiS, hyi])
    exact (Finset.mem_filter.1 hiA).2.2
  · intro h
    refine congrArg Finset.card (Finset.Subset.antisymm hAB fun i hi ↦ ?_)
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, h i hi.1 hi.2⟩

/-- In the quadrant model `𝓡c n`, the depth of a point of the quadrant is its number of
vanishing coordinates. -/
@[simp]
theorem depthAt_modelWithCornersEuclideanQuadrant {n : ℕ} {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ range (𝓡c n)) : (𝓡c n).depthAt y = Nat.card {i // y i = 0} := by
  rw [depthAt_eq_natCard_of_range_eq (range_modelWithCornersEuclideanQuadrant_eq n) hy]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i ↦ by simp)

/-- In the half-space model `𝓡∂ n`, a point of the half-space has depth `1` on the boundary
hyperplane and depth `0` elsewhere. -/
@[simp]
theorem depthAt_modelWithCornersEuclideanHalfSpace {n : ℕ} [NeZero n]
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ range (𝓡∂ n)) :
    (𝓡∂ n).depthAt y = if y 0 = 0 then 1 else 0 := by
  rw [depthAt_eq_natCard_of_range_eq (range_modelWithCornersEuclideanHalfSpace_eq n) hy]
  split_ifs with h
  · exact Nat.card_eq_one_iff_exists.mpr ⟨⟨0, rfl, h⟩, fun j ↦ Subtype.ext j.property.1⟩
  · have : IsEmpty {i // i ∈ ({0} : Set (Fin n)) ∧ y i = 0} := ⟨fun j ↦ h
      (j.property.1 ▸ j.property.2)⟩
    exact Nat.card_of_isEmpty

end Coordinates

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The **depth** of a point `x` of a manifold with corners: the depth of its image in the
preferred extended chart. On a `C¹` manifold every chart of the maximal atlas gives the same
value (`ModelWithCorners.depthAt_extend_eq_depth`). -/
def depth (x : M) : ℕ :=
  I.depthAt (extChartAt I x x)

variable {I I'}

/-- The depth of a point is the depth of its image in the preferred extended chart. -/
theorem depth_def (x : M) : I.depth x = I.depthAt (extChartAt I x x) := (rfl)

/-- The depth of a point is at most the dimension of the model vector space. -/
theorem depth_le_finrank (x : M) : I.depth x ≤ finrank ℝ E :=
  depthAt_le_finrank _

variable [FiniteDimensional ℝ E]

/-- A point of a manifold has depth zero exactly when it is an interior point. -/
@[simp]
theorem depth_eq_zero_iff {x : M} : I.depth x = 0 ↔ I.IsInteriorPoint x := by
  rw [depth_def, depthAt_eq_zero_iff (extChartAt_target_subset_range x (mem_extChartAt_target x))]
  -- `IsInteriorPoint x` is defined as exactly this membership.
  exact Iff.rfl

/-- A point of a manifold has positive depth exactly when it is a boundary point. -/
@[simp]
theorem depth_pos_iff {x : M} : 0 < I.depth x ↔ I.IsBoundaryPoint x := by
  rw [Nat.pos_iff_ne_zero, Ne, depth_eq_zero_iff, isBoundaryPoint_iff_not_isInteriorPoint]

/-- **The depth is additive on product manifolds**: the depth of a point of `M × N` is the sum of
the depths of its two coordinates. -/
@[simp]
theorem depth_prod [FiniteDimensional ℝ E'] (x : M) (x' : N) :
    (I.prod I').depth (x, x') = I.depth x + I'.depth x' := by
  simp only [depth_def, extChartAt_prod, PartialEquiv.prod_coe]
  exact depthAt_prod (extChartAt_target_subset_range x (mem_extChartAt_target x))
    (extChartAt_target_subset_range x' (mem_extChartAt_target x'))

/-- A continuous linear change of model coordinates leaves the depth of every point of a manifold
unchanged. -/
@[simp]
theorem depth_transContinuousLinearEquiv (e : E ≃L[ℝ] E') (x : M) :
    (I.transContinuousLinearEquiv e).depth x = I.depth x := by
  simp only [depth_def, I.coe_extChartAt_transContinuousLinearEquiv, Function.comp_apply]
  exact depthAt_transContinuousLinearEquiv e
    (extChartAt_target_subset_range x (mem_extChartAt_target x))

/-- On a manifold modelled on a region `{z | ∀ i ∈ S, 0 ≤ z i}`, every point has depth at most
the cardinality of `S`. -/
theorem depth_le_natCard_of_range_eq {ι : Type*} [Fintype ι]
    {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (x : M) :
    J.depth x ≤ Nat.card S :=
  depthAt_le_natCard_of_range_eq hJ
    (extChartAt_target_subset_range x (mem_extChartAt_target x))

variable {n : WithTop ℕ∞} [IsManifold I n M]

/-- On a `C¹` manifold the depth of a point does not depend on the chart: its image in any chart
of the maximal atlas has the depth of the point. -/
theorem depthAt_extend_eq_depth (hn : n ≠ 0) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) {x : M} (hx : x ∈ e.source) :
    I.depthAt (e.extend I x) = I.depth x := by
  -- Compare the two charts through the transition maps in both directions.
  have key {e e' : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M)
      (he' : e' ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
      finrank ℝ E - I.depthAt (e.extend I x) ≤ finrank ℝ E - I.depthAt (e'.extend I x) := by
    let φ := I.extendCoordChange e e'
    have hφx : e.extend I x ∈ φ.source := by
      rw [← OpenPartialHomeomorph.extend_image_source_inter]
      exact mem_image_of_mem _ ⟨hx, hx'⟩
    have hφy : φ (e.extend I x) = e'.extend I x := by
      simp [φ, e.left_inv hx]
    rw [← hφy]
    refine finrank_sub_depthAt_le_of_hasFDerivWithinAt (by simp)
      (I.extendCoordChange_source_mem_nhdsWithin' hx hx')
      (φ.mapsTo.mono_right fun _ hz ↦ e'.extend_target_subset_range (I := I) hz.1)
      (((I.contDiffOn_extendCoordChange he he').differentiableOn hn _ hφx).hasFDerivWithinAt)
      (isInvertible_fderivWithin_extendCoordChange hn he he' hφx).injective
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := n) x
  have hxc := mem_chart_source H x
  have h₁ := key he hc hx hxc
  have h₂ := key hc he hxc hx
  have h₃ := depthAt_le_finrank (I := I) (e.extend I x)
  have h₄ := depth_le_finrank (I := I) x
  rw [depth_def, extChartAt] at h₄ ⊢
  omega

end Manifold

section Semicontinuity

section RangeEq

variable {ι : Type*} [Fintype ι] {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}
  {M : Type*} [TopologicalSpace M]

/-- Inside the source of an open partial homeomorphism `e : OpenPartialHomeomorph M H`, the subset
where every coordinate in `S` nonzero at `e.extend J x` stays strictly positive is open in `M`. -/
theorem isOpen_setOf_forall_extend_pos (J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H)
    (S : Set ι) (e : OpenPartialHomeomorph M H) (x : M) :
    IsOpen {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} := by
  have hset : {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} =
      e.source ∩ ⋂ j : {j : ι // j ∈ S ∧ e.extend J x j ≠ 0},
        (fun q ↦ e.extend J q j.val) ⁻¹' Ioi 0 := by
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_Ioi, Subtype.forall]
    exact ⟨fun ⟨hq, h⟩ ↦ ⟨hq, fun j hj ↦ h j hj.1 hj.2⟩,
      fun ⟨hq, h⟩ ↦ ⟨hq, fun j hj hx0 ↦ h j ⟨hj, hx0⟩⟩⟩
  rw [hset]
  refine isOpen_iff_mem_nhds.2 fun q ⟨hq, hpos⟩ ↦ ?_
  have hcont (j : {j : ι // j ∈ S ∧ e.extend J x j ≠ 0}) :
      ContinuousAt (fun p ↦ e.extend J p j.val) q :=
    (EuclideanSpace.proj j.val : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.continuousAt.comp
      (J.continuous.continuousAt.comp (e.continuousAt hq))
  refine Filter.inter_mem (e.open_source.mem_nhds hq) ?_
  rw [Filter.iInter_mem]
  intro j
  exact (hcont j).preimage_mem_nhds (isOpen_Ioi.mem_nhds (mem_iInter.1 hpos j))

/-- A point `x ∈ e.source` belongs to the positive slice of `e` defined at `x`. -/
theorem mem_setOf_forall_extend_pos_self (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    x ∈ {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} := by
  refine ⟨hx, fun j hj hne ↦ ?_⟩
  have hmem : e.extend J x ∈ range J := by
    rw [OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  rw [hJ] at hmem
  exact lt_of_le_of_ne (hmem j hj) hne.symm

variable [ChartedSpace H M] {n : WithTop ℕ∞}

/-- **Upper semicontinuity of depth** for coordinate-region models: on a `C^n` manifold (`n ≠ 0`)
modelled on `{z | ∀ i ∈ S, 0 ≤ z i}`, the points of depth at most `k` form an open set. -/
theorem isOpen_setOf_depth_le_of_range_eq [IsManifold J n M] (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsOpen {x : M | J.depth x ≤ k} := by
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
  let e := chartAt H x
  let U := {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j}
  refine ⟨U, ?_, isOpen_setOf_forall_extend_pos J S e x,
    mem_setOf_forall_extend_pos_self hJ (mem_chart_source H x)⟩
  intro q ⟨hq, hpos⟩
  have hxe : x ∈ e.source := mem_chart_source H x
  have he : e ∈ IsManifold.maximalAtlas J n M := IsManifold.chart_mem_maximalAtlas x
  rw [mem_ofPred_eq, ← depthAt_extend_eq_depth hn he hq]
  have hle := depthAt_le_of_forall_pos hJ
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _)
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _) hpos
  rw [depthAt_extend_eq_depth hn he hxe] at hle
  exact hle.trans hx

/-- On a `C^n` manifold (`n ≠ 0`) modelled on `{z | ∀ i ∈ S, 0 ≤ z i}`, the points of depth at
least `k` form a closed set. -/
theorem isClosed_setOf_le_depth_of_range_eq [IsManifold J n M] (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsClosed {x : M | k ≤ J.depth x} := by
  cases k with
  | zero =>
    have : {x : M | 0 ≤ J.depth x} = univ := eq_univ_of_forall fun _ ↦ Nat.zero_le _
    rw [this]
    exact isClosed_univ
  | succ m =>
    have : {x : M | m + 1 ≤ J.depth x} = {x : M | J.depth x ≤ m}ᶜ := by
      ext x
      simp
    rw [this]
    exact (isOpen_setOf_depth_le_of_range_eq hn hJ m).isClosed_compl

end RangeEq

section ImageRangeEq

variable {I} {ι : Type*} [Finite ι] {S : Set ι}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- **Upper semicontinuity of depth** for any model linearly equivalent to a coordinate region
`{z | ∀ i ∈ S, 0 ≤ z i}`. -/
theorem isOpen_setOf_depth_le_of_image_range_eq [IsManifold I n M]
    (hn : n ≠ 0) (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsOpen {x : M | I.depth x ≤ k} := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  have heq : {x : M | I.depth x ≤ k} =
      {x : M | (I.transContinuousLinearEquiv e).depth x ≤ k} := by
    ext x
    simp
  rw [heq]
  exact isOpen_setOf_depth_le_of_range_eq hn
    (by rwa [I.transContinuousLinearEquiv_range]) k

/-- For any model linearly equivalent to a coordinate region, `{x | k ≤ I.depth x}` is closed. -/
theorem isClosed_setOf_le_depth_of_image_range_eq [IsManifold I n M]
    (hn : n ≠ 0) (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsClosed {x : M | k ≤ I.depth x} := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  have heq : {x : M | k ≤ I.depth x} =
      {x : M | k ≤ (I.transContinuousLinearEquiv e).depth x} := by
    ext x
    simp
  rw [heq]
  exact isClosed_setOf_le_depth_of_range_eq hn
    (by rwa [I.transContinuousLinearEquiv_range]) k

end ImageRangeEq

end Semicontinuity

section Quadrant

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  {r : WithTop ℕ∞} [IsManifold (𝓡c n) r M]

/-- On a `C^r` manifold modelled on the quadrant `𝓡c n`, `r ≠ 0`, the depth of a point is the
number of vanishing coordinates of its image in any chart of the maximal atlas. -/
theorem depth_modelWithCornersEuclideanQuadrant (hr : r ≠ 0)
    {e : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓡c n) r M) {x : M} (hx : x ∈ e.source) :
    (𝓡c n).depth x = Nat.card {i // (e x).val i = 0} := by
  rw [← depthAt_extend_eq_depth hr he hx, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    depthAt_modelWithCornersEuclideanQuadrant (mem_range_self _),
    modelWithCornersEuclideanQuadrant_apply]

open scoped Finset in
/-- On a `C^r` manifold modelled on the quadrant `𝓡c n`, `r ≠ 0`, the depth of a point `y` of the
source of the preferred chart at `x` is the number of vanishing coordinates of its image in that
chart. -/
theorem depth_eq_card_filter_chartAt (hr : r ≠ 0) {x y : M}
    (hy : y ∈ (chartAt (EuclideanQuadrant n) x).source) :
    (𝓡c n).depth y = #{i | (chartAt (EuclideanQuadrant n) x y).val i = 0} := by
  rw [depth_modelWithCornersEuclideanQuadrant hr (IsManifold.chart_mem_maximalAtlas x) hy,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

end Quadrant

section HalfSpace

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]

/-- On a manifold modelled on the half-space `𝓡∂ n`, every point has depth at most `1`. -/
theorem depth_modelWithCornersEuclideanHalfSpace_le_one (x : M) : (𝓡∂ n).depth x ≤ 1 := by
  rw [depth_def, depthAt_modelWithCornersEuclideanHalfSpace
    (extChartAt_target_subset_range x (mem_extChartAt_target x))]
  split_ifs <;> simp

/-- On a manifold modelled on the half-space `𝓡∂ n`, the points of depth `1` are exactly the
boundary points; the others are the interior points, of depth `0`. -/
@[simp]
theorem depth_modelWithCornersEuclideanHalfSpace_eq_one_iff {x : M} :
    (𝓡∂ n).depth x = 1 ↔ (𝓡∂ n).IsBoundaryPoint x := by
  rw [← depth_pos_iff]
  have := depth_modelWithCornersEuclideanHalfSpace_le_one (n := n) x
  omega

variable {m : ℕ} [NeZero m] {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace m) N]

/-- In the product of two manifolds with boundary modelled on half-spaces, the corners, the points
of depth `2`, are exactly the pairs of boundary points. -/
theorem depth_prod_eq_two_iff {x : M} {y : N} :
    ((𝓡∂ n).prod (𝓡∂ m)).depth (x, y) = 2 ↔
      (𝓡∂ n).IsBoundaryPoint x ∧ (𝓡∂ m).IsBoundaryPoint y := by
  rw [depth_prod, ← depth_modelWithCornersEuclideanHalfSpace_eq_one_iff,
    ← depth_modelWithCornersEuclideanHalfSpace_eq_one_iff]
  have := depth_modelWithCornersEuclideanHalfSpace_le_one (n := n) x
  have := depth_modelWithCornersEuclideanHalfSpace_le_one (n := m) y
  omega

end HalfSpace

end ModelWithCorners

section Maps

open ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- If a map is differentiable at `x` with injective differential, the largest linear subspace in
the positive tangent cone at `f x` has at least the dimension of the one at `x`. In equal
dimensions, the map does not increase the depth. -/
theorem MDifferentiableAt.finrank_sub_depth_le {f : M → N} {x : M} (hf : MDifferentiableAt I I' f x)
    (hf' : Injective (mfderiv I I' f x)) :
    finrank ℝ E - I.depth x ≤ finrank ℝ E' - I'.depth (f x) := by
  rw [hf.mfderiv] at hf'
  have hφ := hf.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  have hs : (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' (f x)).source) ∈
        𝓝[range I] (extChartAt I x x) :=
    Filter.inter_mem (extChartAt_target_mem_nhdsWithin x)
      (mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds
        (hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (f x)))))
  have h := finrank_sub_depthAt_le_of_hasFDerivWithinAt (I := I) (I' := I')
    (extChartAt_target_subset_range x (mem_extChartAt_target x)) hs
    (writtenInExtChartAt_mapsTo.mono_right (extChartAt_target_subset_range _))
    (hφ.mono (inter_subset_left.trans (extChartAt_target_subset_range x))) hf'
  rwa [writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)] at h

variable [FiniteDimensional ℝ E] {n : WithTop ℕ∞}

/-- A local diffeomorphism preserves the depth. -/
theorem IsLocalDiffeomorphAt.depth_eq (hn : n ≠ 0) {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) : I'.depth (f x) = I.depth x := by
  have hg := hf.localInverse_isLocalDiffeomorphAt
  have h₁ := (hf.mdifferentiableAt hn).finrank_sub_depth_le (hf.isInvertible_mfderiv hn).injective
  have h₂ := (hg.mdifferentiableAt hn).finrank_sub_depth_le (hg.isInvertible_mfderiv hn).injective
  rw [hf.localInverse_left_inv hf.localInverse_mem_target] at h₂
  have hE : finrank ℝ E = finrank ℝ E' :=
    (hf.mfderivToContinuousLinearEquiv hn).toLinearEquiv.finrank_eq
  have h₃ := depth_le_finrank (I := I) x
  have h₄ := depth_le_finrank (I := I') (f x)
  omega

/-- A diffeomorphism preserves the depth. -/
@[simp]
theorem Diffeomorph.depth_eq (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) (x : M) :
    I'.depth (Φ x) = I.depth x :=
  (Φ.isLocalDiffeomorph x).depth_eq hn

end Maps
