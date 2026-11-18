/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Boundary.SmoothMap
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# The tangent space of the boundary

For a manifold `M` modelled on Mathlib's Euclidean half-space `𝓡∂ (n + 1)`, the boundary `∂M`
carries the boundaryless manifold structure `TauCeti.boundaryChartedSpace`, and its inclusion
`ι : ∂M → M` is a smooth embedding. This file defines the tangent space of the boundary at
`q ∈ ∂M` as the subspace `T_q ∂M := range dι_q` of `T_q M` and relates it to the outward vectors of
`TauCeti.IsOutwardPointing`. It is the space on which the induced metric, the second fundamental
form and the convexity conditions of the boundary live.

The normal coordinate of a half-space chart `e` is `x ↦ (e x) 0`, which is nonnegative and vanishes
exactly on `∂M`. At a boundary point it attains its minimum, so by Fermat's theorem on the model
half-space its differential is nonnegative on the inward half-space of the preferred chart. Together
with the invertibility of the differentials of charts, this shows that the differentials of the
normal coordinates of any two charts of the maximal atlas are positive multiples of each other.
Hence `T_q ∂M` is the kernel of any of them, and each tangent vector at `q` is exactly one of
outward, tangent to the boundary, or inward, independently of the chart.

## Main definitions

* `TauCeti.boundaryTangentSpace q`: the tangent space of the boundary at `q`, as a subspace of the
  tangent space of `M`.

## Main results

* `TauCeti.finrank_boundaryTangentSpace`: `T_q ∂M` is a hyperplane, of dimension `n`.
* `TauCeti.exists_pos_mvfderiv_normal_eq_smul`: the differentials of the normal coordinates of two
  charts of the maximal atlas at a boundary point are positive multiples of each other.
* `TauCeti.isOutwardPointing_iff_mvfderiv_neg`, `TauCeti.boundaryTangentSpace_eq_ker_mvfderiv`:
  outward vectors and boundary tangent vectors, read in any chart of the maximal atlas.
* `TauCeti.isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg` and
  `TauCeti.mem_boundaryTangentSpace_iff_not_isOutwardPointing`: the trichotomy outward, tangent,
  inward.
* `TauCeti.frontier_setOf_isOutwardPointing`, `TauCeti.frontier_setOf_isOutwardPointing_neg`: the
  outward and the inward vectors are open half-spaces whose common frontier is `T_q ∂M`.
* `TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici`,
  `TauCeti.curveVelocity_mem_boundaryTangentSpace`: a curve starting at a boundary point leaves it
  in an inward or tangent direction, and a curve through a boundary point is tangent to the
  boundary there.
* `Diffeomorph.map_boundaryTangentSpace`: diffeomorphisms carry `T_q ∂M` onto `T_{Φ q} ∂M'`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 5
  (tangent spaces of the boundary, inward- and outward-pointing vectors).
* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Section 3.1 (inward, outward and tangent vectors
  at the boundary).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The tangent space `T_q ∂M` of the boundary at `q`, as a subspace of `T_q M`: the range of the
differential at `q` of the inclusion `∂M → M`, for the boundary manifold structure
`TauCeti.boundaryChartedSpace`. -/
def boundaryTangentSpace (q : (𝓡∂ (n + 1)).boundary M) :
    Submodule ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) :=
  LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q).toLinearMap

/-- A vector is tangent to the boundary when it is the differential of the inclusion applied to a
tangent vector of the boundary manifold. -/
theorem mem_boundaryTangentSpace_iff {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    v ∈ boundaryTangentSpace q ↔ ∃ u, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u = v :=
  LinearMap.mem_range

/-- The differential of the boundary inclusion takes values in the boundary tangent space. -/
@[simp]
theorem mfderiv_subtypeVal_mem_boundaryTangentSpace (q : (𝓡∂ (n + 1)).boundary M)
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u ∈ boundaryTangentSpace q :=
  LinearMap.mem_range_self _ u

/-- The differential of the boundary inclusion is injective. -/
theorem injective_mfderiv_subtypeVal_boundary (q : (𝓡∂ (n + 1)).boundary M) :
    Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q) := by
  rw [mfderiv_subtypeVal_boundary]
  exact euclideanHalfSpaceBoundaryParam_injective n

/-- The tangent space of the boundary is a hyperplane: it has dimension `n` in the
`(n + 1)`-dimensional tangent space `T_q M`. -/
@[simp]
theorem finrank_boundaryTangentSpace (q : (𝓡∂ (n + 1)).boundary M) :
    Module.finrank ℝ (boundaryTangentSpace q) = n := by
  rw [boundaryTangentSpace, LinearMap.finrank_range_of_inj
    (injective_mfderiv_subtypeVal_boundary q)]
  exact finrank_euclideanSpace_fin

section Naturality

variable {k : WithTop ℕ∞} {M' : Type*} [TopologicalSpace M']
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M'] [IsManifold (𝓡∂ (n + 1)) k M]
  [IsManifold (𝓡∂ (n + 1)) k M']

/-- A diffeomorphism of manifolds with boundary maps the boundary into the boundary
(`Diffeomorph.preimage_boundary`), and its differential carries the tangent space of the boundary
at `q` onto the tangent space of the boundary at the image of `q`. -/
theorem _root_.Diffeomorph.map_boundaryTangentSpace
    (Φ : M ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M') (hk : k ≠ 0) (q : (𝓡∂ (n + 1)).boundary M) :
    (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap =
      boundaryTangentSpace
        (⟨Φ q, (Φ.preimage_boundary hk).ge q.2⟩ : (𝓡∂ (n + 1)).boundary M') := by
  -- The restriction of `Φ` to the boundaries, a smooth map between the boundary manifolds.
  let Φb : (𝓡∂ (n + 1)).boundary M → (𝓡∂ (n + 1)).boundary M' :=
    fun p ↦ ⟨Φ p, (Φ.preimage_boundary hk).ge p.2⟩
  have hι := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M).contMDiff
  have hι' := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M').contMDiff
  have hΦb : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k Φb :=
    contMDiff_iff_comp_subtypeVal_boundary.mpr (Φ.contMDiff.comp hι)
  have hchain : (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q) =
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M' → M') (Φb q)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Φb q) := by
    rw [← mfderiv_comp q ((Φ.mdifferentiable hk).mdifferentiableAt)
      ((hι.mdifferentiable hk).mdifferentiableAt),
      ← mfderiv_comp q ((hι'.mdifferentiable hk).mdifferentiableAt)
        ((hΦb.mdifferentiable hk).mdifferentiableAt)]
    -- `Φ ∘ ι` and `ι' ∘ Φb` are the same function, `Φb` being `Φ` with the boundary membership.
    rfl
  have hle : (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap ≤
      boundaryTangentSpace (Φb q) := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Φb q u,
      (congrArg (fun L ↦ L u) hchain).symm⟩
  -- Both sides have dimension `n`, the differential of `Φ` being a linear equivalence.
  have hmap := LinearEquiv.finrank_map_eq
    (Φ.mfderivToContinuousLinearEquiv hk (q : M)).toLinearEquiv (boundaryTangentSpace q)
  have hcoe : ((Φ.mfderivToContinuousLinearEquiv hk (q : M)).toLinearEquiv :
      TangentSpace (𝓡∂ (n + 1)) (q : M) →ₗ[ℝ] TangentSpace (𝓡∂ (n + 1)) (Φ q)) =
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap := by
    rw [← Φ.mfderivToContinuousLinearEquiv_coe hk]
    -- Both sides are the same linear map, reached through two chains of forgetful coercions.
    rfl
  rw [hcoe] at hmap
  exact Submodule.eq_of_le_of_finrank_eq hle ((hmap.trans (finrank_boundaryTangentSpace q)).trans
    (finrank_boundaryTangentSpace (Φb q)).symm)

end Naturality

/-- A vector and its negative are never both outward. -/
theorem IsOutwardPointing.not_isOutwardPointing_neg {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) : ¬ IsOutwardPointing x (-v) := by
  intro hnv
  exact (hv.add hnv).ne_zero (add_neg_cancel v)

/-- The outward vectors at a point form an open subset of the tangent space. -/
theorem isOpen_setOf_isOutwardPointing (x : M) :
    IsOpen {v : TangentSpace (𝓡∂ (n + 1)) x | IsOutwardPointing x v} := by
  by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
  · simp only [isOutwardPointing_iff, hx, true_and]
    exact isOpen_lt (((EuclideanSpace.proj (0 : Fin (n + 1))).continuous.comp
      (NormedSpace.fromTangentSpace (extChartAt (𝓡∂ (n + 1)) x x)).continuous).comp
        (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          (extChartAt (𝓡∂ (n + 1)) x) x).continuous) continuous_const
  · simp only [isOutwardPointing_iff, hx, false_and, ofPred_false, isOpen_empty]

/-- The inward vectors at a point, those whose negative is outward, form an open subset of the
tangent space. -/
theorem isOpen_setOf_isOutwardPointing_neg (x : M) :
    IsOpen {v : TangentSpace (𝓡∂ (n + 1)) x | IsOutwardPointing x (-v)} :=
  (isOpen_setOf_isOutwardPointing x).preimage continuous_neg

omit [ChartedSpace (EuclideanHalfSpace (n + 1)) M] in
/-- The normal coordinate of a chart is the zeroth coordinate of the extended chart. -/
private theorem normal_eq_proj_comp_extend
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) :
    (fun y ↦ (e y).1 0) = EuclideanSpace.proj (0 : Fin (n + 1)) ∘ e.extend (𝓡∂ (n + 1)) := by
  ext y
  simp

/-- The preferred chart at a boundary point has vanishing normal coordinate there. -/
private theorem normal_chartAt_self {q : M} (hq : q ∈ (𝓡∂ (n + 1)).boundary M) :
    (chartAt (EuclideanHalfSpace (n + 1)) q q).1 0 = 0 :=
  (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff (mem_chart_source _ q)).mp hq

/-- The normal coordinate of the preferred chart at a boundary point attains its minimum there. -/
private theorem normal_chartAt_self_le {q : M} (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (y : M) :
    (chartAt (EuclideanHalfSpace (n + 1)) q q).1 0 ≤
      (chartAt (EuclideanHalfSpace (n + 1)) q y).1 0 :=
  (normal_chartAt_self hq).trans_le (chartAt (EuclideanHalfSpace (n + 1)) q y).2

/-- The normal coordinate of a chart of the maximal atlas is differentiable on its source. -/
private theorem mdifferentiableAt_normal
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M} (hqe : q ∈ e.source) :
    MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) (fun y ↦ (e y).1 0) q := by
  rw [normal_eq_proj_comp_extend]
  exact (EuclideanSpace.proj (0 : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).mdifferentiableAt.comp q
      (e.mdifferentiableAt_extend he hqe)

variable [IsManifold (𝓡∂ (n + 1)) 1 M]

/-- In the preferred chart, the differential of the normal coordinate reads off the zeroth
coordinate of a tangent vector. -/
private theorem mvfderiv_chartAt_normal_apply (x : M) (v : TangentSpace (𝓡∂ (n + 1)) x) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).1 0) x v =
      tangentSpaceCastModel (𝓡∂ (n + 1)) x v 0 := by
  have hext := (TauCeti.hasMFDerivAt_extChartAt_self (I := 𝓡∂ (n + 1)) x).mdifferentiableAt
  have hfun : (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).1 0) =
      EuclideanSpace.proj (0 : Fin (n + 1)) ∘ extChartAt (𝓡∂ (n + 1)) x := by
    ext y
    simp
  rw [hfun, (EuclideanSpace.proj (0 : Fin (n + 1))).mvfderiv_comp_apply
    (I := 𝓡∂ (n + 1)) hext, mvfderiv_apply_eq_mfderiv_apply, mfderiv_extChartAt_self]
  -- Both sides evaluate `v` in slot `0`; the tangent-space wrappers around the model space
  -- block the rewriting lemmas for the identity map and for `proj 0`.
  rfl
/-- In the preferred chart at a boundary point, the boundary tangent space is the kernel of the
differential of the normal coordinate. -/
private theorem mem_boundaryTangentSpace_iff_chartAt (q : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    v ∈ boundaryTangentSpace q ↔
      mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).1 0)
        (q : M) v = 0 := by
  rw [mvfderiv_chartAt_normal_apply, mem_boundaryTangentSpace_iff, mfderiv_subtypeVal_boundary]
  exact (Set.ext_iff.mp (range_euclideanHalfSpaceBoundaryParam n) v).trans
    mem_euclideanHalfSpaceBoundary

/-- The differential of the normal coordinate of the preferred chart takes the value `1` on the
first standard basis vector. -/
private theorem mvfderiv_chartAt_normal_single (x : M) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).1 0) x
      ((tangentSpaceCastModel (𝓡∂ (n + 1)) x).symm (EuclideanSpace.single 0 1)) = 1 := by
  rw [mvfderiv_chartAt_normal_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

/-- Fermat's theorem at a boundary point: the normal coordinate of any chart of the maximal atlas
is nonnegative and vanishes at a boundary point, so its differential is nonnegative on the vectors
that are inward or tangent in the preferred chart. -/
private theorem mvfderiv_normal_nonneg {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hqe : q ∈ e.source)
    (v : TangentSpace (𝓡∂ (n + 1)) q)
    (hv : 0 ≤ mvfderiv (𝓡∂ (n + 1))
      (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) q y).1 0) q v) :
    0 ≤ mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).1 0) q v := by
  let I := 𝓡∂ (n + 1)
  let y := extChartAt I q q
  let f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun z ↦ (e ((extChartAt I q).symm z)).1 0
  -- The manifold derivative of the normal coordinate is the derivative within the model
  -- half-space of its coordinate expression `f` in the preferred chart.
  have hf := (mdifferentiableAt_normal he hqe).hasMFDerivAt.2
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp] at hf
  have hy0 : y 0 = 0 := by simpa [y, I] using normal_chartAt_self hq
  have hmin : IsLocalMinOn f (range I) y := by
    refine Filter.Eventually.of_forall fun z ↦ ?_
    have hf0 : f y = 0 := by
      simp only [f, y, (extChartAt I q).left_inv (mem_extChartAt_source q)]
      exact (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hqe).mp hq
    rw [hf0]
    exact (e ((extChartAt I q).symm z)).2
  have hcone : tangentSpaceCastModel I q v ∈ posTangentConeAt (range I) y := by
    apply mem_posTangentConeAt_of_segment_subset
    apply I.convex_range.segment_subset (mem_range_self (chartAt _ q q))
    rw [range_modelWithCornersEuclideanHalfSpace]
    rw [mvfderiv_chartAt_normal_apply] at hv
    simp only [mem_ofPred_eq, PiLp.add_apply, hy0, zero_add]
    exact hv
  have h := hmin.hasFDerivWithinAt_nonneg hf hcone
  simpa [I, mvfderiv, NormedSpace.fromTangentSpace] using h

/-- The differential of the normal coordinate of a chart of the maximal atlas is a positive
multiple of that of the preferred chart. -/
private theorem exists_pos_mvfderiv_normal_eq_smul_chartAt
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hqe : q ∈ e.source) :
    ∃ a : ℝ, 0 < a ∧ mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).1 0) q =
      a • mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) q y).1 0) q := by
  let I := 𝓡∂ (n + 1)
  set ℓ := mvfderiv I (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) q y).1 0) q
  set ℓe := mvfderiv I (fun y ↦ (e y).1 0) q
  set w : TangentSpace I q := (tangentSpaceCastModel I q).symm (EuclideanSpace.single 0 1)
  have hw : ℓ w = 1 := mvfderiv_chartAt_normal_single q
  have hfactor (u : TangentSpace I q) : ℓe u = ℓe w * ℓ u :=
    Module.Dual.apply_eq_mul_apply_of_nonneg (ℓ : TangentSpace I q →ₗ[ℝ] ℝ)
      (ℓe : TangentSpace I q →ₗ[ℝ] ℝ) hw (mvfderiv_normal_nonneg he hq hqe) u
  -- The differential of the normal coordinate of `e` is nonzero, since `e` has invertible
  -- differential and the zeroth coordinate projection is surjective.
  have hne : ℓe ≠ 0 := by
    obtain ⟨u, hu⟩ := (isInvertible_mfderiv_extend he hqe).surjective
      (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))
    intro h0
    have h := (EuclideanSpace.proj (0 : Fin (n + 1))).mvfderiv_comp_apply (I := I)
      (e.mdifferentiableAt_extend he hqe) u
    rw [← normal_eq_proj_comp_extend, mvfderiv_apply_eq_mfderiv_apply (f := e.extend I), hu] at h
    have h1 : ℓe u = 1 := by simpa [ℓe] using h
    simp [h0] at h1
  refine ⟨ℓe w, lt_of_le_of_ne (mvfderiv_normal_nonneg he hq hqe w (by rw [hw]; exact zero_le_one))
    fun h0 ↦ hne ?_, ?_⟩
  · ext u
    rw [hfactor u, ← h0, zero_mul, zero_apply]
  · ext u
    rw [hfactor u, smul_apply, smul_eq_mul]

/-- At a boundary point, the differentials of the normal coordinates of two charts of the maximal
atlas are positive multiples of each other. -/
theorem exists_pos_mvfderiv_normal_eq_smul
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M)
    (he' : e' ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hqe : q ∈ e.source) (hqe' : q ∈ e'.source) :
    ∃ a : ℝ, 0 < a ∧ mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).1 0) q =
      a • mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e' y).1 0) q := by
  obtain ⟨a, ha, h⟩ := exists_pos_mvfderiv_normal_eq_smul_chartAt he hq hqe
  obtain ⟨a', ha', h'⟩ := exists_pos_mvfderiv_normal_eq_smul_chartAt he' hq hqe'
  refine ⟨a / a', div_pos ha ha', ?_⟩
  rw [h, h', smul_smul, div_mul_cancel₀ a ha'.ne']

/-- A tangent vector at a boundary point is outward exactly when the differential of the normal
coordinate of any chart of the maximal atlas is negative on it. -/
theorem isOutwardPointing_iff_mvfderiv_neg
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hqe : q ∈ e.source)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔ mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).1 0) q v < 0 := by
  obtain ⟨a, ha, h⟩ := exists_pos_mvfderiv_normal_eq_smul_chartAt he hq hqe
  rw [h, smul_apply, smul_neg_iff_of_pos_left ha,
    mvfderiv_chartAt_normal_apply, isOutwardPointing_iff, and_iff_right hq,
    mfderiv_extChartAt_self]
  -- Both sides evaluate `v` in slot `0`, read through the identification of the tangent space
  -- with the model space.
  rfl

/-- The tangent space of the boundary is the kernel of the differential of the normal coordinate
of any chart of the maximal atlas. -/
theorem boundaryTangentSpace_eq_ker_mvfderiv
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) (q : (𝓡∂ (n + 1)).boundary M)
    (hqe : (q : M) ∈ e.source) :
    boundaryTangentSpace q =
      LinearMap.ker (mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).1 0) (q : M)).toLinearMap := by
  obtain ⟨a, ha, h⟩ := exists_pos_mvfderiv_normal_eq_smul_chartAt he q.2 hqe
  ext v
  rw [mem_boundaryTangentSpace_iff_chartAt, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, h,
    smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right ha.ne']

/-- In the preferred chart, outward vectors are those on which the differential of the normal
coordinate is negative. -/
private theorem isOutwardPointing_iff_chartAt {q : M} (hq : q ∈ (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔
      mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) q y).1 0) q v < 0 :=
  isOutwardPointing_iff_mvfderiv_neg (IsManifold.chart_mem_maximalAtlas q) hq
    (mem_chart_source _ q) v

/-! ### Inward, tangent and outward vectors -/

/-- An outward vector is not tangent to the boundary. -/
theorem IsOutwardPointing.notMem_boundaryTangentSpace {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} (hv : IsOutwardPointing (q : M) v) :
    v ∉ boundaryTangentSpace q := by
  rw [mem_boundaryTangentSpace_iff_chartAt]
  exact ((isOutwardPointing_iff_chartAt q.2 v).mp hv).ne

/-- At a boundary point every tangent vector is outward, tangent to the boundary, or inward
(its negative is outward). By `IsOutwardPointing.not_isOutwardPointing_neg` and
`IsOutwardPointing.notMem_boundaryTangentSpace`, exactly one of the three holds. -/
theorem isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg
    (q : (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    IsOutwardPointing (q : M) v ∨ v ∈ boundaryTangentSpace q ∨ IsOutwardPointing (q : M) (-v) := by
  rw [isOutwardPointing_iff_chartAt q.2, isOutwardPointing_iff_chartAt q.2, map_neg,
    neg_lt_zero, mem_boundaryTangentSpace_iff_chartAt]
  exact lt_trichotomy _ _

/-- A tangent vector at a boundary point is tangent to the boundary exactly when neither it nor
its negative is outward. -/
theorem mem_boundaryTangentSpace_iff_not_isOutwardPointing (q : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    v ∈ boundaryTangentSpace q ↔
      ¬ IsOutwardPointing (q : M) v ∧ ¬ IsOutwardPointing (q : M) (-v) := by
  refine ⟨fun hv ↦ ⟨fun h ↦ h.notMem_boundaryTangentSpace hv,
    fun h ↦ h.notMem_boundaryTangentSpace ((boundaryTangentSpace q).neg_mem hv)⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  exact ((isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg q v).resolve_left
    h₁).resolve_right h₂

/-- The outward vectors at a boundary point form an open half-space whose frontier is the tangent
space of the boundary. -/
theorem frontier_setOf_isOutwardPointing (q : (𝓡∂ (n + 1)).boundary M) :
    frontier {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) v} =
      boundaryTangentSpace q := by
  set ℓ := mvfderiv (𝓡∂ (n + 1))
    (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).1 0) (q : M)
  have hsurj : Function.Surjective ℓ := fun r ↦
    ⟨r • (tangentSpaceCastModel (𝓡∂ (n + 1)) (q : M)).symm (EuclideanSpace.single 0 1), by
      rw [map_smul, mvfderiv_chartAt_normal_single, smul_eq_mul, mul_one]⟩
  have hopen : IsOpenMap ℓ :=
    LinearMap.isOpenMap_of_finiteDimensional (ℓ : TangentSpace (𝓡∂ (n + 1)) (q : M) →ₗ[ℝ] ℝ)
      hsurj
  have hset : {v | IsOutwardPointing (q : M) v} = ℓ ⁻¹' Iio 0 := by
    ext v
    exact isOutwardPointing_iff_chartAt q.2 v
  ext v
  rw [hset, ← hopen.preimage_frontier_eq_frontier_preimage ℓ.continuous, frontier_Iio,
    SetLike.mem_coe, mem_boundaryTangentSpace_iff_chartAt, mem_preimage, mem_singleton_iff]

/-- The inward vectors at a boundary point, those whose negative is outward, form an open
half-space whose frontier is the tangent space of the boundary. -/
theorem frontier_setOf_isOutwardPointing_neg (q : (𝓡∂ (n + 1)).boundary M) :
    frontier {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) (-v)} =
      boundaryTangentSpace q := by
  have h := (Homeomorph.neg (TangentSpace (𝓡∂ (n + 1)) (q : M))).preimage_frontier
    {v | IsOutwardPointing (q : M) v}
  rw [frontier_setOf_isOutwardPointing] at h
  have hset : {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) (-v)} =
      Homeomorph.neg (TangentSpace (𝓡∂ (n + 1)) (q : M)) ⁻¹'
        {v | IsOutwardPointing (q : M) v} := by
    ext v
    simp
  rw [hset, ← h]
  ext v
  simp only [Homeomorph.coe_neg, mem_preimage, SetLike.mem_coe, neg_mem_iff]

/-! ### Velocities of curves at the boundary -/

/-- A curve starting at a boundary point and running for nonnegative parameters leaves it in an
inward or tangent direction: its one-sided velocity is not outward. -/
theorem not_isOutwardPointing_curveVelocityWithin_Ici (c : ℝ → M) (t : ℝ) :
    ¬ IsOutwardPointing (c t) (Manifold.curveVelocityWithin (𝓡∂ (n + 1)) c (Ici t) t) := by
  intro hout
  have hq := hout.mem_boundary
  have hc : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ (n + 1)) c (Ici t) t := by
    by_contra hc
    rw [Manifold.curveVelocityWithin_apply,
      mfderivWithin_zero_of_not_mdifferentiableWithinAt hc] at hout
    exact hout.ne_zero rfl
  have hderiv := Manifold.hasDerivWithinAt_comp_curve (mdifferentiableAt_normal
    (IsManifold.chart_mem_maximalAtlas (c t)) (mem_chart_source _ (c t)))
    (Manifold.hasMFDerivWithinAt_curveVelocityWithin hc)
  have hmin : IsLocalMinOn ((fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) (c t) y).1 0) ∘ c)
      (Ici t) t :=
    Filter.Eventually.of_forall fun s ↦ normal_chartAt_self_le hq (c s)
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici t) t :=
    mem_posTangentConeAt_of_segment_subset (by
      rw [segment_eq_Icc (by linarith)]
      exact Icc_subset_Ici_self)
  have h := hmin.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  exact h.not_gt ((isOutwardPointing_iff_chartAt hq _).mp hout)

/-- The velocity of a curve through a boundary point is tangent to the boundary. -/
theorem curveVelocity_mem_boundaryTangentSpace (c : ℝ → M) {t : ℝ}
    (hq : c t ∈ (𝓡∂ (n + 1)).boundary M) :
    Manifold.curveVelocity (𝓡∂ (n + 1)) c t ∈ boundaryTangentSpace ⟨c t, hq⟩ := by
  by_cases hc : MDifferentiableAt 𝓘(ℝ) (𝓡∂ (n + 1)) c t
  · have hderiv := Manifold.hasDerivAt_comp_curve (mdifferentiableAt_normal
      (IsManifold.chart_mem_maximalAtlas (c t)) (mem_chart_source _ (c t)))
      (Manifold.hasMFDerivAt_curveVelocity hc)
    have hmin : IsLocalMin ((fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) (c t) y).1 0) ∘ c)
        t :=
      Filter.Eventually.of_forall fun s ↦ normal_chartAt_self_le hq (c s)
    rw [mem_boundaryTangentSpace_iff_chartAt]
    exact hmin.hasDerivAt_eq_zero hderiv
  · rw [Manifold.curveVelocity_apply, mfderiv_zero_of_not_mdifferentiableAt hc]
    exact (boundaryTangentSpace _).zero_mem

end TauCeti
