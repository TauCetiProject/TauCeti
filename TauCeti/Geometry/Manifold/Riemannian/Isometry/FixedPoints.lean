/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential

import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# Common fixed points of Riemannian isometries

Let `Φ i`, for `i` in an arbitrary index type, be smooth Riemannian isometries of a Riemannian
manifold `M`, and let `M^Φ = ⋂ i, fixedPoints (Φ i)` be their common fixed set. For a group `K`
acting on `M` by isometries, take `Φ k` to be the action of `k`; no topology or Lie group structure
on the index type is needed, and neither completeness of the metric nor compactness of `M` is
assumed.

At a common fixed point `p`, the tangent vectors fixed by all the differentials `dΦ_i` at `p` form
the **fixed tangent subspace** `TauCeti.RiemannianIsometry.fixedTangentSubspace Φ p`. For a group
acting by isometries this is the subspace of invariants of the isotropy representation on `T_p M`
(`TauCeti.RiemannianIsometry.fixedTangentSubspace_stabilizer_eq_invariants`). Assume now that `M`
is smooth, finite-dimensional, boundaryless and Hausdorff, with a smooth metric. This file proves
that `M^Φ` is closed and totally geodesic, that on a normal ball at each of its points `p` it is the
image under `exp_p` of the intersection of the ball with the fixed tangent subspace, and that the
fixed points at which the fixed tangent subspace has a given dimension form an embedded
submanifold. Different parts of `M^Φ` may have different dimensions.

The proof uses the exponential map. An isometry intertwines exponential maps, so
`Φ_i ∘ exp_p = exp_p ∘ dΦ_i` at a fixed point `p`
(`TauCeti.RiemannianIsometry.riemannianExp_mfderiv`), and its differential preserves every tangent
ball around the origin. So on a normal ball, where
`exp_p` is injective, `exp_p v` is fixed by `Φ_i` exactly when `v` is fixed by `dΦ_i`
(`TauCeti.RiemannianIsometry.riemannianExp_mem_iInter_fixedPoints_iff`). In normal coordinates,
the Riemannian logarithm `log_p`, the fixed set near `p` is therefore exactly the fixed tangent
subspace (`TauCeti.RiemannianIsometry.mem_iInter_fixedPoints_iff_riemannianLog_mem`): normal
coordinates are slice charts for `M^Φ`. No transversality argument is needed.

The fixed tangent subspace has the same dimension at nearby fixed points. Differentiating
`Φ_i ∘ exp_p = exp_p ∘ dΦ_i` at a fixed vector `v` of a normal domain
(`TauCeti.RiemannianIsometry.mfderiv_apply_mfderiv_riemannianExp`) shows that the differential
of `exp_p` at `v` conjugates the differentials of the `Φ_i` at `p` to those at `exp_p v`, so it
carries the fixed tangent subspace at `p` onto the one at `exp_p v`
(`TauCeti.RiemannianIsometry.coe_fixedTangentSubspace_riemannianExp`). Hence, for each dimension,
the fixed points whose fixed tangent subspace has that dimension form a smooth manifold whose
inclusion into `M` is a smooth embedding, and the differential of the inclusion carries its tangent
space onto the fixed tangent subspace
(`TauCeti.RiemannianIsometry.exists_isManifold_iInter_fixedPoints_finrank`).

Finally, the common fixed set is totally geodesic: the maximal geodesic through a fixed point with
a fixed initial velocity stays in `M^Φ` throughout its maximal interval
(`TauCeti.RiemannianIsometry.maximalGeodesic_mem_iInter_fixedPoints`), because each `Φ_i` carries
it to the maximal geodesic with the same initial data.

## Main definitions

* `TauCeti.RiemannianIsometry.fixedTangentSubspace Φ p`: at a common fixed point `p`, the tangent
  vectors at `p` fixed by the differentials of all the `Φ i` at `p`.

## Main results

* `TauCeti.RiemannianIsometry.fixedTangentSubspace_stabilizer_eq_invariants`: for a group action,
  the fixed tangent subspace of the stabilizer is the space of invariants of the isotropy
  representation.
* `TauCeti.RiemannianIsometry.fixedTangentSubspace_eq_invariants`: at a point fixed by the whole
  group, the fixed tangent subspace is the space of invariants of the isotropy representation.
* `TauCeti.RiemannianIsometry.isClosed_iInter_fixedPoints`: the common fixed set is closed.
* `TauCeti.RiemannianIsometry.maximalGeodesic_mem_iInter_fixedPoints`: it is totally geodesic.
* `TauCeti.RiemannianIsometry.riemannianExp_mem_iInter_fixedPoints_iff`: on a normal ball at a
  fixed point, the exponential map identifies the fixed tangent subspace with the fixed set.
* `TauCeti.RiemannianIsometry.mem_iInter_fixedPoints_iff_riemannianLog_mem`: normal coordinates
  at a fixed point flatten the fixed set onto the fixed tangent subspace.
* `TauCeti.RiemannianIsometry.coe_fixedTangentSubspace_riemannianExp`,
  `TauCeti.RiemannianIsometry.finrank_fixedTangentSubspace_riemannianExp`: the differential of
  the exponential map carries the fixed tangent subspace at `p` onto those at nearby fixed points.
* `TauCeti.RiemannianIsometry.exists_isManifold_iInter_fixedPoints_finrank`: the fixed points
  with fixed tangent subspace of a given dimension form an embedded submanifold, whose tangent
  space at each point is the fixed tangent subspace there.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed sets of compact group actions through an invariant
  metric and the exponential map).
* S. Kobayashi, *Fixed points of isometries*, Nagoya Mathematical Journal 13 (1958), 63–68.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Chapter 5
  (naturality of the exponential map) and Chapter 6 (normal neighbourhoods).
-/

public section

open Bundle Function Manifold Module Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} (Φ : ι → RiemannianIsometry I I M M)

/-! ### The fixed tangent subspace -/

/-- The **fixed tangent subspace** of a family of Riemannian isometries at `p`: the vectors `v` of
`T_p M` with `dΦ_i v = v` for every `i`. When `p` is a common fixed point, so that each `dΦ_i` at
`p` is an endomorphism of `T_p M`, these are the tangent vectors fixed by all the differentials.
Otherwise the comparison of `dΦ_i v ∈ T_(Φ_i p) M` with `v ∈ T_p M` is made in the common model
space, and the subspace has no intrinsic meaning. -/
def fixedTangentSubspace (p : M) : Submodule ℝ (TangentSpace I p) where
  carrier := {v | ∀ i, mfderiv I I (Φ i) p v = v}
  -- The differential takes values in `T_(Φ_i p) M`; both tangent spaces are the model space, so
  -- the last step is a definitional equality of the two vector space structures.
  add_mem' hv hw i := by rw [map_add, hv i, hw i]; rfl
  zero_mem' _ := map_zero _
  smul_mem' c _ hv i := by rw [map_smul, hv i]; rfl

variable {Φ} in
@[simp]
theorem mem_fixedTangentSubspace {p : M} {v : TangentSpace I p} :
    v ∈ fixedTangentSubspace Φ p ↔ ∀ i, mfderiv I I (Φ i) p v = v :=
  Iff.rfl

@[simp]
theorem coe_fixedTangentSubspace (p : M) :
    (fixedTangentSubspace Φ p : Set (TangentSpace I p)) = {v | ∀ i, mfderiv I I (Φ i) p v = v} :=
  Set.ext fun _ ↦ mem_fixedTangentSubspace

/-- For a group acting by Riemannian isometries, the fixed tangent subspace at `p` of the
stabilizer of `p` is the space of invariants of its tangent representation on `T_p M`. -/
theorem fixedTangentSubspace_stabilizer_eq_invariants {G : Type*} [Group G] [MulAction G M]
    (Ψ : G → RiemannianIsometry I I M M) (hΨ : ∀ g y, Ψ g y = g • y) (p : M)
    (hd : ∀ g ∈ MulAction.stabilizer G p, MDifferentiableAt I I (fun y : M ↦ g • y) p) :
    fixedTangentSubspace (fun g : MulAction.stabilizer G p ↦ Ψ g) p =
      (tangentRepresentation hd).toRepresentation.invariants := by
  ext v
  simp only [mem_fixedTangentSubspace, Representation.mem_invariants,
    ContRepresentation.toRepresentation_apply, tangentRepresentation_apply]
  -- The isometry indexed by `g` is the action of `g`.
  exact forall_congr' fun g ↦ by rw [funext (hΨ g)]; exact Iff.rfl

/-- For a group acting by Riemannian isometries with a common fixed point `p`, the fixed tangent
subspace at `p` is the space of invariants of the tangent representation on `T_p M`. -/
theorem fixedTangentSubspace_eq_invariants {G : Type*} [Group G] [MulAction G M]
    (Ψ : G → RiemannianIsometry I I M M) (hΨ : ∀ g y, Ψ g y = g • y) {p : M}
    (hp : p ∈ MulAction.fixedPoints G M)
    (hd : ∀ g ∈ MulAction.stabilizer G p, MDifferentiableAt I I (fun y : M ↦ g • y) p) :
    fixedTangentSubspace Ψ p = (tangentRepresentation hd).toRepresentation.invariants := by
  rw [← fixedTangentSubspace_stabilizer_eq_invariants Ψ hΨ p hd]
  ext v
  simp only [mem_fixedTangentSubspace, Subtype.forall]
  exact ⟨fun h g _ ↦ h g, fun h g ↦ h g (MulAction.mem_stabilizer_iff.2 (hp g))⟩

/-- The common fixed set of a family of isometries of a Hausdorff manifold is closed. -/
theorem isClosed_iInter_fixedPoints [T2Space M] : IsClosed (⋂ i, fixedPoints (Φ i)) :=
  isClosed_iInter fun i ↦ isClosed_fixedPoints (Φ i).mdifferentiable.continuous

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M]

/-! ### The fixed set is totally geodesic -/

variable {Φ}

/-- **The common fixed set is totally geodesic.** The maximal geodesic through a common fixed
point `p` whose initial velocity lies in the fixed tangent subspace consists of common fixed points
on its maximal interval. Off that interval it takes the junk value `p`, which is also fixed. -/
theorem maximalGeodesic_mem_iInter_fixedPoints {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {v : TangentSpace I p} (hv : v ∈ fixedTangentSubspace Φ p) (t : ℝ) :
    maximalGeodesic I M p v t ∈ ⋂ i, fixedPoints (Φ i) := by
  simp only [mem_iInter, mem_fixedPoints] at hp ⊢
  intro i
  have h := (Φ i).maximalGeodesic_mfderiv p v t
  rw [hv i, hp i] at h
  exact h.symm

/-- The exponential map at a common fixed point sends the fixed tangent subspace into the common
fixed set. Off the natural domain of `exp_p` it takes the junk value `p`, which is also fixed. -/
theorem riemannianExp_mem_iInter_fixedPoints {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {v : TangentSpace I p} (hv : v ∈ fixedTangentSubspace Φ p) :
    riemannianExp I M p v ∈ ⋂ i, fixedPoints (Φ i) := by
  rw [riemannianExp_def]
  exact maximalGeodesic_mem_iInter_fixedPoints hp hv 1

/-! ### Normal coordinates are slice charts -/

/-- At a fixed point `p` of a Riemannian isometry `Ψ`, the differential of `Ψ` intertwines the
exponential map with itself: `Ψ (exp_p v) = exp_p (dΨ_p v)`. Off the natural domain of `exp_p`
both sides take the junk value `p`. -/
theorem apply_riemannianExp_of_isFixedPt (Ψ : RiemannianIsometry I I M M) {p : M}
    (hp : IsFixedPt Ψ p) (v : TangentSpace I p) :
    Ψ (riemannianExp I M p v) = riemannianExp I M p (mfderiv I I Ψ p v) := by
  have h := Ψ.riemannianExp_mfderiv p v
  rw [hp.eq] at h
  exact h.symm

/-- **The fixed set on a normal ball.** On a normal ball at a common fixed point `p`, a vector `v`
is sent by `exp_p` to a common fixed point exactly when it lies in the fixed tangent subspace. -/
theorem riemannianExp_mem_iInter_fixedPoints_iff {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {r : ℝ} (hr : IsNormalDomain I M p (Metric.ball 0 r)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 r) :
    riemannianExp I M p v ∈ ⋂ i, fixedPoints (Φ i) ↔ v ∈ fixedTangentSubspace Φ p := by
  -- The differentials `dΦ_i` preserve the ball, on which `exp_p` is injective.
  refine ⟨fun h i ↦ hr.injOn ?_ hv ?_, riemannianExp_mem_iInter_fixedPoints hp⟩
  · -- The norm of `T_(Φ_i p) M` is read at `p` after transporting along `Φ_i p = p`.
    have hnorm := (Φ i).norm_mfderiv p v
    rw [(mem_fixedPoints.1 (mem_iInter.1 hp i) : Φ i p = p)] at hnorm
    exact mem_ball_zero_iff.2 (hnorm.trans_lt (mem_ball_zero_iff.1 hv))
  · rw [← apply_riemannianExp_of_isFixedPt (Φ i) (mem_iInter.1 hp i)]
    exact mem_fixedPoints.1 (mem_iInter.1 h i)

/-- **Normal coordinates flatten the fixed set.** On the normal neighbourhood of a normal ball at
a common fixed point `p`, a point is a common fixed point exactly when its Riemannian logarithm lies
in the fixed tangent subspace. -/
theorem mem_iInter_fixedPoints_iff_riemannianLog_mem {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {r : ℝ} (hr : IsNormalDomain I M p (Metric.ball 0 r)) {z : M}
    (hz : z ∈ riemannianExp I M p '' Metric.ball 0 r) :
    z ∈ ⋂ i, fixedPoints (Φ i) ↔
      riemannianLog I M p (Metric.ball 0 r) z ∈ fixedTangentSubspace Φ p := by
  conv_lhs => rw [← riemannianExp_riemannianLog hz]
  exact riemannianExp_mem_iInter_fixedPoints_iff hp hr (riemannianLog_mem hz)

/-! ### Dimension of the fixed tangent subspace -/

/-- At a fixed point `p` of a Riemannian isometry `Ψ` and a vector `v` of the natural domain of
`exp_p` fixed by `dΨ_p`, the differential of `exp_p` at `v` conjugates the differential of `Ψ` at
`p` to its differential at `exp_p v`: `dΨ (d exp_p w) = d exp_p (dΨ_p w)`. -/
theorem mfderiv_apply_mfderiv_riemannianExp_of_isFixedPt (Ψ : RiemannianIsometry I I M M) {p : M}
    (hp : IsFixedPt Ψ p) {v : TangentSpace I p} (hv : v ∈ expDomain I M p)
    (hvf : mfderiv I I Ψ p v = v) (w : TangentSpace I p) :
    mfderiv I I Ψ (riemannianExp I M p v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w) =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v (mfderiv I I Ψ p w) := by
  have h := Ψ.mfderiv_apply_mfderiv_riemannianExp hv w
  rw [hvf, hp.eq] at h
  exact h

/-- **The fixed tangent subspace near a fixed point.** For a fixed vector `v` of a normal domain at
a common fixed point `p`, the differential of `exp_p` at `v` carries the fixed tangent subspace at
`p` onto the fixed tangent subspace at `exp_p v`. -/
theorem coe_fixedTangentSubspace_riemannianExp {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {U : Set (TangentSpace I p)} (hU : IsNormalDomain I M p U) {v : TangentSpace I p}
    (hv : v ∈ U) (hvf : v ∈ fixedTangentSubspace Φ p) :
    (fixedTangentSubspace Φ (riemannianExp I M p v) : Set (TangentSpace I _)) =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ''
        (fixedTangentSubspace Φ p : Set (TangentSpace I p)) := by
  obtain ⟨hinj, hsurj⟩ :=
    ((hU.isLocalDiffeomorphOn ⟨v, hv⟩).isInvertible_mfderiv (by simp)).bijective
  have hconj (i : ι) := mfderiv_apply_mfderiv_riemannianExp_of_isFixedPt (Φ i)
    (mem_iInter.1 hp i) (hU.subset_expDomain hv) (hvf i)
  ext u
  obtain ⟨w, rfl⟩ := hsurj u
  simp only [SetLike.mem_coe, mem_fixedTangentSubspace]
  refine ⟨fun h ↦ ⟨w, fun i ↦ hinj ((hconj i w).symm.trans (h i)), rfl⟩, ?_⟩
  rintro ⟨w', hw', hw'w⟩ i
  rw [← hinj hw'w, hconj i w', hw' i]

/-- The fixed tangent subspace has the same dimension at `p` and at `exp_p v`, for a fixed vector
`v` of a normal domain at a common fixed point `p`. -/
theorem finrank_fixedTangentSubspace_riemannianExp {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {U : Set (TangentSpace I p)} (hU : IsNormalDomain I M p U) {v : TangentSpace I p}
    (hv : v ∈ U) (hvf : v ∈ fixedTangentSubspace Φ p) :
    finrank ℝ (fixedTangentSubspace Φ (riemannianExp I M p v)) =
      finrank ℝ (fixedTangentSubspace Φ p) := by
  -- The differential of `exp_p` at `v`, as a linear equivalence from `T_p M`.
  let D : TangentSpace I p ≃ₗ[ℝ] TangentSpace I (riemannianExp I M p v) :=
    ((NormedSpace.fromTangentSpace v).symm.trans
      ((hU.isLocalDiffeomorphOn ⟨v, hv⟩).mfderivToContinuousLinearEquiv (by simp))).toLinearEquiv
  have hD : ⇑D.toLinearMap = mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v := by
    ext w
    simp only [D, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.trans_apply, NormedSpace.fromTangentSpace_symm_apply]
    rw [← ContinuousLinearEquiv.coe_coe, IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe]
  have hmap : fixedTangentSubspace Φ (riemannianExp I M p v) =
      (fixedTangentSubspace Φ p).map D.toLinearMap := by
    refine SetLike.coe_injective ?_
    rw [Submodule.map_coe, hD]
    exact coe_fixedTangentSubspace_riemannianExp hp hU hv hvf
  rw [hmap, LinearEquiv.finrank_map_eq]

/-! ### The fixed set as a manifold -/

variable (Φ) in
/-- **Each dimension stratum of the common fixed set is an embedded submanifold.** For a subspace
`L` of the model space, the common fixed points whose fixed tangent subspace has the dimension of
`L` form a smooth manifold modelled on `L`, their inclusion into `M` is a smooth embedding, and the
differential of the inclusion at each point `x` has image the fixed tangent subspace at `x`. -/
theorem exists_isManifold_iInter_fixedPoints_finrank (L : Submodule ℝ E) :
    ∃ C : ChartedSpace L {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
        finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L}, letI := C
      IsManifold 𝓘(ℝ, L) ∞ {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
        finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L} ∧
      IsSmoothEmbedding 𝓘(ℝ, L) I ∞ (Subtype.val : {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
        finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L} → M) ∧
      ∀ x : {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
          finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L},
        (mfderiv 𝓘(ℝ, L) I Subtype.val x).range = fixedTangentSubspace Φ x.1 := by
  -- Normal coordinates at the points of the stratum are slice charts for it.
  refine (exists_isManifold_isSmoothEmbedding_of_finrankSubspaceCharts ?_).imp
    fun C ⟨hC, hemb⟩ ↦ ⟨hC, hemb, fun x ↦ ?_⟩
  swap
  · -- Each `Φ_i` fixes the stratum pointwise, so its differential fixes the image of the
    -- differential of the inclusion; both subspaces have the dimension of `L`.
    let := C
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨w, rfl⟩ i
      have hval : Φ i ∘ Subtype.val = (Subtype.val : {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
          finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L} → M) :=
        funext fun y ↦ (mem_iInter.1 y.2.1 i).eq
      have h := mfderiv_comp x ((Φ i).mdifferentiableAt _)
        ((hemb.contMDiff x).mdifferentiableAt (by simp))
      rw [hval] at h
      exact (congrArg (fun T ↦ T w) h).symm
    · rw [LinearMap.finrank_range_of_inj (hemb.isImmersion.mfderiv_injective (by simp) x), x.2.2]
      rfl
  intro p ⟨hp, hdim⟩
  obtain ⟨r, -, hr⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  -- Normal coordinates are read in the model space `E` through the fibre of the tangent bundle's
  -- trivialization at `p`.
  let A : E ≃L[ℝ] TangentSpace I p :=
    ((trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ p
      (mem_baseSet_trivializationAt E (TangentSpace I) p)).symm
  obtain ⟨Ψ, hΨs, hΨ⟩ := hr.exists_partialDiffeomorph_riemannianExp_comp A
    (Metric.isOpen_ball.preimage A.continuous) (mapsTo_preimage A _)
  let q : OpenPartialHomeomorph M E := Ψ.toOpenPartialHomeomorph.symm
  refine ⟨q, (fixedTangentSubspace Φ p).map (A.symm.toLinearEquiv : TangentSpace I p →ₗ[ℝ] E),
    ?_, fun z hz ↦ ?_, fun w hw ↦ ?_, fun z hz ↦ ?_, ?_⟩
  · -- The base point is `exp_p (A 0)`.
    have h0 : (0 : E) ∈ Ψ.source := by
      rw [hΨs, mem_preimage, map_zero]
      exact hr.zero_mem
    have hp0 : Ψ 0 = p := by rw [hΨ, comp_apply, map_zero, riemannianExp_zero]
    exact hp0 ▸ Ψ.map_source h0
  · exact Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds hz)
  · exact Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hw)
  · -- Write `z = exp_p (A w)` with `A w` in the normal ball.
    have hw : q z ∈ Ψ.source := q.map_source hz
    have hzw : riemannianExp I M p (A (q z)) = z := by
      rw [← comp_apply (f := riemannianExp I M p), ← hΨ]
      exact q.left_inv hz
    have hball : A (q z) ∈ Metric.ball 0 r := by rwa [hΨs] at hw
    have hiff := riemannianExp_mem_iInter_fixedPoints_iff hp hr hball
    rw [hzw] at hiff
    rw [mem_ofPred_eq, Submodule.mem_map_equiv, ContinuousLinearEquiv.toLinearEquiv_symm,
      LinearEquiv.symm_symm, ContinuousLinearEquiv.coe_toLinearEquiv]
    refine ⟨fun h ↦ hiff.1 h.1, fun h ↦ ⟨hiff.2 h, ?_⟩⟩
    rw [← hzw, finrank_fixedTangentSubspace_riemannianExp hp hr hball h, hdim]
  · rw [LinearEquiv.finrank_map_eq, hdim]

end TauCeti.RiemannianIsometry
