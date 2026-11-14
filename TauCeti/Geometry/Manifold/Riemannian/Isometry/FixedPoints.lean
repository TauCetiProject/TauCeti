/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action

import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# Fixed points of groups of Riemannian isometries

Let a group `K` act on a Riemannian manifold `M` by smooth maps preserving the metric. No
topology or Lie group structure on `K` is required. This file shows that the common fixed set
`M^K = MulAction.fixedPoints K M` is, near each of its points `p`, the exponential image of the
subspace

`V^K = {v ∈ T_p M | d(k •)_p v = v for every k ∈ K}`

of tangent vectors fixed by the derivatives at `p`. The argument uses only the naturality of the
exponential map under isometries, `k (exp_p v) = exp_p (d(k •)_p v)` at a fixed point `p`
(`TauCeti.RiemannianIsometry.riemannianExp_mfderiv`), and its injectivity on a normal ball. Each
`d(k •)_p` is a linear isometry of `T_p M`, so it maps every ball around the origin into itself,
and two vectors of a normal ball with the same exponential image are equal. No completeness of
the metric and no compactness of `M` or `K` is needed.

* The fixed set is closed, since each group element acts continuously
  (`TauCeti.isClosed_fixedPoints_of_continuousConstSMul`).
* At a fixed point the invariant vectors of the tangent representation are `V^K`
  (`TauCeti.mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints`), and each `d(k •)_p`
  preserves every ball around the origin of `T_p M`
  (`TauCeti.mfderiv_mem_ball_of_apply_eq_self`).
* A geodesic leaving a fixed point with fixed initial velocity stays in `M^K` for all times
  (`TauCeti.maximalGeodesic_mem_fixedPoints`): the fixed set is totally geodesic.
* On a normal domain `U` at `p` stable under the derivatives, a vector `v` has `exp_p v ∈ M^K`
  exactly when it is fixed by every derivative
  (`TauCeti.Manifold.IsNormalDomain.riemannianExp_mem_fixedPoints_iff`), so
  `exp_p (U ∩ V^K) = M^K ∩ exp_p U`
  (`TauCeti.Manifold.IsNormalDomain.image_riemannianExp_inter_eq_fixedPoints_inter`). Every normal
  ball is such a domain
  (`TauCeti.Manifold.IsNormalDomain.image_riemannianExp_ball_inter_eq_fixedPoints_inter`).
* Hence the Riemannian logarithm on such a domain, a smooth chart of `M` around `p`, carries `M^K`
  onto the linear subspace `V^K` (`TauCeti.Manifold.IsNormalDomain.isSliceChart_fixedPoints`).
  In particular `M^K` has a smooth slice chart around each of its points
  (`TauCeti.exists_isSliceChart_fixedPoints`), with model subspace `V^K` at `p`; its dimension may
  vary from one fixed point to another.

For a group preserving a nondegenerate two-form as well, `V^K` is a symplectic subspace
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation_of_inner`),
so near each point of the fixed set of a group of symplectic isometries, the fixed set is flattened
onto a symplectic subspace of the tangent space.

The basic identities are stated for a single isometry fixing `p`, in the namespace
`TauCeti.RiemannianIsometry`. A compact group acting smoothly preserves the metric obtained by
averaging any smooth metric (`TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`), so the
results apply to smooth actions of compact Lie groups once that metric is chosen.

For a family of isometries `Φ i`, indexed by an arbitrary type, the same argument describes the
common fixed set `M^Φ = ⋂ i, fixedPoints (Φ i)` in terms of the **fixed tangent subspace**
`TauCeti.RiemannianIsometry.fixedTangentSubspace Φ p` of vectors fixed by every `dΦ_i` at `p`.
For a group acting by isometries this is the subspace of invariants of the isotropy representation
(`TauCeti.RiemannianIsometry.fixedTangentSubspace_stabilizer_eq_invariants`).

* The common fixed set is closed (`TauCeti.RiemannianIsometry.isClosed_iInter_fixedPoints`) and
  totally geodesic (`TauCeti.RiemannianIsometry.maximalGeodesic_mem_iInter_fixedPoints`).
* On a normal ball at a common fixed point `p`, `exp_p v` is a common fixed point exactly when `v`
  lies in the fixed tangent subspace
  (`TauCeti.RiemannianIsometry.riemannianExp_mem_iInter_fixedPoints_iff`), so normal coordinates
  flatten `M^Φ` onto it (`TauCeti.RiemannianIsometry.mem_iInter_fixedPoints_iff_riemannianLog_mem`).
* Differentiating `Φ_i ∘ exp_p = exp_p ∘ dΦ_i` at a fixed vector `v` of a normal domain shows that
  the differential of `exp_p` at `v` carries the fixed tangent subspace at `p` onto the one at
  `exp_p v` (`TauCeti.RiemannianIsometry.coe_fixedTangentSubspace_riemannianExp`), so its dimension
  is locally constant on `M^Φ`
  (`TauCeti.RiemannianIsometry.finrank_fixedTangentSubspace_riemannianExp`).
* Hence, for each dimension, the common fixed points whose fixed tangent subspace has that
  dimension form a smooth manifold whose inclusion into `M` is a smooth embedding, with tangent
  space the fixed tangent subspace
  (`TauCeti.RiemannianIsometry.exists_isManifold_iInter_fixedPoints_finrank`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (the fixed set of a group of isometries via the
  exponential map).
* S. Kobayashi, *Fixed points of isometries*, Nagoya Mathematical Journal 13 (1958), 63–68.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Chapter 5
  (naturality of the exponential map) and Chapter 6 (normal neighbourhoods).
-/

public section

open Bundle Manifold Module Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace RiemannianIsometry

/-! ### The fixed tangent subspace -/

section FixedTangentSubspace

open Function

variable {ι : Type*} (Φ : ι → RiemannianIsometry I I M M)

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

end FixedTangentSubspace

end RiemannianIsometry

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable [I.Boundaryless] [T2Space M]

namespace RiemannianIsometry

section Single

variable {Φ : Isom I M} {p : M} {v : TangentSpace I p}

/-- An isometry fixing a point `p` and a tangent vector `v` at `p` fixes the maximal geodesic
from `p` with initial velocity `v` at every time. -/
theorem apply_maximalGeodesic_of_mfderiv_eq (hp : Φ p = p) (hv : mfderiv I I Φ p v = v)
    (t : ℝ) : Φ (maximalGeodesic I M p v t) = maximalGeodesic I M p v t := by
  rw [← Φ.maximalGeodesic_mfderiv]
  exact maximalGeodesic_congr hp hv t

/-- An isometry fixing a point `p` and a tangent vector `v` at `p` fixes `exp_p v`. -/
theorem apply_riemannianExp_of_mfderiv_eq (hp : Φ p = p) (hv : mfderiv I I Φ p v = v) :
    Φ (riemannianExp I M p v) = riemannianExp I M p v := by
  rw [riemannianExp_def]
  exact Φ.apply_maximalGeodesic_of_mfderiv_eq hp hv 1

/-- **Fixed points in a normal neighbourhood.** Let an isometry fix `p`, and let `v` be a vector
of a normal domain at `p` whose image under the differential at `p` also lies in that domain.
Then the isometry fixes `exp_p v` exactly when its differential fixes `v`. -/
theorem apply_riemannianExp_eq_self_iff {U : Set (TangentSpace I p)}
    (hU : IsNormalDomain I M p U) (hp : Φ p = p) (hv : v ∈ U) (hΦv : mfderiv I I Φ p v ∈ U) :
    Φ (riemannianExp I M p v) = riemannianExp I M p v ↔ mfderiv I I Φ p v = v := by
  refine ⟨fun h ↦ hU.injOn hΦv hv ?_, Φ.apply_riemannianExp_of_mfderiv_eq hp⟩
  rw [← h, ← Φ.riemannianExp_mfderiv]
  exact (riemannianExp_congr hp rfl).symm

end Single

/-! ### Families of isometries -/

section Family

open Function

variable {ι : Type*} {Φ : ι → RiemannianIsometry I I M M}

/-- **The common fixed set is totally geodesic.** The maximal geodesic through a common fixed
point `p` whose initial velocity lies in the fixed tangent subspace consists of common fixed points
on its maximal interval. Off that interval it takes the junk value `p`, which is also fixed. -/
theorem maximalGeodesic_mem_iInter_fixedPoints {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {v : TangentSpace I p} (hv : v ∈ fixedTangentSubspace Φ p) (t : ℝ) :
    maximalGeodesic I M p v t ∈ ⋂ i, fixedPoints (Φ i) :=
  mem_iInter.2 fun i ↦ (Φ i).apply_maximalGeodesic_of_mfderiv_eq (mem_iInter.1 hp i) (hv i) t

/-- The exponential map at a common fixed point sends the fixed tangent subspace into the common
fixed set. Off the natural domain of `exp_p` it takes the junk value `p`, which is also fixed. -/
theorem riemannianExp_mem_iInter_fixedPoints {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {v : TangentSpace I p} (hv : v ∈ fixedTangentSubspace Φ p) :
    riemannianExp I M p v ∈ ⋂ i, fixedPoints (Φ i) :=
  mem_iInter.2 fun i ↦ (Φ i).apply_riemannianExp_of_mfderiv_eq (mem_iInter.1 hp i) (hv i)

/-! ### Normal coordinates are slice charts -/

/-- **The fixed set on a normal ball.** On a normal ball at a common fixed point `p`, a vector `v`
is sent by `exp_p` to a common fixed point exactly when it lies in the fixed tangent subspace. -/
theorem riemannianExp_mem_iInter_fixedPoints_iff {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {r : ℝ} (hr : IsNormalDomain I M p (Metric.ball 0 r)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 r) :
    riemannianExp I M p v ∈ ⋂ i, fixedPoints (Φ i) ↔ v ∈ fixedTangentSubspace Φ p := by
  -- The differentials `dΦ_i` preserve the ball, on which `exp_p` is injective.
  refine ⟨fun h i ↦ ((Φ i).apply_riemannianExp_eq_self_iff hr (mem_iInter.1 hp i) hv ?_).1
    (mem_iInter.1 h i), riemannianExp_mem_iInter_fixedPoints hp⟩
  -- The norm of `T_(Φ_i p) M` is read at `p` after transporting along `Φ_i p = p`.
  have hnorm := (Φ i).norm_mfderiv p v
  rw [(mem_fixedPoints.1 (mem_iInter.1 hp i) : Φ i p = p)] at hnorm
  exact mem_ball_zero_iff.2 (hnorm.trans_lt (mem_ball_zero_iff.1 hv))

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

end Family

end RiemannianIsometry

/-! ### Groups acting by isometries -/

section Action

open _root_.MulAction

variable {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M] {p : M}
  {v : TangentSpace I p}
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)

include hK

/-- **The fixed set is totally geodesic.** For a group acting by isometries, the maximal
geodesic leaving a fixed point `p` with initial velocity fixed by the differential of every
group element stays in the fixed set at every time. -/
theorem maximalGeodesic_mem_fixedPoints (hp : p ∈ fixedPoints K M)
    (hv : ∀ k : K, mfderiv I I (k • ·) p v = v) (t : ℝ) :
    maximalGeodesic I M p v t ∈ fixedPoints K M := fun k ↦ by
  have h := (RiemannianIsometry.constSMul k (hK k)).apply_maximalGeodesic_of_mfderiv_eq
    (by simpa using hp k) (by rw [RiemannianIsometry.coe_constSMul]; exact hv k) t
  rwa [RiemannianIsometry.coe_constSMul] at h

/-- For a group acting by isometries, the exponential map at a fixed point `p` sends tangent
vectors fixed by the differential of every group element into the fixed set. -/
theorem riemannianExp_mem_fixedPoints (hp : p ∈ fixedPoints K M)
    (hv : ∀ k : K, mfderiv I I (k • ·) p v = v) :
    riemannianExp I M p v ∈ fixedPoints K M := by
  rw [riemannianExp_def]
  exact maximalGeodesic_mem_fixedPoints hK hp hv 1

namespace Manifold.IsNormalDomain

variable {U : Set (TangentSpace I p)}

/-- **The fixed set in a normal neighbourhood.** Let a group act by isometries fixing `p`, and
let `U` be a normal domain at `p` mapped into itself by the differential at `p` of every group
element, for instance a normal ball. A vector `v ∈ U` has `exp_p v` in the fixed set exactly when
it is fixed by the differential of every group element. -/
theorem riemannianExp_mem_fixedPoints_iff (hU : IsNormalDomain I M p U)
    (hp : p ∈ fixedPoints K M) (hUK : ∀ k : K, ∀ w ∈ U, mfderiv I I (k • ·) p w ∈ U)
    (hv : v ∈ U) :
    riemannianExp I M p v ∈ fixedPoints K M ↔ ∀ k : K, mfderiv I I (k • ·) p v = v := by
  refine ⟨fun h k ↦ ?_, riemannianExp_mem_fixedPoints hK hp⟩
  have hk := (RiemannianIsometry.constSMul k (hK k)).apply_riemannianExp_eq_self_iff hU
    (by simpa using hp k) hv (by rw [RiemannianIsometry.coe_constSMul]; exact hUK k v hv)
  rw [RiemannianIsometry.coe_constSMul] at hk
  exact hk.1 (h k)

/-- The case of a normal ball in `IsNormalDomain.riemannianExp_mem_fixedPoints_iff`: the
differential at `p` of each group element preserves the ball. -/
theorem riemannianExp_mem_fixedPoints_iff_of_mem_ball {r : ℝ}
    (hU : IsNormalDomain I M p (Metric.ball 0 r)) (hp : p ∈ fixedPoints K M)
    (hv : v ∈ Metric.ball 0 r) :
    riemannianExp I M p v ∈ fixedPoints K M ↔ ∀ k : K, mfderiv I I (k • ·) p v = v :=
  hU.riemannianExp_mem_fixedPoints_iff hK hp
    (fun k _ hw ↦ mfderiv_mem_ball_of_apply_eq_self (hp k) (hK k p) hw) hv

/-- **The fixed set is the exponential image of the fixed tangent vectors.** For a group acting
by isometries fixing `p`, and a normal domain `U` at `p` mapped into itself by the differential at
`p` of every group element, the fixed set meets the normal neighbourhood `exp_p U` in the
exponential image of the vectors of `U` fixed by the differential of every group element. -/
theorem image_riemannianExp_inter_eq_fixedPoints_inter (hU : IsNormalDomain I M p U)
    (hp : p ∈ fixedPoints K M) (hUK : ∀ k : K, ∀ w ∈ U, mfderiv I I (k • ·) p w ∈ U) :
    riemannianExp I M p '' (U ∩ {v | ∀ k : K, mfderiv I I (k • ·) p v = v}) =
      fixedPoints K M ∩ riemannianExp I M p '' U := by
  ext q
  constructor
  · rintro ⟨w, ⟨hw, hwK⟩, rfl⟩
    exact ⟨riemannianExp_mem_fixedPoints hK hp hwK, mem_image_of_mem _ hw⟩
  · rintro ⟨hq, w, hw, rfl⟩
    exact ⟨w, ⟨hw, (hU.riemannianExp_mem_fixedPoints_iff hK hp hUK hw).1 hq⟩, rfl⟩

/-- The case of a normal ball `B` in
`IsNormalDomain.image_riemannianExp_inter_eq_fixedPoints_inter`:
`exp_p (B ∩ V^K) = M^K ∩ exp_p B`. -/
theorem image_riemannianExp_ball_inter_eq_fixedPoints_inter {r : ℝ}
    (hU : IsNormalDomain I M p (Metric.ball 0 r)) (hp : p ∈ fixedPoints K M) :
    riemannianExp I M p '' (Metric.ball 0 r ∩ {v | ∀ k : K, mfderiv I I (k • ·) p v = v}) =
      fixedPoints K M ∩ riemannianExp I M p '' Metric.ball 0 r :=
  hU.image_riemannianExp_inter_eq_fixedPoints_inter hK hp
    fun k _ hw ↦ mfderiv_mem_ball_of_apply_eq_self (hp k) (hK k p) hw

/-- **The Riemannian logarithm is a slice chart for the fixed set.** For a group acting by
isometries fixing `p`, and a normal domain `U` at `p` mapped into itself by the differential at
`p` of every group element, the Riemannian logarithm on `exp_p U` carries the fixed set onto the
linear subspace of tangent vectors fixed by the differential at `p` of every group element. -/
theorem isSliceChart_fixedPoints (hU : IsNormalDomain I M p U) (hp : p ∈ fixedPoints K M)
    (hUK : ∀ k : K, ∀ w ∈ U, mfderiv I I (k • ·) p w ∈ U) :
    IsSliceChart hU.toPartialDiffeomorph.symm.toOpenPartialHomeomorph
      {v | ∀ k : K, mfderiv I I (k • ·) p v = v} (fixedPoints K M) := by
  refine isSliceChart_iff.2 fun q hq ↦ ?_
  simp only [PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
    PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
    hU.toPartialDiffeomorph_target] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have hlog : hU.toPartialDiffeomorph.symm.toOpenPartialHomeomorph (riemannianExp I M p w) = w :=
    by simpa [PartialDiffeomorph.symm_toPartialEquiv] using hU.riemannianLog_riemannianExp hw
  rw [hlog, mem_ofPred_eq]
  exact hU.riemannianExp_mem_fixedPoints_iff hK hp hUK hw

/-- The case of a normal ball in `IsNormalDomain.isSliceChart_fixedPoints`. -/
theorem isSliceChart_fixedPoints_of_ball {r : ℝ} (hU : IsNormalDomain I M p (Metric.ball 0 r))
    (hp : p ∈ fixedPoints K M) :
    IsSliceChart hU.toPartialDiffeomorph.symm.toOpenPartialHomeomorph
      {v | ∀ k : K, mfderiv I I (k • ·) p v = v} (fixedPoints K M) :=
  hU.isSliceChart_fixedPoints hK hp
    fun k _ hw ↦ mfderiv_mem_ball_of_apply_eq_self (hp k) (hK k p) hw

end Manifold.IsNormalDomain

/-- **A slice chart for the fixed set of a group of isometries.** For a group acting on `M` by
isometries and a fixed point `p`, there is a smooth chart of `M` around `p` with values in
`T_p M`, centred at `p` and with inverse the exponential map at `p`, which carries the fixed set
onto the linear subspace of tangent vectors fixed by the differential at `p` of every group
element. The chart is the Riemannian logarithm on a normal ball
(`TauCeti.Manifold.IsNormalDomain.isSliceChart_fixedPoints_of_ball`). -/
theorem exists_isSliceChart_fixedPoints (hp : p ∈ fixedPoints K M) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, TangentSpace I p) M (TangentSpace I p) ∞,
      p ∈ φ.source ∧ φ p = 0 ∧ ⇑φ.symm = riemannianExp I M p ∧
        IsSliceChart φ.toOpenPartialHomeomorph {v | ∀ k : K, mfderiv I I (k • ·) p v = v}
          (fixedPoints K M) := by
  obtain ⟨r, hr, hU⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  refine ⟨hU.toPartialDiffeomorph.symm, ?_, ?_, ?_, hU.isSliceChart_fixedPoints_of_ball hK hp⟩
  · simp [PartialDiffeomorph.symm_toPartialEquiv, hU.self_mem_image]
  · simpa [PartialDiffeomorph.symm_toPartialEquiv] using
      hU.riemannianLog_riemannianExp (Metric.mem_ball_self hr)
  · simp

end Action

end TauCeti
