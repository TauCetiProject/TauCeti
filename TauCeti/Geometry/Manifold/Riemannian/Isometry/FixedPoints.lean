/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential

/-!
# Common fixed points of Riemannian isometries

Let `Φ i`, for `i` in an arbitrary index type, be smooth Riemannian isometries of a Riemannian
manifold `M`, and let `M^Φ = ⋂ i, fixedPoints (Φ i)` be their common fixed set. For a group `K`
acting on `M` by isometries, take `Φ k` to be the action of `k`; no topology or Lie group structure
on the index type is needed, and neither completeness of the metric nor compactness of `M` is
assumed.

At a point `p`, the tangent vectors fixed by all the differentials `dΦ_i` at `p` form the
**fixed tangent subspace** `TauCeti.RiemannianIsometry.fixedTangentSubspace Φ p`. When `p` is
fixed this is the subspace of invariants of the isotropy representation on `T_p M`. This file
proves that `M^Φ` is closed and totally geodesic, that near each of its points `p` it is the image
under `exp_p` of a neighbourhood of the origin in the fixed tangent subspace, and that the fixed
points at which the fixed tangent subspace has a given dimension form a smooth manifold. Different
parts of `M^Φ` may have different dimensions.

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
`Φ_i ∘ exp_p = exp_p ∘ dΦ_i` at a fixed vector `v` of the normal ball shows that the differential
of `exp_p` at `v` conjugates the differentials of the `Φ_i` at `p` to those at `exp_p v`, so it
carries the fixed tangent subspace at `p` onto the one at `exp_p v`
(`TauCeti.RiemannianIsometry.coe_fixedTangentSubspace_riemannianExp`). Hence, for each dimension,
the fixed points whose fixed tangent subspace has that dimension form a smooth manifold, with smooth
inclusion into `M` (`TauCeti.RiemannianIsometry.exists_isManifold_iInter_fixedPoints_finrank`).

Finally, the common fixed set is totally geodesic: the maximal geodesic through a fixed point with
a fixed initial velocity stays in `M^Φ` for all time
(`TauCeti.RiemannianIsometry.maximalGeodesic_mem_iInter_fixedPoints`), because each `Φ_i` carries
it to the maximal geodesic with the same initial data.

## Main definitions

* `TauCeti.RiemannianIsometry.fixedTangentSubspace Φ p`: the tangent vectors at `p` fixed by the
  differentials of all the `Φ i` at `p`.

## Main results

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
  with fixed tangent subspace of a given dimension form a smooth manifold.

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

/-- The **fixed tangent subspace** of a family of Riemannian isometries at `p`: the tangent vectors
at `p` fixed by the differentials at `p` of all the `Φ i`. When `p` is a common fixed point, the
exponential map at `p` carries it onto the common fixed set near `p`. -/
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

/-- The common fixed set of a family of isometries of a Hausdorff manifold is closed. -/
theorem isClosed_iInter_fixedPoints [T2Space M] : IsClosed (⋂ i, fixedPoints (Φ i)) :=
  isClosed_iInter fun i ↦ isClosed_fixedPoints (Φ i).mdifferentiable.continuous

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M]

/-! ### The fixed set is totally geodesic -/

variable {Φ}

/-- **The common fixed set is totally geodesic.** The maximal geodesic through a common fixed
point `p` whose initial velocity lies in the fixed tangent subspace consists of common fixed points:
each `Φ i` carries it to the maximal geodesic with the same initial data. -/
theorem maximalGeodesic_mem_iInter_fixedPoints {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {v : TangentSpace I p} (hv : v ∈ fixedTangentSubspace Φ p) (t : ℝ) :
    maximalGeodesic I M p v t ∈ ⋂ i, fixedPoints (Φ i) := by
  simp only [mem_iInter, mem_fixedPoints] at hp ⊢
  intro i
  have h := (Φ i).maximalGeodesic_mfderiv p v t
  rw [hv i, hp i] at h
  exact h.symm

/-- The exponential map at a common fixed point sends the fixed tangent subspace into the common
fixed set. -/
theorem riemannianExp_mem_iInter_fixedPoints {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {v : TangentSpace I p} (hv : v ∈ fixedTangentSubspace Φ p) :
    riemannianExp I M p v ∈ ⋂ i, fixedPoints (Φ i) := by
  simp only [mem_iInter, mem_fixedPoints] at hp ⊢
  intro i
  have h := (Φ i).riemannianExp_mfderiv p v
  rw [hv i, hp i] at h
  exact h.symm

/-! ### Normal coordinates are slice charts -/

/-- At a common fixed point, the differential of each `Φ i` intertwines the exponential map with
itself: `Φ_i (exp_p v) = exp_p (dΦ_i v)`. -/
theorem apply_riemannianExp_of_mem_iInter_fixedPoints {p : M}
    (hp : p ∈ ⋂ i, fixedPoints (Φ i)) (i : ι) (v : TangentSpace I p) :
    Φ i (riemannianExp I M p v) = riemannianExp I M p (mfderiv I I (Φ i) p v) := by
  have h := (Φ i).riemannianExp_mfderiv p v
  rw [(mem_fixedPoints.1 (mem_iInter.1 hp i) : Φ i p = p)] at h
  exact h.symm

/-- **The fixed set on a normal ball.** On a normal ball at a common fixed point `p`, a vector `v`
is sent by `exp_p` to a common fixed point exactly when it lies in the fixed tangent subspace: the
differentials `dΦ_i` preserve the ball, on which `exp_p` is injective. -/
theorem riemannianExp_mem_iInter_fixedPoints_iff {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {r : ℝ} (hr : IsNormalDomain I M p (Metric.ball 0 r)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 r) :
    riemannianExp I M p v ∈ ⋂ i, fixedPoints (Φ i) ↔ v ∈ fixedTangentSubspace Φ p := by
  refine ⟨fun h i ↦ hr.injOn ?_ hv ?_, riemannianExp_mem_iInter_fixedPoints hp⟩
  · -- The norm of `T_(Φ_i p) M` is read at `p` after transporting along `Φ_i p = p`.
    have hnorm := (Φ i).norm_mfderiv p v
    rw [(mem_fixedPoints.1 (mem_iInter.1 hp i) : Φ i p = p)] at hnorm
    exact mem_ball_zero_iff.2 (hnorm.trans_lt (mem_ball_zero_iff.1 hv))
  · rw [← apply_riemannianExp_of_mem_iInter_fixedPoints hp]
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

/-- At a common fixed point `p` and a fixed vector `v` of a normal ball, the differential of
`exp_p` at `v` conjugates the differential of each `Φ i` at `p` to its differential at `exp_p v`:
`dΦ_i (d exp_p w) = d exp_p (dΦ_i w)`. -/
theorem mfderiv_apply_mfderiv_riemannianExp {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {r : ℝ} (hr : IsNormalDomain I M p (Metric.ball 0 r)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 r) (hvf : v ∈ fixedTangentSubspace Φ p) (i : ι)
    (w : TangentSpace I p) :
    mfderiv I I (Φ i) (riemannianExp I M p v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w) =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
        (mfderiv I I (Φ i) p w) := by
  have hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v :=
    (hr.isLocalDiffeomorphOn ⟨v, hv⟩).mdifferentiableAt (by simp)
  -- Both sides are derivatives at `v` of the same map `Φ_i ∘ exp_p = exp_p ∘ dΦ_i`.
  have hfun : Φ i ∘ riemannianExp I M p = riemannianExp I M p ∘ mfderiv I I (Φ i) p :=
    funext (apply_riemannianExp_of_mem_iInter_fixedPoints hp i)
  have hleft := ((Φ i).mdifferentiableAt _).hasMFDerivAt.comp v hexp.hasMFDerivAt
  have hexp' : HasMFDerivAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p)
      (mfderiv I I (Φ i) p v)
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v) := by
    rw [hvf i]
    exact hexp.hasMFDerivAt
  have hright := hexp'.comp v (mfderiv I I (Φ i) p).hasMFDerivAt
  rw [hfun] at hleft
  exact congrArg (fun L ↦ L w) (hasMFDerivAt_unique hleft hright)

/-- **The fixed tangent subspace near a fixed point.** For a fixed vector `v` of a normal ball at
a common fixed point `p`, the differential of `exp_p` at `v` carries the fixed tangent subspace at
`p` onto the fixed tangent subspace at `exp_p v`. -/
theorem coe_fixedTangentSubspace_riemannianExp {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {r : ℝ} (hr : IsNormalDomain I M p (Metric.ball 0 r)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 r) (hvf : v ∈ fixedTangentSubspace Φ p) :
    (fixedTangentSubspace Φ (riemannianExp I M p v) : Set (TangentSpace I _)) =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ''
        (fixedTangentSubspace Φ p : Set (TangentSpace I p)) := by
  set D := mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  have hinj : Injective D := hr.injective_mfderiv_riemannianExp hv
  -- `D` is an injective endomorphism of the finite-dimensional model space, hence onto.
  have hsurj : Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hinj
  have hconj := mfderiv_apply_mfderiv_riemannianExp hp hr hv hvf
  ext u
  obtain ⟨w, rfl⟩ := hsurj u
  simp only [SetLike.mem_coe, mem_fixedTangentSubspace]
  refine ⟨fun h ↦ ⟨w, fun i ↦ hinj ((hconj i w).symm.trans (h i)), rfl⟩, ?_⟩
  rintro ⟨w', hw', hw'w⟩ i
  rw [← hinj hw'w, hconj i w', hw' i]

/-- The fixed tangent subspace has the same dimension at `p` and at `exp_p v`, for a fixed vector
`v` of a normal ball at a common fixed point `p`. -/
theorem finrank_fixedTangentSubspace_riemannianExp {p : M} (hp : p ∈ ⋂ i, fixedPoints (Φ i))
    {r : ℝ} (hr : IsNormalDomain I M p (Metric.ball 0 r)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 r) (hvf : v ∈ fixedTangentSubspace Φ p) :
    finrank ℝ (fixedTangentSubspace Φ (riemannianExp I M p v)) =
      finrank ℝ (fixedTangentSubspace Φ p) := by
  -- The differential of `exp_p` at `v`, as a linear map between the vector space structures of
  -- the two tangent spaces carrying the fixed tangent subspaces.
  let D : TangentSpace I p →ₗ[ℝ] TangentSpace I (riemannianExp I M p v) :=
    { toFun := mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
      map_add' := map_add _
      map_smul' := map_smul _ }
  have hinj : Injective D := hr.injective_mfderiv_riemannianExp hv
  have hmap : fixedTangentSubspace Φ (riemannianExp I M p v) = (fixedTangentSubspace Φ p).map D :=
    SetLike.coe_injective ((coe_fixedTangentSubspace_riemannianExp hp hr hv hvf).trans
      (Submodule.map_coe D _).symm)
  rw [hmap]
  exact (Submodule.equivMapOfInjective D hinj _).finrank_eq.symm

/-! ### The fixed set as a manifold -/

variable (Φ) in
/-- **Each dimension stratum of the common fixed set is a smooth manifold.** For a subspace `L` of
the model space, the common fixed points whose fixed tangent subspace has the dimension of `L` form
a smooth manifold modelled on `L`, and their inclusion into `M` is smooth. Its charts are normal
coordinates at its points, which flatten it onto the fixed tangent subspaces. -/
theorem exists_isManifold_iInter_fixedPoints_finrank (L : Submodule ℝ E) :
    ∃ C : ChartedSpace L {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
        finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L}, letI := C
      IsManifold 𝓘(ℝ, L) ∞ {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
        finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L} ∧
      ContMDiff 𝓘(ℝ, L) I ∞ (Subtype.val : {x : M | x ∈ ⋂ i, fixedPoints (Φ i) ∧
        finrank ℝ (fixedTangentSubspace Φ x) = finrank ℝ L} → M) := by
  refine exists_isManifold_of_finrankSubspaceCharts fun p ⟨hp, hdim⟩ ↦ ?_
  obtain ⟨r, -, hr⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  -- The tangent space `T_p M` carries the Riemannian norm; normal coordinates are read in the
  -- model space `E` through the identity of the underlying vector spaces.
  let A : E ≃L[ℝ] TangentSpace I p :=
    (LinearEquiv.refl ℝ E : E ≃ₗ[ℝ] TangentSpace I p).toContinuousLinearEquiv
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
