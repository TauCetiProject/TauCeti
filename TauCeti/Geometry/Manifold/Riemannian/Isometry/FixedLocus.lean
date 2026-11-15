/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints
public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.LinearSlice

import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The fixed locus of a group of isometries is an embedded submanifold

Let a group `K` act on a Riemannian manifold `M` by smooth maps preserving the metric. No topology
or Lie group structure on `K` is required. The common fixed set `M^K` is, near each of its points
`p`, the exponential image of the subspace `V^K_p ⊆ T_p M` of tangent vectors fixed by every
differential `d(k •)_p` (`TauCeti.exists_isSliceChart_fixedPoints`). This file shows that `M^K`
is a disjoint union of closed embedded submanifolds, one for each dimension of `V^K_p`, with
tangent space `V^K_p` at each point.

The dimension of `V^K` is locally constant along `M^K`. If `w ∈ V^K_p` lies in a normal ball at a
fixed point `p`, then `q = exp_p w` is fixed, and differentiating the naturality of the exponential
map, `k • exp_p v = exp_p (d(k •)_p v)`, at `w` shows that the invertible differential
`D = d(exp_p)_w` conjugates `d(k •)_p` into `d(k •)_q`
(`TauCeti.mfderiv_smul_mfderiv_riemannianExp`). Hence `D` carries `V^K_p` onto `V^K_q`, and the two
spaces have the same dimension
(`TauCeti.Manifold.IsNormalDomain.finrank_tangentInvariants_riemannianExp`).

So for each `d` the *stratum* `M^K_d` of fixed points `p` with `dim V^K_p = d`
(`TauCeti.fixedPointsFinrank`) is closed in `M` and open in `M^K`. The Riemannian logarithm at each
of its points is a smooth chart flattening it onto a `d`-dimensional subspace, so it is a smooth
embedded submanifold of dimension `d`
(`TauCeti.exists_isSmoothEmbedding_fixedPointsFinrank`). Its tangent space at `p` is `V^K_p`: the
differential of every map into `M^K` takes values in `V^K`, and an immersion of a `d`-dimensional
manifold into `M^K_d` fills it (`TauCeti.range_mfderiv_eq_tangentInvariants`). Different strata
may have different dimensions, and a connected component of `M^K` lies in a single stratum. None
of this needs completeness of the metric or compactness of `M` or `K`; a compact Lie group acting
smoothly preserves an averaged metric, so the results apply to it after choosing that metric.

## Main definitions

* `TauCeti.tangentInvariants I K x`: the tangent vectors at `x` fixed by the differential of every
  element of the stabilizer of `x`, the invariants of the tangent representation.
* `TauCeti.fixedPointsFinrank I K M d`: the fixed points `p` with `dim V^K_p = d`.

## Main results

* `TauCeti.mfderiv_smul_mfderiv_riemannianExp`: at `q = exp_p w` with `w` fixed, the differential
  of the exponential map intertwines `d(k •)_p` and `d(k •)_q`.
* `TauCeti.Manifold.IsNormalDomain.finrank_tangentInvariants_riemannianExp`: `V^K_q` and `V^K_p`
  have the same dimension.
* `TauCeti.eventually_finrank_tangentInvariants_eq`: the dimension of `V^K` is locally constant
  along `M^K`.
* `TauCeti.isClosed_fixedPointsFinrank`, `TauCeti.eventually_mem_fixedPointsFinrank`: each stratum
  is closed, and open in `M^K`.
* `TauCeti.connectedComponentIn_fixedPoints_subset_fixedPointsFinrank`: a connected component of
  `M^K` lies in a single stratum.
* `TauCeti.exists_isSmoothEmbedding_fixedPointsFinrank`: each stratum is a smooth embedded
  submanifold of dimension `d`.
* `TauCeti.range_mfderiv_le_tangentInvariants`, `TauCeti.range_mfderiv_eq_tangentInvariants`: its
  tangent spaces are the spaces `V^K`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (the fixed set of a group of isometries via the
  exponential map).
* S. Kobayashi, *Fixed points of isometries*, Nagoya Mathematical Journal 13 (1958), 63–68.
-/

public section

open Bundle Manifold Set MulAction Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {K : Type*} [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]

/-! ### The strata of the fixed set -/

section Strata

variable [ContMDiffConstSMul I ∞ K M]

variable (I K) in
/-- The tangent vectors at `x` fixed by the differential at `x` of every element of the stabilizer
of `x`, for a group acting by smooth maps: the invariants of the tangent representation. -/
abbrev tangentInvariants (x : M) : Submodule ℝ (TangentSpace I x) :=
  (tangentRepresentation fun g (_ : g ∈ stabilizer K x) ↦
    (contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt
      (by simp)).toRepresentation.invariants

/-- At a point fixed by the whole group, the invariant tangent vectors are those fixed by the
differential of every group element. -/
theorem mem_tangentInvariants_iff {x : M} (hx : x ∈ fixedPoints K M) {v : TangentSpace I x} :
    v ∈ tangentInvariants I K x ↔ ∀ k : K, mfderiv I I (k • ·) x v = v :=
  mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints _ hx

variable (I K M) in
/-- The **stratum of dimension `d`** of the fixed set: the fixed points `p` at which the tangent
vectors fixed by every differential `d(k •)_p` form a subspace of dimension `d`. -/
def fixedPointsFinrank (d : ℕ) : Set M :=
  {p | p ∈ fixedPoints K M ∧ Module.finrank ℝ (tangentInvariants I K p) = d}

@[simp]
theorem mem_fixedPointsFinrank_iff {d : ℕ} {p : M} :
    p ∈ fixedPointsFinrank I K M d ↔
      p ∈ fixedPoints K M ∧ Module.finrank ℝ (tangentInvariants I K p) = d :=
  Iff.rfl

theorem fixedPointsFinrank_subset_fixedPoints (d : ℕ) :
    fixedPointsFinrank I K M d ⊆ fixedPoints K M :=
  fun _ hp ↦ hp.1

/-- Every fixed point lies in the stratum of the dimension of its invariant tangent vectors. -/
theorem iUnion_fixedPointsFinrank : ⋃ d, fixedPointsFinrank I K M d = fixedPoints K M :=
  subset_antisymm (iUnion_subset fixedPointsFinrank_subset_fixedPoints)
    fun _ hp ↦ mem_iUnion.2 ⟨_, hp, rfl⟩

/-- Strata of different dimensions are disjoint. -/
theorem disjoint_fixedPointsFinrank {d d' : ℕ} (h : d ≠ d') :
    Disjoint (fixedPointsFinrank I K M d) (fixedPointsFinrank I K M d') :=
  disjoint_left.2 fun _ hp hp' ↦ h (hp.2.symm.trans hp'.2)

/-- The differential of a map into the fixed set takes values in the invariant tangent vectors. -/
theorem range_mfderiv_le_tangentInvariants {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] {f : N → M} (hf : ∀ y, f y ∈ fixedPoints K M) (y : N) :
    LinearMap.range (mfderiv J I f y).toLinearMap ≤ tangentInvariants I K (f y) := by
  by_cases hfy : MDifferentiableAt J I f y
  swap
  · simp [mfderiv_zero_of_not_mdifferentiableAt hfy]
  rintro _ ⟨u, rfl⟩
  refine (mem_tangentInvariants_iff (hf y)).2 fun k ↦ ?_
  have hk : MDifferentiableAt I I (k • ·) (f y) :=
    (contMDiff_const_smul (I := I) (n := ∞) k).mdifferentiableAt (by simp)
  have hcomp : (k • ·) ∘ f = f := funext fun z ↦ hf z k
  have h := mfderiv_comp y hk hfy
  rw [hcomp] at h
  exact (DFunLike.congr_fun h u).symm

/-- **The tangent spaces of a stratum.** An immersion of a manifold of dimension `d` into the
stratum of dimension `d` of the fixed set has, as tangent images, the invariant tangent vectors. -/
theorem range_mfderiv_eq_tangentInvariants [FiniteDimensional ℝ E] {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] {d : ℕ} {f : N → M}
    (hf : ∀ y, f y ∈ fixedPointsFinrank I K M d) (hE' : Module.finrank ℝ E' = d) {y : N}
    (hinj : Function.Injective (mfderiv J I f y)) :
    LinearMap.range (mfderiv J I f y).toLinearMap = tangentInvariants I K (f y) := by
  have : FiniteDimensional ℝ E' := FiniteDimensional.of_injective (mfderiv J I f y).toLinearMap hinj
  refine Submodule.eq_of_le_of_finrank_eq
    (range_mfderiv_le_tangentInvariants (fun z ↦ (hf z).1) y) ?_
  rw [LinearMap.finrank_range_of_inj hinj, (hf y).2]
  exact hE'

end Strata

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M] [ContMDiffConstSMul I ∞ K M]

/-! ### Groups acting by isometries -/

section Isometry

variable {p : M} {U : Set (TangentSpace I p)} {w : TangentSpace I p}
  (hK : ∀ (k : K) (x : M) (u v : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x v) = inner ℝ u v)

include hK

/-- **The exponential map intertwines differentials at fixed points.** Let `k` act by an isometry
fixing `p` and a tangent vector `w` at `p`. Then the differential `D` of `exp_p` at `w` satisfies
`d(k •)_q ∘ D = D ∘ d(k •)_p` at `q = exp_p w`. -/
theorem mfderiv_smul_mfderiv_riemannianExp (k : K) (hkp : k • p = p)
    (hkw : mfderiv I I (k • ·) p w = w) (v : TangentSpace I p) :
    mfderiv I I (k • ·) (riemannianExp I M p w)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w v) =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w (mfderiv I I (k • ·) p v) := by
  by_cases hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w
  swap
  · -- Both sides vanish: the differential of `exp_p` at `w` is zero.
    rw [mfderiv_zero_of_not_mdifferentiableAt hexp]
    exact map_zero (mfderiv I I (k • ·) (riemannianExp I M p w))
  have hk : MDifferentiableAt I I (k • ·) (riemannianExp I M p w) :=
    (contMDiff_const_smul (I := I) (n := ∞) k).mdifferentiableAt (by simp)
  -- `d(k •)_p` as an endomorphism of `T_p M`: as `k` fixes `p`, the two tangent spaces agree.
  let A : TangentSpace I p →L[ℝ] TangentSpace I p := mfderiv I I (k • ·) p
  -- Naturality of the exponential map: `k • exp_p v = exp_p (d(k •)_p v)` for every `v`.
  have hfun : (k • ·) ∘ riemannianExp I M p = riemannianExp I M p ∘ A := by
    ext v
    exact (riemannianExp_mfderiv_smul_of_smul_eq (hK k) hkp v).symm
  have hAw : A w = w := hkw
  have h₁ := mfderiv_comp (I' := I) w hk hexp
  have hA : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ, TangentSpace I p) A w :=
    (A.contMDiff (n := ∞)).mdifferentiableAt (by simp)
  have hdA : mfderiv 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ, TangentSpace I p) A w = A := by
    rw [mfderiv_eq_fderiv, A.fderiv]
    rfl
  have h₂ := mfderiv_comp_of_eq hexp hA hAw
  have h : mfderiv 𝓘(ℝ, TangentSpace I p) I ((k • ·) ∘ riemannianExp I M p) w =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p ∘ A) w :=
    by rw [hfun]
  rw [h₁, h₂, hdA] at h
  have hv := DFunLike.congr_fun h v
  rwa [hAw] at hv

namespace Manifold.IsNormalDomain

/-- **The invariant tangent vectors along the exponential image of a fixed vector.** For a group
acting by isometries fixing `p`, and a vector `w` of a normal domain at `p` fixed by every
differential `d(k •)_p`, the tangent vectors at `exp_p w` fixed by every differential form a
subspace of the same dimension as those at `p`. -/
theorem finrank_tangentInvariants_riemannianExp (hU : IsNormalDomain I M p U)
    (hp : p ∈ fixedPoints K M) (hwU : w ∈ U) (hw : ∀ k : K, mfderiv I I (k • ·) p w = w) :
    Module.finrank ℝ (tangentInvariants I K (riemannianExp I M p w)) =
      Module.finrank ℝ (tangentInvariants I K p) := by
  have hq : riemannianExp I M p w ∈ fixedPoints K M := riemannianExp_mem_fixedPoints hK hp hw
  obtain ⟨D, hD⟩ := (hU.isLocalDiffeomorphOn ⟨w, hwU⟩).isInvertible_mfderiv (by simp)
  have hDf : ⇑D = ⇑(mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w) :=
    congrArg DFunLike.coe hD
  -- The differential of `exp_p` at `w`, as a linear isomorphism `T_p M ≃ T_q M` of the tangent
  -- spaces with their own module structures.
  let De : TangentSpace I p ≃ₗ[ℝ] TangentSpace I (riemannianExp I M p w) := D.toLinearEquiv
  have hDe (v : TangentSpace I p) :
      De v = mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w v := congrFun hDf v
  -- `De` carries the invariant vectors at `p` onto those at `exp_p w`.
  have hmap : (tangentInvariants I K (riemannianExp I M p w)).comap De.toLinearMap =
      tangentInvariants I K p := by
    ext v
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, mem_tangentInvariants_iff hq,
      mem_tangentInvariants_iff hp]
    refine forall_congr' fun k ↦ ?_
    rw [hDe, mfderiv_smul_mfderiv_riemannianExp hK k (hp k) (hw k)]
    exact ⟨fun h ↦ De.injective ((hDe _).trans (h.trans (hDe v).symm)),
      fun h ↦ (hDe _).symm.trans ((congrArg De h).trans (hDe v))⟩
  rw [← hmap, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

end Manifold.IsNormalDomain

/-- **The dimension of the invariant tangent vectors is locally constant along the fixed set.** -/
theorem eventually_finrank_tangentInvariants_eq (p : M) :
    ∀ᶠ q in 𝓝 p, q ∈ fixedPoints K M →
      Module.finrank ℝ (tangentInvariants I K q) = Module.finrank ℝ (tangentInvariants I K p) := by
  have : ContinuousConstSMul K M := ⟨fun k ↦ (contMDiff_const_smul (I := I) (n := ∞) k).continuous⟩
  by_cases hp : p ∈ fixedPoints K M
  swap
  · -- Away from the closed fixed set the statement is vacuous.
    filter_upwards [isClosed_fixedPoints_of_continuousConstSMul.isOpen_compl.mem_nhds hp]
      with q hq hqK using absurd hqK hq
  obtain ⟨r, -, hU⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  filter_upwards [hU.image_mem_nhds] with q ⟨w, hw, hwq⟩ hq
  subst hwq
  exact hU.finrank_tangentInvariants_riemannianExp hK hp hw
    ((hU.riemannianExp_mem_fixedPoints_iff_of_mem_ball hK hp hw).1 hq)

/-- **A stratum of the fixed set is open in the fixed set.** Near a point of the stratum of
dimension `d`, every fixed point lies in that stratum. -/
theorem eventually_mem_fixedPointsFinrank {d : ℕ} (hp : p ∈ fixedPointsFinrank I K M d) :
    ∀ᶠ q in 𝓝 p, q ∈ fixedPoints K M → q ∈ fixedPointsFinrank I K M d := by
  filter_upwards [eventually_finrank_tangentInvariants_eq hK p] with q hq hqK
  exact ⟨hqK, (hq hqK).trans hp.2⟩

/-- **A stratum of the fixed set is closed.** -/
theorem isClosed_fixedPointsFinrank (d : ℕ) : IsClosed (fixedPointsFinrank I K M d) := by
  have : ContinuousConstSMul K M := ⟨fun k ↦ (contMDiff_const_smul (I := I) (n := ∞) k).continuous⟩
  refine isClosed_iff_frequently.2 fun p hp ↦ ?_
  have hpK : p ∈ fixedPoints K M :=
    isClosed_fixedPoints_of_continuousConstSMul.mem_of_frequently_of_tendsto
      (hp.mono fun _ hq ↦ hq.1) tendsto_id
  obtain ⟨q, hq, hqd⟩ := ((eventually_finrank_tangentInvariants_eq hK p).and_frequently hp).exists
  exact ⟨hpK, (hq hqd.1).symm.trans hqd.2⟩

/-- **A connected component of the fixed set lies in a single stratum**, that of the dimension of
the invariant tangent vectors at any of its points: each stratum is closed, and open in the fixed
set. -/
theorem connectedComponentIn_fixedPoints_subset_fixedPointsFinrank (p : M) :
    connectedComponentIn (fixedPoints K M) p ⊆
      fixedPointsFinrank I K M (Module.finrank ℝ (tangentInvariants I K p)) := by
  by_cases hp : p ∈ fixedPoints K M
  swap
  · simp [connectedComponentIn_eq_empty hp]
  have hpd : p ∈ fixedPointsFinrank I K M (Module.finrank ℝ (tangentInvariants I K p)) :=
    ⟨hp, rfl⟩
  have hclosed := (isClosed_fixedPointsFinrank hK
    (Module.finrank ℝ (tangentInvariants I K p))).preimage
    (continuous_subtype_val (p := (· ∈ fixedPoints K M)))
  have hopen : IsOpen ((↑) ⁻¹' fixedPointsFinrank I K M
      (Module.finrank ℝ (tangentInvariants I K p)) : Set (fixedPoints K M)) := by
    refine isOpen_iff_eventually.2 fun x hx ↦ ?_
    filter_upwards [(continuous_subtype_val.tendsto x).eventually
      (eventually_mem_fixedPointsFinrank hK hx)] with y hy
    exact hy y.2
  rw [connectedComponentIn_eq_image hp]
  rintro _ ⟨x, hx, rfl⟩
  exact (IsClopen.connectedComponent_subset ⟨hclosed, hopen⟩ (x := ⟨p, hp⟩) hpd) hx

/-- **A stratum of the fixed set is an embedded submanifold.** For a group acting by isometries,
the fixed points at which the invariant tangent vectors form a subspace of dimension `d` make up a
smooth manifold modelled on any `d`-dimensional subspace `L` of the model space, whose inclusion
into `M` is a smooth embedding. -/
theorem exists_isSmoothEmbedding_fixedPointsFinrank {d : ℕ} {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L (fixedPointsFinrank I K M d), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (fixedPointsFinrank I K M d) ∧
        IsSmoothEmbedding 𝓘(ℝ, L) I ∞ (Subtype.val : fixedPointsFinrank I K M d → M) := by
  refine exists_isSmoothEmbedding_of_finrankSubspaceCharts (by simp) fun y hy ↦ ?_
  obtain ⟨r, -, hU⟩ := exists_isNormalDomain_ball (I := I) (M := M) y
  let φ := hU.toPartialDiffeomorph.symm
  -- The identity of the model space, from the normed structure of `T_y M` to that of `E`.
  let B : TangentSpace I y ≃L[ℝ] E := ContinuousLinearEquiv.refl ℝ E
  have hφs : φ.source = riemannianExp I M y '' Metric.ball 0 r := by
    simp [φ, PartialDiffeomorph.symm_toPartialEquiv]
  have hφ (z : M) (hz : z ∈ φ.source) : ∃ v ∈ Metric.ball (0 : TangentSpace I y) r,
      riemannianExp I M y v = z ∧ φ z = v := by
    rw [hφs] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact ⟨v, hv, rfl, by
      simpa [φ, PartialDiffeomorph.symm_toPartialEquiv] using hU.riemannianLog_riemannianExp hv⟩
  refine ⟨φ.toOpenPartialHomeomorph, tangentInvariants I K y, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_,
    fun z hz ↦ ?_, hy.2.trans hL.symm⟩
  · simpa [hφs] using hU.self_mem_image
  · exact B.contDiff.contMDiff.contMDiffAt.comp z
      ((φ.contMDiffOn z hz).contMDiffAt (φ.open_source.mem_nhds hz))
  · exact ((φ.symm.contMDiffOn (B.symm z) hz).contMDiffAt
      (φ.symm.open_source.mem_nhds hz)).comp z B.symm.contDiff.contMDiff.contMDiffAt
  · obtain ⟨v, hv, rfl, hφv⟩ := hφ z hz
    -- Near `y`, the stratum is the fixed set, which `φ` flattens onto the invariant vectors.
    have key : riemannianExp I M y v ∈ fixedPointsFinrank I K M d ↔
        ∀ k : K, mfderiv I I (k • ·) y v = v :=
      ⟨fun h ↦ (hU.riemannianExp_mem_fixedPoints_iff_of_mem_ball hK hy.1 hv).1 h.1,
        fun h ↦ ⟨riemannianExp_mem_fixedPoints hK hy.1 h,
          (hU.finrank_tangentInvariants_riemannianExp hK hy.1 hv h).trans hy.2⟩⟩
    refine key.trans ((mem_tangentInvariants_iff hy.1).symm.trans ?_)
    exact Iff.of_eq (congrArg (· ∈ tangentInvariants I K y) hφv.symm)

end Isometry

end TauCeti
