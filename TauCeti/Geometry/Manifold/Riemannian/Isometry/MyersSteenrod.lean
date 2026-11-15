/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Radial
import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
import TauCeti.Analysis.InnerProductSpace.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Distance
import TauCeti.Topology.EMetricSpace.Component

/-!
# Distance-preserving maps between Riemannian manifolds are smooth

Let `M` and `N` be finite-dimensional Riemannian manifolds without boundary whose extended
distances are their Riemannian distances, with `N` complete, and let `f : M → N` preserve these
distances. This file proves the theorem of Myers and Steenrod that `f` is smooth and that its
differential preserves the Riemannian inner products, so that a bijective such map is a smooth
Riemannian isometry. The manifolds need not be connected: points in different components are at
infinite distance.

Fix `p : M`. On a small normal ball at `p`, the radial map `A v = log_{f p} (f (exp_p v))`
preserves norms and is homogeneous along rays (`Isometry.norm_riemannianLog_apply_riemannianExp`,
`Isometry.riemannianLog_apply_riemannianExp_smul`). It also preserves distances: near the origin
the exponential maps at `p` and at `f p` distort distances by a factor as close to one as we like
(`TauCeti.Manifold.exists_isNormalDomain_ball_dist_riemannianExp_bounds`), and rescaling a pair of
vectors along their rays towards the origin turns this into an exact equality. Hence `A` preserves
inner products, and since the ball spans `T_p M` it agrees there with a linear isometry `L`
(`TauCeti.exists_linearIsometry_eqOn_of_inner_eq`). Thus `f = exp_{f p} ∘ L ∘ log_p` near `p`,
which is smooth with differential `L` at `p`.

The normal-coordinate steps use the metric form of the radial lemmas of `Isometry/Radial.lean`, so
they are stated for metric spaces, where all distances are finite. Smoothness and differentials
are local, so the main theorems pass to extended distances by restricting `f` to the open
finite-distance components `Metric.eball p ∞` and `Metric.eball (f p) ∞`, which are metric spaces
and carry the restricted Riemannian metrics.

The converse, that a smooth Riemannian isometry preserves the Riemannian distance, is the
`IsometryClass` instance on `TauCeti.RiemannianIsometry`.

## Main results

* `Isometry.norm_sub_riemannianLog_apply_riemannianExp`: the radial map preserves distances.
* `Isometry.exists_linearIsometry_apply_riemannianExp`: in normal coordinates at `p` and at `f p`,
  a distance-preserving map is a linear isometry, `f (exp_p v) = exp_{f p} (L v)`.
* `Isometry.contMDiff`: a distance-preserving map is smooth.
* `Isometry.inner_mfderiv`: the differential of a distance-preserving map preserves inner products.
* `IsometryEquiv.toRiemannianIsometry`: a bijective distance-preserving map is a smooth Riemannian
  isometry. With the `IsometryClass` coercion back to `M ≃ᵢ N` it is a bijection
  (`IsometryEquiv.toIsometryEquiv_toRiemannianIsometry`,
  `TauCeti.RiemannianIsometry.toRiemannianIsometry_toIsometryEquiv`).
* `TauCeti.RiemannianIsometry.isometryEquivMulEquiv`: on a complete manifold, the group of smooth
  Riemannian isometries is isomorphic to the group of isometries of the Riemannian distance.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. 40 (1939), 400–416.
* R. S. Palais, *On the differentiability of isometries*, Proc. Amer. Math. Soc. 8 (1957),
  805–807.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
-/

public section

open Bundle Filter Manifold Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Isometry

section Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

variable {f : M → N} {p : M} {U : Set (TangentSpace J (f p))} {r : ℝ} {v w : TangentSpace I p}

/-- Let the tangent ball of radius `r` in `T_p M` be a normal domain at `p`, and let the tangent
ball of radius `r` in `T_{f p} N` lie in a normal domain `U` at `f p`. For `v` in the first ball,
the exponential map at `f p` recovers `f (exp_p v)` from its logarithm. -/
private theorem riemannianExp_riemannianLog_apply_riemannianExp (hf : Isometry f)
    (hp : IsNormalDomain I M p (Metric.ball 0 r)) (hq : IsNormalDomain J N (f p) U)
    (hU : Metric.ball 0 r ⊆ U) (hv : v ∈ Metric.ball 0 r) :
    riemannianExp J N (f p) (riemannianLog J N (f p) U (f (riemannianExp I M p v))) =
      f (riemannianExp I M p v) := by
  simpa using (hf.apply_riemannianExp_smul hq hU
    (hp.dist_riemannianExp_eq_of_mem_ball subset_rfl hv).ge (mem_ball_zero_iff.1 hv)
    (t := 1) ⟨zero_le_one, le_rfl⟩).symm

/-- For every `c > 1`, the radial map `v ↦ log_{f p} (f (exp_p v))` distorts the distance between
two vectors of a normal ball by at most the factor `c * c`. The vectors are first rescaled
towards the origin, where both exponential maps distort distances by at most `c`. -/
private theorem norm_sub_riemannianLog_apply_riemannianExp_le_mul (hf : Isometry f)
    (hp : IsNormalDomain I M p (Metric.ball 0 r)) (hq : IsNormalDomain J N (f p) U)
    (hU : Metric.ball 0 r ⊆ U) (hv : v ∈ Metric.ball 0 r) (hw : w ∈ Metric.ball 0 r)
    {c : ℝ} (hc : 1 < c) :
    ‖riemannianLog J N (f p) U (f (riemannianExp I M p v)) -
        riemannianLog J N (f p) U (f (riemannianExp I M p w))‖ ≤ c * c * ‖v - w‖ ∧
      ‖v - w‖ ≤ c * c * ‖riemannianLog J N (f p) U (f (riemannianExp I M p v)) -
        riemannianLog J N (f p) U (f (riemannianExp I M p w))‖ := by
  set A : TangentSpace I p → TangentSpace J (f p) :=
    fun u ↦ riemannianLog J N (f p) U (f (riemannianExp I M p u))
  have hmin {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 r) :
      ‖u‖ ≤ dist p (riemannianExp I M p u) :=
    (hp.dist_riemannianExp_eq_of_mem_ball subset_rfl hu).ge
  obtain ⟨ρ₁, hρ₁, -, h₁⟩ := exists_isNormalDomain_ball_dist_riemannianExp_bounds (I := I) p hc
  obtain ⟨ρ₂, hρ₂, -, h₂⟩ := exists_isNormalDomain_ball_dist_riemannianExp_bounds (I := J) (f p) hc
  -- A parameter `t ∈ (0, 1]` putting `t • v` and `t • w` in the tangent balls of radius `ρ₁, ρ₂`.
  have hsmall (u : TangentSpace I p) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), t • u ∈ Metric.ball (0 : TangentSpace I p) (min ρ₁ ρ₂) :=
    nhdsWithin_le_nhds <| (Continuous.tendsto (continuous_id.smul continuous_const) 0).eventually
      (Metric.isOpen_ball.mem_nhds (by simpa using lt_min hρ₁ hρ₂))
  obtain ⟨t, ⟨⟨htv, htw⟩, ht1⟩, ht0⟩ := (((hsmall v).and (hsmall w)).and
    (nhdsWithin_le_nhds (Iic_mem_nhds zero_lt_one))).and self_mem_nhdsWithin |>.exists
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht0, ht1⟩
  have hsmul_mem {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 r) : t • u ∈ Metric.ball 0 r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg u) ht.2).trans_lt (mem_ball_zero_iff.1 hu)
  have hnorm {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 r) : ‖A u‖ = ‖u‖ :=
    hf.norm_riemannianLog_apply_riemannianExp hq hU (hmin hu) (mem_ball_zero_iff.1 hu)
  have hsmul {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 r) : A (t • u) = t • A u :=
    hf.riemannianLog_apply_riemannianExp_smul hq hU (hmin hu) (mem_ball_zero_iff.1 hu) ht
  have hexp {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 r) :
      riemannianExp J N (f p) (A u) = f (riemannianExp I M p u) :=
    riemannianExp_riemannianLog_apply_riemannianExp hf hp hq hU hu
  have hball₂ {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 r)
      (hut : t • u ∈ Metric.ball 0 (min ρ₁ ρ₂)) : A (t • u) ∈ Metric.ball 0 ρ₂ := by
    rw [mem_ball_zero_iff, hnorm (hsmul_mem hu)]
    exact (mem_ball_zero_iff.1 hut).trans_le (min_le_right _ _)
  -- `f` identifies the distance of `exp_p (t • v)` and `exp_p (t • w)` with that of their images.
  have hd : dist (riemannianExp J N (f p) (A (t • v))) (riemannianExp J N (f p) (A (t • w))) =
      dist (riemannianExp I M p (t • v)) (riemannianExp I M p (t • w)) := by
    rw [hexp (hsmul_mem hv), hexp (hsmul_mem hw), hf.dist_eq]
  have hN := h₂ _ (hball₂ hv htv) _ (hball₂ hw htw)
  have hM := h₁ _ (Metric.ball_subset_ball (min_le_left _ _) htv) _
    (Metric.ball_subset_ball (min_le_left _ _) htw)
  rw [hd, hsmul hv, hsmul hw] at hN
  -- Rescaling by `t ≥ 0` multiplies both differences by `t`.
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.1] at hN hM
  constructor
  · refine le_of_mul_le_mul_left ?_ ht0
    nlinarith [hN.1, hM.2]
  · refine le_of_mul_le_mul_left ?_ ht0
    nlinarith [hN.2, hM.1]

/-- **A distance-preserving map preserves distances in normal coordinates.** Let `f` preserve
distances into a complete manifold, let the tangent ball of radius `r` in `T_p M` be a normal
domain at `p`, and let the tangent ball of radius `r` in `T_{f p} N` lie in a normal domain `U` at
`f p`. Then the radial map `v ↦ log_{f p} (f (exp_p v))` preserves the distances between vectors
of the first ball. As for the radial lemmas this rests on, `M` and `N` are metric spaces. -/
theorem norm_sub_riemannianLog_apply_riemannianExp (hf : Isometry f)
    (hp : IsNormalDomain I M p (Metric.ball 0 r)) (hq : IsNormalDomain J N (f p) U)
    (hU : Metric.ball 0 r ⊆ U) (hv : v ∈ Metric.ball 0 r) (hw : w ∈ Metric.ball 0 r) :
    ‖riemannianLog J N (f p) U (f (riemannianExp I M p v)) -
        riemannianLog J N (f p) U (f (riemannianExp I M p w))‖ = ‖v - w‖ := by
  have hlim (y : ℝ) : Tendsto (fun c : ℝ ↦ c * c * y) (𝓝[>] 1) (𝓝 y) := by
    have h : Tendsto (fun c : ℝ ↦ c * c * y) (𝓝 1) (𝓝 (1 * 1 * y)) :=
      Continuous.tendsto (by fun_prop) 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have key {c : ℝ} (hc : 1 < c) :=
    norm_sub_riemannianLog_apply_riemannianExp_le_mul hf hp hq hU hv hw hc
  exact le_antisymm (ge_of_tendsto (hlim _) (eventually_nhdsWithin_of_forall fun c hc ↦ (key hc).1))
    (ge_of_tendsto (hlim _) (eventually_nhdsWithin_of_forall fun c hc ↦ (key hc).2))

variable (I J) in
/-- **A distance-preserving map is a linear isometry in normal coordinates.** If `f` preserves
distances into a complete manifold, then there are a radius `r > 0`, for which the tangent balls
of radius `r` at `p` and at `f p` are normal domains, and a linear isometry `L : T_p M → T_{f p} N`
such that `f (exp_p v) = exp_{f p} (L v)` for every `v` in the tangent ball of radius `r`. As for
the radial lemmas this rests on, `M` and `N` are metric spaces. -/
theorem exists_linearIsometry_apply_riemannianExp (hf : Isometry f) (p : M) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      IsNormalDomain J N (f p) (Metric.ball 0 r) ∧
      ∃ L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p),
        ∀ v ∈ Metric.ball (0 : TangentSpace I p) r,
          f (riemannianExp I M p v) = riemannianExp J N (f p) (L v) := by
  obtain ⟨R₁, hR₁, hp⟩ := exists_isNormalDomain_ball (I := I) p
  obtain ⟨R₂, hR₂, hq⟩ := exists_isNormalDomain_ball (I := J) (f p)
  set r := min R₁ R₂
  have hr : 0 < r := lt_min hR₁ hR₂
  have hp' := hp.ball (Metric.ball_subset_ball (min_le_left _ _)) hr
  have hU : Metric.ball (0 : TangentSpace J (f p)) r ⊆ Metric.ball 0 R₂ :=
    Metric.ball_subset_ball (min_le_right _ _)
  -- The radial map `A v = log_{f p} (f (exp_p v))` fixes the origin and preserves distances on
  -- the ball of radius `r`, hence inner products.
  set A : TangentSpace I p → TangentSpace J (f p) :=
    fun v ↦ riemannianLog J N (f p) (Metric.ball 0 R₂) (f (riemannianExp I M p v))
  have hinner {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 r) {w : TangentSpace I p}
      (hw : w ∈ Metric.ball 0 r) : inner ℝ (A v) (A w) = inner ℝ v w :=
    TauCeti.real_inner_map_map_of_dist_map_eq (Metric.mem_ball_self hr)
      (by simp [A, hq.riemannianLog_self])
      (fun z hz u hu ↦ by
        simpa only [dist_eq_norm] using
          hf.norm_sub_riemannianLog_apply_riemannianExp hp' hq hU hz hu) hv hw
  -- The ball spans `T_p M`, so `A` agrees on it with a linear isometry.
  have hspan : Submodule.span ℝ (Metric.ball (0 : TangentSpace I p) r) = ⊤ :=
    ((absorbent_nhds_zero (Metric.ball_mem_nhds 0 hr)).mono Submodule.subset_span).submodule_eq_top
  obtain ⟨L, hL⟩ := TauCeti.exists_linearIsometry_eqOn_of_inner_eq hspan
    fun v hv w hw ↦ hinner hv hw
  refine ⟨r, hr, hp', hq.ball hU hr, L, fun v hv ↦ ?_⟩
  rw [← hL hv]
  exact (riemannianExp_riemannianLog_apply_riemannianExp hf hp' hq hU hv).symm

variable (I J) in
/-- In normal coordinates, a distance-preserving map is a linear isometry on a whole normal
neighbourhood: `f = exp_{f p} ∘ L ∘ log_p` near `p`. -/
private theorem eventuallyEq_riemannianExp_linearIsometry_riemannianLog (hf : Isometry f)
    (p : M) : ∃ r, IsNormalDomain I M p (Metric.ball 0 r) ∧
      ∃ L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p), f =ᶠ[𝓝 p]
        fun x ↦ riemannianExp J N (f p) (L (riemannianLog I M p (Metric.ball 0 r) x)) := by
  obtain ⟨r, -, hp, -, L, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp I J p
  refine ⟨r, hp, L, ?_⟩
  filter_upwards [hp.image_mem_nhds] with x hx
  rw [← hL _ (riemannianLog_mem hx), riemannianExp_riemannianLog hx]

/-- A distance-preserving map between Riemannian manifolds with finite distances is smooth.
`Isometry.contMDiff` extends this to extended distances. -/
private theorem contMDiff_of_metricSpace (hf : Isometry f) : ContMDiff I J ∞ f := by
  intro p
  obtain ⟨r, hp, L, heq⟩ := eventuallyEq_riemannianExp_linearIsometry_riemannianLog I J hf p
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have hlog : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ (riemannianLog I M p (Metric.ball 0 r)) p :=
    hp.contMDiffOn_riemannianLog.contMDiffAt hp.image_mem_nhds
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace J (f p)) J ∞ (riemannianExp J N (f p))
      (L (riemannianLog I M p (Metric.ball 0 r) p)) := by
    rw [hp.riemannianLog_self, map_zero]
    exact contMDiffAt_riemannianExp (zero_mem_expDomain _)
  exact hexp.comp p (L.toContinuousLinearMap.contMDiff.contMDiffAt.comp p hlog)

/-- The differential of a distance-preserving map between Riemannian manifolds with finite
distances preserves inner products. `Isometry.inner_mfderiv` extends this to extended
distances. -/
private theorem inner_mfderiv_of_metricSpace (hf : Isometry f) (p : M) (v w : TangentSpace I p) :
    inner ℝ (mfderiv I J f p v) (mfderiv I J f p w) = inner ℝ v w := by
  obtain ⟨r, hp, L, heq⟩ := eventuallyEq_riemannianExp_linearIsometry_riemannianLog I J hf p
  -- The differentials of `log_p` at `p` and of `exp_{f p}` at `0` are the canonical
  -- identifications of `T_p M` and `T_{f p} N` with their own tangent spaces.
  have hlog : HasMFDerivAt I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 r)) p
      (NormedSpace.fromTangentSpace
        (riemannianLog I M p (Metric.ball 0 r) p)).symm.toContinuousLinearMap := by
    have h := (hp.mdifferentiableAt_riemannianLog hp.self_mem_image).hasMFDerivAt
    have e : mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 r)) p =
        (NormedSpace.fromTangentSpace
          (riemannianLog I M p (Metric.ball 0 r) p)).symm.toContinuousLinearMap := by
      ext u
      rw [ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace_symm_apply]
      exact hp.mfderiv_riemannianLog_self_apply u
    rwa [e] at h
  have hexp : HasMFDerivAt 𝓘(ℝ, TangentSpace J (f p)) J (riemannianExp J N (f p))
      (L (riemannianLog I M p (Metric.ball 0 r) p))
      (NormedSpace.fromTangentSpace
        (L (riemannianLog I M p (Metric.ball 0 r) p))).toContinuousLinearMap := by
    rw [hp.riemannianLog_self, map_zero]
    exact hasMFDerivAt_riemannianExp_zero (I := J) (f p)
  have hderiv := ((hexp.comp p (L.toContinuousLinearMap.hasMFDerivAt.comp p
    hlog)).congr_of_eventuallyEq_abuse heq).mfderiv
  have happly (u : TangentSpace I p) : mfderiv I J f p u = L u := by
    -- The composite runs through the tangent spaces of `T_p M` at `log_p p` and of `T_{f p} N` at
    -- `L (log_p p)`, both of which are only definitionally `T_p M` and `T_{f p} N`; this blocks
    -- `ContinuousLinearMap.comp_apply` and the `NormedSpace.fromTangentSpace` evaluation lemmas
    -- syntactically, but both identifications are the identity, so the value is `L u` by
    -- definition.
    rw [hderiv]
    rfl
  rw [happly, happly, L.inner_map_map]

end Metric

section Component

/-! ### Finite-distance components

Distances in a Riemannian manifold may be infinite, between points of different components. The
points at finite distance from `p` form an open submanifold whose distance is finite, so the
results above apply to it, and they transfer back since smoothness and differentials are local.
-/

open TopologicalSpace
open scoped ENNReal TauCeti

/-- The finite-distance component of `p`, as an open subset. -/
private def component {X : Type*} [EMetricSpace X] (p : X) : Opens X :=
  ⟨Metric.eball p ∞, Metric.isOpen_eball⟩

@[simp]
private theorem coe_component {X : Type*} [EMetricSpace X] (p : X) :
    (component p : Set X) = Metric.eball p ∞ :=
  rfl

@[simp]
private theorem mem_component_iff {X : Type*} [EMetricSpace X] {p x : X} :
    x ∈ component p ↔ edist x p < ⊤ := by
  rw [← SetLike.mem_coe, coe_component, Metric.mem_eball]

private theorem mem_component {X : Type*} [EMetricSpace X] (p : X) : p ∈ component p :=
  mem_component_iff.2 (by simp)

/-- The metric of a finite-distance component. It is built with `EMetricSpace.toMetricSpace`
rather than taken from `TauCeti.instMetricSpaceEBallTop`, so that its topology unfolds reducibly
to the subtype topology carrying the charts of the open subset. -/
private instance {X : Type*} [EMetricSpace X] (p : X) : MetricSpace (component p) :=
  EMetricSpace.toMetricSpace fun x y ↦ ((edist_triangle_right (x : X) y p).trans_lt
    (ENNReal.add_lt_top.2 ⟨mem_component_iff.1 x.2, mem_component_iff.1 y.2⟩)).ne

/-- A finite-distance component of a complete space is complete. -/
private instance {X : Type*} [EMetricSpace X] [CompleteSpace X] (p : X) :
    CompleteSpace (component p) :=
  -- The subtype of `component p` is that of `Metric.eball p ∞` (`coe_component`).
  TauCeti.instCompleteSpaceEBallTop p

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- The distance of a finite-distance component is its own Riemannian distance. -/
private instance (p : M) : IsRiemannianManifold I (component p) := by
  refine ⟨fun x y ↦ ((component p).riemannianEDist_open_eq_edist_of_eball_subset x y ?_
    (edist_lt_top x y)).symm⟩
  rw [coe_component, TauCeti.eball_top_eq_of_edist_ne_top (mem_component_iff.1 x.2).ne]

variable {N : Type*} [EMetricSpace N] {f : M → N}

/-- A distance-preserving map restricts to the finite-distance components of `p` and `f p`. -/
private def componentMap (hf : Isometry f) (p : M) : component p → component (f p) :=
  fun x ↦ ⟨f x, by rw [mem_component_iff, hf.edist_eq]; exact mem_component_iff.1 x.2⟩

@[simp]
private theorem coe_componentMap (hf : Isometry f) (p : M) (x : component p) :
    (componentMap hf p x : N) = f x :=
  rfl

private theorem val_comp_componentMap (hf : Isometry f) (p : M) :
    Subtype.val ∘ componentMap hf p = f ∘ Subtype.val :=
  funext (coe_componentMap hf p)

/-- The restriction of a distance-preserving map to finite-distance components preserves
distances. -/
private theorem isometry_componentMap (hf : Isometry f) (p : M) :
    Isometry (componentMap hf p) :=
  fun x y ↦ by simp only [Subtype.edist_eq, coe_componentMap, hf.edist_eq]

end Component

section EMetric

open scoped TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

variable {f : M → N}

/-- **Myers–Steenrod: a distance-preserving map between Riemannian manifolds is smooth.** The
manifolds are finite-dimensional and without boundary, their extended distances are the
Riemannian distances, and the target is complete; no connectedness, completeness, compactness or
surjectivity is needed on the source. -/
theorem contMDiff (hf : Isometry f) : ContMDiff I J ∞ f := by
  intro p
  have h : ContMDiffAt I J ∞ (Subtype.val ∘ componentMap hf p)
      (⟨p, mem_component p⟩ : component p) :=
    (contMDiff_subtype_val.comp (isometry_componentMap hf p).contMDiff_of_metricSpace) _
  rw [val_comp_componentMap] at h
  exact contMDiffAt_subtype_iff.1 h

/-- **The differential of a distance-preserving map preserves inner products.** -/
theorem inner_mfderiv (hf : Isometry f) (p : M) (v w : TangentSpace I p) :
    inner ℝ (mfderiv I J f p v) (mfderiv I J f p w) = inner ℝ v w := by
  set x : component p := ⟨p, mem_component p⟩
  have hcomp := val_comp_componentMap hf p
  set e := tangentSpaceOpenEquiv (I := I) x
  have h := (isometry_componentMap hf p).inner_mfderiv_of_metricSpace (I := I) (J := J) x
    (e.symm v) (e.symm w)
  -- Inner products on the components are those of `M` and `N`, and the differential of the
  -- restriction of `f` is that of `f`.
  rw [inner_tangentSpace_open (I := J), inner_tangentSpace_open (I := I),
    tangentSpaceOpenEquiv_mfderiv_apply hcomp, tangentSpaceOpenEquiv_mfderiv_apply hcomp,
    e.apply_symm_apply, e.apply_symm_apply] at h
  -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
  exact h

/-- The differential of a distance-preserving map preserves norms. -/
theorem norm_mfderiv (hf : Isometry f) (p : M) (v : TangentSpace I p) :
    ‖mfderiv I J f p v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, hf.inner_mfderiv]

end EMetric

end Isometry

namespace IsometryEquiv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ F H') [J.Boundaryless]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

/-- **Myers–Steenrod: a bijective distance-preserving map is a smooth Riemannian isometry.** An
isometry `e : M ≃ᵢ N` of the Riemannian extended distances between finite-dimensional Riemannian
manifolds without boundary, with complete target (equivalently, since `e` transfers completeness,
complete source), is a diffeomorphism whose differential preserves the Riemannian inner
products. -/
def toRiemannianIsometry (e : M ≃ᵢ N) : TauCeti.RiemannianIsometry I J M N :=
  haveI : CompleteSpace M := e.completeSpace
  { toEquiv := e.toEquiv
    contMDiff_toFun := e.isometry.contMDiff
    contMDiff_invFun := e.symm.isometry.contMDiff
    inner_mfderiv' := e.isometry.inner_mfderiv }

/-- The smooth Riemannian isometry underlying a bijective distance-preserving map is that map. -/
@[simp]
theorem coe_toRiemannianIsometry (e : M ≃ᵢ N) : ⇑(e.toRiemannianIsometry I J) = e :=
  (rfl)

/-- The underlying equivalence of `e.toRiemannianIsometry I J` is that of `e`. -/
@[simp]
theorem toEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    (e.toRiemannianIsometry I J).toEquiv = e.toEquiv :=
  (rfl)

/-- The inverse of `e.toRiemannianIsometry I J` is the inverse of `e`. -/
@[simp]
theorem coe_toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    ⇑(e.toRiemannianIsometry I J).symm = e.symm := by
  funext y
  apply e.injective
  rw [apply_symm_apply, ← coe_toRiemannianIsometry I J e,
    TauCeti.RiemannianIsometry.apply_symm_apply]

/-- Forgetting the smooth structure of `e.toRiemannianIsometry I J` recovers `e`. -/
@[simp]
theorem toIsometryEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    ((e.toRiemannianIsometry I J : TauCeti.RiemannianIsometry I J M N) : M ≃ᵢ N) = e := by
  ext x
  simp

/-- The smooth Riemannian isometry of the identity is the identity. -/
@[simp]
theorem toRiemannianIsometry_refl [CompleteSpace M] :
    (IsometryEquiv.refl M).toRiemannianIsometry I I = TauCeti.RiemannianIsometry.refl I M := by
  ext x
  rw [coe_toRiemannianIsometry, TauCeti.RiemannianIsometry.refl_apply]
  rfl

/-- The smooth Riemannian isometry of the inverse is the inverse smooth Riemannian isometry. The
completeness of `M` it needs is transferred from `N` by `e`. -/
@[simp]
theorem toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    haveI : CompleteSpace M := e.completeSpace
    e.symm.toRiemannianIsometry J I = (e.toRiemannianIsometry I J).symm := by
  ext x
  simp

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {H'' : Type*} [TopologicalSpace H''] (K : ModelWithCorners ℝ G H'') [K.Boundaryless]
  {P : Type*} [EMetricSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]
  [IsContMDiffRiemannianBundle K ∞ G (fun z : P ↦ TangentSpace K z)] [IsRiemannianManifold K P]
  [CompleteSpace P]

omit [CompleteSpace N] in
/-- The smooth Riemannian isometry of a composite is the composite of the smooth Riemannian
isometries. The completeness of `N` it needs is transferred from `P` by `e₂`. -/
theorem toRiemannianIsometry_trans (e₁ : M ≃ᵢ N) (e₂ : N ≃ᵢ P) :
    haveI : CompleteSpace N := e₂.completeSpace
    (e₁.trans e₂).toRiemannianIsometry I K =
      (e₁.toRiemannianIsometry I J).trans (e₂.toRiemannianIsometry J K) := by
  ext x
  simp

/-- The smooth Riemannian isometry of the unit of `M ≃ᵢ M` is the unit of `Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_one [CompleteSpace M] :
    (1 : M ≃ᵢ M).toRiemannianIsometry I I = 1 :=
  toRiemannianIsometry_refl I

/-- The smooth Riemannian isometry of a product in `M ≃ᵢ M` is the product in `Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_mul [CompleteSpace M] (e₁ e₂ : M ≃ᵢ M) :
    (e₁ * e₂).toRiemannianIsometry I I =
      e₁.toRiemannianIsometry I I * e₂.toRiemannianIsometry I I :=
  toRiemannianIsometry_trans I I I e₂ e₁

/-- The smooth Riemannian isometry of an inverse in `M ≃ᵢ M` is the inverse in `Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_inv [CompleteSpace M] (e : M ≃ᵢ M) :
    e⁻¹.toRiemannianIsometry I I = (e.toRiemannianIsometry I I)⁻¹ :=
  toRiemannianIsometry_symm I I e

end IsometryEquiv

namespace TauCeti.RiemannianIsometry

section Group

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- The metric equivalence of the unit of `Isom I M` is the unit of `M ≃ᵢ M`. -/
@[simp]
theorem toIsometryEquiv_one : ((1 : Isom I M) : M ≃ᵢ M) = 1 :=
  toIsometryEquiv_refl

/-- The metric equivalence of a product in `Isom I M` is the product in `M ≃ᵢ M`. -/
@[simp]
theorem toIsometryEquiv_mul (Φ Ψ : Isom I M) :
    ((Φ * Ψ : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M) * (Ψ : M ≃ᵢ M) :=
  toIsometryEquiv_trans Ψ Φ

/-- The metric equivalence of an inverse in `Isom I M` is the inverse in `M ≃ᵢ M`. -/
@[simp]
theorem toIsometryEquiv_inv (Φ : Isom I M) :
    ((Φ⁻¹ : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M)⁻¹ :=
  toIsometryEquiv_symm Φ

end Group

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

section Map

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

/-- A smooth Riemannian isometry is recovered from its underlying distance-preserving
bijection. -/
@[simp]
theorem toRiemannianIsometry_toIsometryEquiv (Φ : RiemannianIsometry I J M N) :
    (Φ : M ≃ᵢ N).toRiemannianIsometry I J = Φ := by
  ext x
  simp

end Map

variable (I M) [CompleteSpace M]

/-- **The smooth and the metric isometry groups agree.** On a complete finite-dimensional
Riemannian manifold without boundary, forgetting the smooth structure is a group isomorphism from
the smooth Riemannian isometries onto the isometries of the Riemannian extended distance. -/
def isometryEquivMulEquiv : Isom I M ≃* (M ≃ᵢ M) where
  toFun Φ := Φ
  invFun e := e.toRiemannianIsometry I I
  left_inv := toRiemannianIsometry_toIsometryEquiv
  right_inv := IsometryEquiv.toIsometryEquiv_toRiemannianIsometry I I
  map_mul' := toIsometryEquiv_mul

/-- The isomorphism of isometry groups forgets the smooth structure. -/
@[simp]
theorem isometryEquivMulEquiv_apply (Φ : Isom I M) :
    isometryEquivMulEquiv I M Φ = (Φ : M ≃ᵢ M) :=
  (rfl)

/-- The inverse isomorphism of isometry groups is `IsometryEquiv.toRiemannianIsometry`. -/
@[simp]
theorem isometryEquivMulEquiv_symm_apply (e : M ≃ᵢ M) :
    (isometryEquivMulEquiv I M).symm e = e.toRiemannianIsometry I I :=
  (rfl)

end TauCeti.RiemannianIsometry
