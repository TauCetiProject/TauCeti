/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Radial
import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion

/-!
# Distance-preserving maps between Riemannian manifolds are smooth

Let `f : M → N` preserve the Riemannian distances between Riemannian manifolds without boundary,
with `N` complete. This file proves the theorem of Myers and Steenrod that `f` is smooth and that
its differential preserves the Riemannian inner products, so that a bijective such map is a smooth
Riemannian isometry.

Fix `p : M`. On a small normal ball at `p`, the radial map `A v = log_{f p} (f (exp_p v))`
preserves norms and is homogeneous along rays (`Isometry.norm_riemannianLog_apply_riemannianExp`,
`Isometry.riemannianLog_apply_riemannianExp_smul`). It also preserves distances: near the origin
the exponential maps at `p` and at `f p` distort distances by a factor as close to one as we like
(`TauCeti.Manifold.exists_isNormalDomain_ball_dist_riemannianExp_bounds`), and rescaling a pair of
vectors along their rays towards the origin turns this into an exact equality. Hence `A` preserves
inner products, and since the ball spans `T_p M` it agrees there with a linear isometry `L`
(`TauCeti.exists_linearIsometry_eqOn_of_inner_eq`). Thus `f = exp_{f p} ∘ L ∘ log_p` near `p`,
which is smooth with differential `L` at `p`.

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

/-- On a normal ball at `p` lying in a normal domain `U` at `f p`, the exponential map at `f p`
recovers `f (exp_p v)` from its logarithm. -/
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
  have hscale (x y : TangentSpace J (f p)) : ‖t • x - t • y‖ = t * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.1]
  have hscale' (x y : TangentSpace I p) : ‖t • x - t • y‖ = t * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.1]
  -- `f` identifies the distance of `exp_p (t • v)` and `exp_p (t • w)` with that of their images.
  have hd : dist (riemannianExp J N (f p) (A (t • v))) (riemannianExp J N (f p) (A (t • w))) =
      dist (riemannianExp I M p (t • v)) (riemannianExp I M p (t • w)) := by
    rw [hexp (hsmul_mem hv), hexp (hsmul_mem hw), hf.dist_eq]
  have hN := h₂ _ (hball₂ hv htv) _ (hball₂ hw htw)
  have hM := h₁ _ (Metric.ball_subset_ball (min_le_left _ _) htv) _
    (Metric.ball_subset_ball (min_le_left _ _) htw)
  rw [hd, hsmul hv, hsmul hw, hscale] at hN
  rw [hscale'] at hM
  constructor
  · refine le_of_mul_le_mul_left ?_ ht0
    nlinarith [hN.1, hM.2]
  · refine le_of_mul_le_mul_left ?_ ht0
    nlinarith [hN.2, hM.1]

/-- **A distance-preserving map preserves distances in normal coordinates.** Let `f` preserve
distances into a complete manifold, let the tangent ball of radius `r` be a normal domain at `p`,
and let it lie in a normal domain `U` at `f p`. Then the radial map
`v ↦ log_{f p} (f (exp_p v))` preserves the distances between vectors of that ball. -/
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
such that `f (exp_p v) = exp_{f p} (L v)` for every `v` in the tangent ball of radius `r`. -/
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
  -- The radial map `A v = log_{f p} (f (exp_p v))` preserves norms and distances on the ball of
  -- radius `r`, hence inner products.
  set A : TangentSpace I p → TangentSpace J (f p) :=
    fun v ↦ riemannianLog J N (f p) (Metric.ball 0 R₂) (f (riemannianExp I M p v))
  have hinner {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 r) {w : TangentSpace I p}
      (hw : w ∈ Metric.ball 0 r) : inner ℝ (A v) (A w) = inner ℝ v w := by
    have hnorm {u : TangentSpace I p} (hu : u ∈ Metric.ball 0 r) : ‖A u‖ = ‖u‖ :=
      hf.norm_riemannianLog_apply_riemannianExp hq hU
        (hp'.dist_riemannianExp_eq_of_mem_ball subset_rfl hu).ge (mem_ball_zero_iff.1 hu)
    have hdist : ‖A v - A w‖ = ‖v - w‖ :=
      hf.norm_sub_riemannianLog_apply_riemannianExp hp' hq hU hv hw
    have h₁ := norm_sub_sq_real (A v) (A w)
    have h₂ := norm_sub_sq_real v w
    rw [hdist, hnorm hv, hnorm hw] at h₁
    linarith
  -- The ball spans `T_p M`, so `A` agrees on it with a linear isometry.
  have hspan : Submodule.span ℝ (Metric.ball (0 : TangentSpace I p) r) = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨t, ht, htx⟩ : ∃ t : ℝ, 0 < t ∧ t • x ∈ Metric.ball (0 : TangentSpace I p) r := by
      refine ⟨r / (2 * (‖x‖ + 1)), by positivity, ?_⟩
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity),
        div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg x]
    simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using
      Submodule.smul_mem _ t⁻¹ (Submodule.subset_span htx)
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

/-- **Myers–Steenrod: a distance-preserving map between Riemannian manifolds is smooth.** The
target is complete; no completeness, compactness or surjectivity is needed on the source. -/
theorem contMDiff (hf : Isometry f) : ContMDiff I J ∞ f := by
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

/-- **The differential of a distance-preserving map preserves inner products.** -/
theorem inner_mfderiv (hf : Isometry f) (p : M) (v w : TangentSpace I p) :
    inner ℝ (mfderiv I J f p v) (mfderiv I J f p w) = inner ℝ v w := by
  obtain ⟨r, hp, L, heq⟩ := eventuallyEq_riemannianExp_linearIsometry_riemannianLog I J hf p
  -- The differentials of `log_p` at `p` and of `exp_{f p}` at `0` are the identity.
  have hlog : HasMFDerivAt I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 r)) p
      (ContinuousLinearMap.id ℝ (TangentSpace I p)) := by
    have h := (hp.mdifferentiableAt_riemannianLog hp.self_mem_image).hasMFDerivAt
    have e : mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 r)) p =
        ContinuousLinearMap.id ℝ (TangentSpace I p) := by
      ext u
      exact hp.mfderiv_riemannianLog_self_apply u
    rwa [e] at h
  have hexp : HasMFDerivAt 𝓘(ℝ, TangentSpace J (f p)) J (riemannianExp J N (f p))
      (L (riemannianLog I M p (Metric.ball 0 r) p))
      (ContinuousLinearMap.id ℝ (TangentSpace J (f p))) := by
    rw [hp.riemannianLog_self, map_zero]
    have h := ((contMDiffAt_riemannianExp (I := J) (M := N)
      (zero_mem_expDomain (f p))).mdifferentiableAt (by simp)).hasMFDerivAt
    have e : mfderiv 𝓘(ℝ, TangentSpace J (f p)) J (riemannianExp J N (f p)) 0 =
        ContinuousLinearMap.id ℝ (TangentSpace J (f p)) := by
      ext u
      exact mfderiv_riemannianExp_apply_zero (I := J) (f p) u
    rwa [e] at h
  have hderiv := ((hexp.comp p (L.toContinuousLinearMap.hasMFDerivAt.comp p
    hlog)).congr_of_eventuallyEq_abuse heq).mfderiv
  have happly (u : TangentSpace I p) : mfderiv I J f p u = L u := by
    -- The composite `id ∘ L ∘ id` is typed through the tangent spaces of `T_{f p} N` at
    -- `L (log_p p)` and of `N` at `exp_{f p} (L (log_p p))`, all of which are `F`; these types
    -- block `ContinuousLinearMap.comp_apply` syntactically, but the evaluation is `L u` by
    -- definition of composition.
    rw [hderiv]
    rfl
  rw [happly, happly, L.inner_map_map]

/-- The differential of a distance-preserving map preserves norms. -/
theorem norm_mfderiv (hf : Isometry f) (p : M) (v : TangentSpace I p) :
    ‖mfderiv I J f p v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, hf.inner_mfderiv]

end Isometry

namespace IsometryEquiv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ F H') [J.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

/-- **Myers–Steenrod: a bijective distance-preserving map is a smooth Riemannian isometry.** An
isometry of the Riemannian distances between Riemannian manifolds, one of them complete, is a
diffeomorphism whose differential preserves the Riemannian inner products. -/
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

/-- Forgetting the smooth structure of `e.toRiemannianIsometry I J` recovers `e`. -/
@[simp]
theorem toIsometryEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    ((e.toRiemannianIsometry I J : TauCeti.RiemannianIsometry I J M N) : M ≃ᵢ N) = e := by
  ext x
  simp

end IsometryEquiv

namespace TauCeti.RiemannianIsometry

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

/-- A smooth Riemannian isometry is recovered from its underlying distance-preserving
bijection. -/
@[simp]
theorem toRiemannianIsometry_toIsometryEquiv (Φ : RiemannianIsometry I J M N) :
    (Φ : M ≃ᵢ N).toRiemannianIsometry I J = Φ := by
  ext x
  simp

end TauCeti.RiemannianIsometry
