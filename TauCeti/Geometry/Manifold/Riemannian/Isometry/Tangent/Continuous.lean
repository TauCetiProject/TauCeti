/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Frame
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Smooth
public import TauCeti.Topology.FiberBundle.Separation
public import TauCeti.Topology.MetricSpace.Isometry.Group
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
import TauCeti.Topology.VectorBundle.Smul

/-!
# Continuity of the differentials of isometries

A family of local Riemannian isometries `Φ x : M → N` whose values `Φ x y` depend jointly
continuously on the parameter `x` and the point `y` has differentials depending jointly
continuously on `x` and the tangent vector: `(x, v) ↦ dΦ_x v` is continuous on `X × TM`
(`TauCeti.IsLocalRiemannianIsometry.continuous_tangentMap`). No continuity of the differentials is
assumed; it is forced by the exponential maps. Indeed a local isometry intertwines them, so for a
small `t > 0` and a vector `v` at `p`,
`t • dΦ_p v = log_{Φ p} (Φ (exp_p (t • v)))`, and the logarithm is jointly continuous in both
points on a uniformly normal neighbourhood. One `t` serves for all `(x, v)` near a given one.

For the compact-open topology on the isometries `M ≃ᵢ N` of the Riemannian distances,
evaluation is jointly continuous and every such isometry is a smooth Riemannian
isometry, so the tangent map `(e, v) ↦ de v` is continuous on `(M ≃ᵢ N) × TM`
(`IsometryEquiv.continuous_tangentMap`).

On a compact Riemannian manifold `M`, pick one point and one orthonormal tangent frame in each of
the finitely many connected components. Evaluating an isometry at these points and frames is
injective (`TauCeti.RiemannianIsometry.exists_orthonormalBasis_injective_tangentMap`) and, by the
above, continuous on the compact group `M ≃ᵢ M`. Hence it is a closed embedding of the isometry
group into a finite product of copies of `M` and of the tangent bundle
(`IsometryEquiv.exists_orthonormalBasis_isClosedEmbedding_tangentMap`). This is the frame
evaluation through which the isometry group is studied in the theorem of Myers and Steenrod.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.continuous_tangentMap`: the differentials of a continuous
  family of local Riemannian isometries are jointly continuous in the parameter and the tangent
  vector.
* `IsometryEquiv.continuous_tangentMap`: the tangent map is jointly continuous on the isometries
  of the Riemannian distance and the tangent bundle.
* `IsometryEquiv.exists_orthonormalBasis_isClosedEmbedding_tangentMap`: on a compact Riemannian
  manifold, evaluation on one orthonormal frame in each component is a closed embedding of the
  isometry group.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. 40 (1939), 400–416.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
-/

public section

noncomputable section

open Bundle Manifold Set Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti.IsLocalRiemannianIsometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- Let `W` be an open set of points of `N` at which the tangent ball of radius `r` is a normal
domain. For a continuous family of local isometries `Φ x`, the logarithm at `Φ x p` of
`Φ x (exp_p (t • v))`, as a vector of the tangent bundle, is continuous in `(x, v)` wherever
`Φ x p ∈ W`, `‖t • v‖ < r` and `t • v` lies in the domain of `exp_p`. -/
private theorem continuousAt_totalSpaceMk_riemannianLog_apply_riemannianExp {X : Type*}
    [TopologicalSpace X] {Φ : X → M → N} (hΦi : ∀ x, IsLocalRiemannianIsometry I J (Φ x))
    (hΦ : Continuous fun q : X × M ↦ Φ q.1 q.2) {W : Set N} (hWo : IsOpen W) {r : ℝ}
    (hW : ∀ y ∈ W, IsNormalDomain J N y (Metric.ball 0 r)) (t : ℝ)
    {q₀ : X × TangentBundle I M} (hq₀ : Φ q₀.1 q₀.2.proj ∈ W) (hr : ‖t • q₀.2.snd‖ < r)
    (hexp : t • q₀.2.snd ∈ expDomain I M q₀.2.proj) :
    ContinuousAt (fun q : X × TangentBundle I M ↦ (⟨Φ q.1 q.2.proj,
      riemannianLog J N (Φ q.1 q.2.proj) (Metric.ball 0 r)
        (Φ q.1 (riemannianExp I M q.2.proj (t • q.2.snd)))⟩ : TangentBundle J N)) q₀ := by
  -- The pair `(Φ x p, Φ x (exp_p (t • v)))` is continuous in `(x, v)`.
  have hscale : Continuous fun z : TangentBundle I M ↦ (⟨z.proj, t • z.snd⟩ : TangentBundle I M) :=
    continuous_const.smul_totalSpace continuous_id
  have hexp' : ContinuousAt
      (fun q : X × TangentBundle I M ↦ riemannianExp I M q.2.proj (t • q.2.snd)) q₀ :=
    ContinuousAt.comp (g := fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.snd)
      (f := fun q : X × TangentBundle I M ↦ (⟨q.2.proj, t • q.2.snd⟩ : TangentBundle I M))
      (contMDiffOn_riemannianExp_tangentBundle.continuousOn.continuousAt
        (isOpen_setOfPred_mem_expDomain.mem_nhds hexp))
      (hscale.comp continuous_snd).continuousAt
  have hB : ContinuousAt (fun q : X × TangentBundle I M ↦
      (Φ q.1 q.2.proj, Φ q.1 (riemannianExp I M q.2.proj (t • q.2.snd)))) q₀ :=
    (hΦ.comp (continuous_fst.prodMk ((FiberBundle.continuous_proj E _).comp
      continuous_snd))).continuousAt.prodMk (hΦ.continuousAt.comp (continuousAt_fst.prodMk hexp'))
  -- The logarithm `(y, y') ↦ (y, log_y y')` is continuous at this pair.
  have hP := isOpen_setOf_mem_riemannianExp_image_ball hWo
    (fun y hy ↦ (hW y hy).subset_expDomain) fun y hy ↦ (hW y hy).isLocalDiffeomorphOn
  have hmem : (Φ q₀.1 q₀.2.proj, Φ q₀.1 (riemannianExp I M q₀.2.proj (t • q₀.2.snd))) ∈
      {y : N × N | y.1 ∈ W ∧ y.2 ∈ riemannianExp J N y.1 '' Metric.ball 0 r} := by
    refine ⟨hq₀, mfderiv I J (Φ q₀.1) q₀.2.proj (t • q₀.2.snd), ?_,
      (hΦi q₀.1).riemannianExp_mfderiv_of_mem hexp⟩
    rwa [mem_ball_zero_iff, (hΦi q₀.1).norm_mfderiv]
  exact ContinuousAt.comp (x := q₀) (g := fun y : N × N ↦
      (⟨y.1, riemannianLog J N y.1 (Metric.ball 0 r) y.2⟩ : TangentBundle J N))
    (f := fun q : X × TangentBundle I M ↦
      (Φ q.1 q.2.proj, Φ q.1 (riemannianExp I M q.2.proj (t • q.2.snd))))
    ((contMDiffOn_totalSpaceMk_riemannianLog hWo hW).continuousOn.continuousAt
      (hP.mem_nhds hmem)) hB

/-- **The differentials of a continuous family of local isometries vary continuously.** Let `Φ x`
be local Riemannian isometries depending on a parameter `x` such that `Φ x y` is jointly
continuous in `x` and `y`. Then the tangent vector `dΦ_x v` is jointly continuous in `x` and the
tangent vector `v`. -/
theorem continuous_tangentMap {X : Type*} [TopologicalSpace X] {Φ : X → M → N}
    (hΦi : ∀ x, IsLocalRiemannianIsometry I J (Φ x))
    (hΦ : Continuous fun q : X × M ↦ Φ q.1 q.2) :
    Continuous fun q : X × TangentBundle I M ↦ tangentMap I J (Φ q.1) q.2 := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  obtain ⟨x₀, ⟨p₀, v₀⟩⟩ := q₀
  -- A uniformly normal neighbourhood `W` of `Φ x₀ p₀` with radius `r`, and a normal ball of
  -- radius `ε` at `p₀`.
  obtain ⟨r, hr, W, hW, hWn⟩ :=
    exists_mem_nhds_forall_isNormalDomain_ball (I := J) (M := N) (Φ x₀ p₀)
  obtain ⟨ε, hε, hεn⟩ := exists_isNormalDomain_ball (I := I) (M := M) p₀
  have hWo : ∀ y ∈ interior W, IsNormalDomain J N y (Metric.ball 0 r) :=
    fun y hy ↦ (hWn y (interior_subset hy)).1
  -- A scale `t > 0` such that `‖t • v‖ < min r ε` whenever `‖v‖ < ‖v₀‖ + 1`.
  set t : ℝ := min r ε / (2 * (‖v₀‖ + 1)) with ht
  have ht0 : 0 < t := div_pos (lt_min hr hε) (by positivity)
  have hnorm {p : M} {v : TangentSpace I p} (hv : ‖v‖ < ‖v₀‖ + 1) : ‖t • v‖ < min r ε := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    calc t * ‖v‖ ≤ t * (‖v₀‖ + 1) := by gcongr
      _ = min r ε / 2 := by rw [ht]; field_simp
      _ < min r ε := half_lt_self (lt_min hr hε)
  have h₀ := hnorm (lt_add_one ‖v₀‖)
  have hexp₀ : t • v₀ ∈ expDomain I M p₀ :=
    hεn.subset_expDomain (mem_ball_zero_iff.2 (h₀.trans_le (min_le_right r ε)))
  have hlog := continuousAt_totalSpaceMk_riemannianLog_apply_riemannianExp hΦi hΦ isOpen_interior
    hWo t (q₀ := (x₀, ⟨p₀, v₀⟩)) (mem_interior_iff_mem_nhds.2 hW) (h₀.trans_le (min_le_left r ε))
    hexp₀
  -- Near `(x₀, v₀)`, the tangent map is `t⁻¹` times that logarithm.
  have hev : ∀ᶠ q in 𝓝 (x₀, (⟨p₀, v₀⟩ : TangentBundle I M)), Φ q.1 q.2.proj ∈ interior W ∧
      ‖q.2.snd‖ < ‖v₀‖ + 1 ∧ t • q.2.snd ∈ expDomain I M q.2.proj := by
    have hbase : Continuous fun q : X × TangentBundle I M ↦ Φ q.1 q.2.proj :=
      hΦ.comp (continuous_fst.prodMk ((FiberBundle.continuous_proj E _).comp continuous_snd))
    have hn : Continuous fun q : X × TangentBundle I M ↦ ‖q.2.snd‖ :=
      (TauCeti.continuous_norm_bundle E (TangentSpace I)).comp continuous_snd
    have hs : Continuous fun q : X × TangentBundle I M ↦
        (⟨q.2.proj, t • q.2.snd⟩ : TangentBundle I M) :=
      continuous_const.smul_totalSpace continuous_snd
    exact ((isOpen_interior.preimage hbase).inter ((isOpen_Iio.preimage hn).inter
      (isOpen_setOfPred_mem_expDomain.preimage hs))).mem_nhds
      ⟨mem_interior_iff_mem_nhds.2 hW, lt_add_one ‖v₀‖, hexp₀⟩
  have hscale : Continuous fun z : TangentBundle J N ↦
      (⟨z.proj, t⁻¹ • z.snd⟩ : TangentBundle J N) :=
    continuous_const.smul_totalSpace continuous_id
  refine (hscale.continuousAt.comp hlog).congr ?_
  filter_upwards [hev] with ⟨x, ⟨p, v⟩⟩ ⟨hx, hv, hve⟩
  have hball : mfderiv I J (Φ x) p (t • v) ∈ Metric.ball 0 r := by
    rw [mem_ball_zero_iff, (hΦi x).norm_mfderiv]
    exact (hnorm hv).trans_le (min_le_left r ε)
  simp only [Function.comp_apply, tangentMap]
  rw [(hΦi x).riemannianLog_apply_riemannianExp hve (hWo _ hx) hball, map_smul, smul_smul,
    inv_mul_cancel₀ ht0.ne', one_smul]

end TauCeti.IsLocalRiemannianIsometry

namespace IsometryEquiv

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

/-- **The tangent map is continuous on the isometry group.** For the isometries of the
Riemannian distances, with the compact-open topology, the
tangent vector `de v` is jointly continuous in the isometry `e` and the tangent vector `v`. -/
theorem continuous_tangentMap :
    Continuous fun q : (M ≃ᵢ N) × TangentBundle I M ↦ tangentMap I J q.1 q.2 := by
  simpa only [coe_toRiemannianIsometry] using
    TauCeti.IsLocalRiemannianIsometry.continuous_tangentMap
      (Φ := fun e : M ≃ᵢ N ↦ e.toRiemannianIsometry I J)
      (fun e ↦ (e.toRiemannianIsometry I J).isLocalRiemannianIsometry)
      (by simpa only [coe_toRiemannianIsometry] using continuous_eval)

/-- **Frame evaluation embeds the isometry group of a compact Riemannian manifold.** There are
finitely many points, one in each connected component, and an orthonormal tangent frame at each,
such that evaluating an isometry of the Riemannian distance at these points and frames is a
closed embedding of the compact group `M ≃ᵢ M`. -/
theorem exists_orthonormalBasis_isClosedEmbedding_tangentMap [CompactSpace M] :
    ∃ (k : ℕ) (p : Fin k → M)
      (b : ∀ c, OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (p c))),
      Function.Bijective (fun c ↦ ConnectedComponents.mk (p c)) ∧
      Topology.IsClosedEmbedding (fun e : M ≃ᵢ M ↦
        fun c ↦ (e (p c), fun i ↦ tangentMap I I e ⟨p c, b c i⟩)) := by
  obtain ⟨k, p, b, hp, hinj⟩ :=
    TauCeti.RiemannianIsometry.exists_orthonormalBasis_injective_tangentMap
      (I := I) (J := I) (M := M) (N := M)
  refine ⟨k, p, b, hp, Continuous.isClosedEmbedding ?_ ?_⟩
  · exact continuous_pi fun c ↦ (continuous_eval_const (p c)).prodMk
      (continuous_pi fun i ↦ continuous_tangentMap.comp (continuous_id.prodMk continuous_const))
  · intro e e' h
    have h' := hinj (a₁ := e.toRiemannianIsometry I I) (a₂ := e'.toRiemannianIsometry I I)
      (by simpa only [coe_toRiemannianIsometry] using h)
    exact IsometryEquiv.ext fun x ↦ by
      simpa only [coe_toRiemannianIsometry] using DFunLike.congr_fun h' x

end IsometryEquiv
