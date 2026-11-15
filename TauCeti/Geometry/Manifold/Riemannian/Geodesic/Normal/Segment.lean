/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# Short geodesic segments depend smoothly on both endpoints

Let `W` be a set of points of a Riemannian manifold `M` and `r > 0` a radius such that the
tangent ball of radius `r` at every point of `W` is a normal domain, as for the uniformly normal
neighbourhoods of `TauCeti.Manifold.exists_mem_nhds_forall_isNormalDomain_ball` or near a compact
set by `IsCompact.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball`. For `x ∈ W` and
`y` in the normal neighbourhood `exp_x '' B(0, r)`, the Riemannian logarithm `log_x y` is the
initial velocity of the radial geodesic segment `t ↦ exp_x (t • log_x y)`, `t ∈ [0, 1]`, from `x`
to `y`.

This file shows that the logarithm, and with it the segment, depends smoothly on **both**
endpoints when `W` is open: the map `(x, y) ↦ (x, log_x y)` from `M × M` to the tangent bundle
is smooth on the open set of such pairs (`TauCeti.Manifold.contMDiffOn_totalSpaceMk_riemannianLog`)
and so is `(x, y, t) ↦ exp_x (t • log_x y)` wherever `t • log_x y` lies in the domain of `exp_x`
(`TauCeti.Manifold.contMDiffAt_riemannianExp_smul_riemannianLog`), in particular for `t ∈ [0, 1]`
(`TauCeti.Manifold.contMDiffOn_riemannianExp_smul_riemannianLog`). The smoothness of `log_x` in
`y` alone, for a fixed `x`, is `TauCeti.Manifold.IsNormalDomain.contMDiffOn_riemannianLog`.

The proof applies the inverse function theorem to `F(x, v) = (x, exp_x v)` on the tube of tangent
vectors of norm less than `r` over `W`. There `F` is injective, since each `exp_x` is injective on
its normal ball, and it is a local diffeomorphism at every point, not only along the zero
section: wherever `exp_x` is a local diffeomorphism, so is `F`
(`TauCeti.Manifold.isLocalDiffeomorphAt_prodMk_proj_riemannianExp`). Hence the inverse of `F`
on its image is smooth (`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`), and it is
`(x, y) ↦ (x, log_x y)`.

When the distance is the Riemannian one, the normal neighbourhood `exp_x '' B(0, r)` is the
metric ball of radius `r` about `x` (`TauCeti.Manifold.IsNormalDomain.image_riemannianExp_ball`),
so the segments are smooth on the pairs at distance less than `r`. One radius serves for all
points of a compact set (`IsCompact.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog`),
and so for all points of a compact manifold
(`TauCeti.Manifold.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog`): pairs of points at
distance less than `r` are joined by short geodesic segments depending smoothly on the pair.

These segments are the minimizing ones. The segment from `x` to `y` has length `dist x y`
(`TauCeti.Manifold.IsNormalDomain.pathELength_riemannianExp_smul_eq_edist_of_mem_ball`), and a
piecewise `C¹` curve from `x` to `y` of the same length, parametrized proportionally to arc length
and staying in the normal neighbourhood, is this segment up to an affine change of time
(`TauCeti.Manifold.IsNormalDomain.eqOn_riemannianExp_smul_of_pathELength_eq_of_piecewise`). Such
smoothly varying segments interpolate broken geodesics through finitely many nearby points.

## Main results

* `TauCeti.Manifold.contMDiffOn_totalSpaceMk_riemannianLog`: the logarithm is jointly smooth in
  both points.
* `TauCeti.Manifold.contMDiffAt_riemannianExp_smul_riemannianLog`,
  `TauCeti.Manifold.contMDiffOn_riemannianExp_smul_riemannianLog`: the short geodesic segments are
  jointly smooth in both endpoints and time.
* `IsCompact.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog`,
  `TauCeti.Manifold.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog`: a single radius
  gives smooth segments from each point of a compact set, or between any two points of a compact
  Riemannian manifold, to every point closer than it.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §10,
  Theorem 10.3 (short geodesics depend differentiably on their two endpoints), whose proof applies
  the inverse function theorem to the same map.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Theorem 3.7 (totally normal
  neighbourhoods).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6
  (uniformly normal neighbourhoods).
-/

public section

open Bundle Manifold Set Function
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Topological

variable
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {W : Set M} {r : ℝ}

/-- **The Riemannian logarithm is smooth in both points.** For an open set `W` of points at which
the tangent ball of radius `r` is a normal domain, the map `(x, y) ↦ (x, log_x y)` to the tangent
bundle is smooth on the pairs with `x ∈ W` and `y ∈ exp_x '' B(0, r)`. -/
theorem contMDiffOn_totalSpaceMk_riemannianLog (hWo : IsOpen W)
    (hW : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r)) :
    ContMDiffOn (I.prod I) I.tangent ∞
      (fun x : M × M ↦ (⟨x.1, riemannianLog I M x.1 (Metric.ball 0 r) x.2⟩ : TangentBundle I M))
      {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} := by
  set F := fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)
  set S := {z : TangentBundle I M | z.proj ∈ W ∧ ‖z.2‖ < r}
  set L := fun x : M × M ↦
    (⟨x.1, riemannianLog I M x.1 (Metric.ball 0 r) x.2⟩ : TangentBundle I M)
  intro x hx
  have : Nonempty (TangentBundle I M) := ⟨⟨x.1, 0⟩⟩
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hinj : InjOn F S := injOn_prodMk_proj_riemannianExp fun q hq ↦ (hW q hq).injOn
  have h := (isLocalDiffeomorphOn_prodMk_proj_riemannianExp (fun q hq ↦ (hW q hq).subset_expDomain)
    fun q hq ↦ (hW q hq).isLocalDiffeomorphOn).contMDiffOn_invFunOn (hWo.norm_lt_bundle r) hinj
  rw [image_prodMk_proj_riemannianExp_setOf_norm_lt] at h
  -- On these pairs `L` is a right inverse of `F` with values in the tube, so it is the inverse
  -- of `F` on the tube.
  have hL : ∀ y ∈ {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r},
      L y ∈ S ∧ F (L y) = y := by
    rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨⟨hy₁, mem_ball_zero_iff.1 (riemannianLog_mem hy₂)⟩,
      Prod.ext rfl (riemannianExp_riemannianLog hy₂)⟩
  have hinv : ∀ y ∈ {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r},
      L y = invFunOn F S y := fun y hy ↦ by
    calc L y = invFunOn F S (F (L y)) := (hinj.leftInvOn_invFunOn (hL y hy).1).symm
      _ = invFunOn F S y := by rw [(hL y hy).2]
  exact (h x hx).congr hinv (hinv x hx)

/-- **Geodesics from `x` towards `y` are smooth in both endpoints and time.** For an open set `W`
of points at which the tangent ball of radius `r` is a normal domain, the map
`(x, y, t) ↦ exp_x (t • log_x y)` is smooth at every `(x, y, t)` with `x ∈ W`,
`y ∈ exp_x '' B(0, r)` and `t • log_x y` in the domain of `exp_x`. -/
theorem contMDiffAt_riemannianExp_smul_riemannianLog (hWo : IsOpen W)
    (hW : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r)) {x y : M} {t : ℝ} (hx : x ∈ W)
    (hy : y ∈ riemannianExp I M x '' Metric.ball 0 r)
    (ht : t • riemannianLog I M x (Metric.ball 0 r) y ∈ expDomain I M x) :
    ContMDiffAt ((I.prod I).prod 𝓘(ℝ)) I ∞
      (fun x : (M × M) × ℝ ↦
        riemannianExp I M x.1.1 (x.2 • riemannianLog I M x.1.1 (Metric.ball 0 r) x.1.2))
      ((x, y), t) := by
  have hP := isOpen_setOf_mem_riemannianExp_image_ball hWo (fun q hq ↦ (hW q hq).subset_expDomain)
    fun q hq ↦ (hW q hq).isLocalDiffeomorphOn
  have hxy : (x, y) ∈
      {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} := ⟨hx, hy⟩
  have hL := (contMDiffOn_totalSpaceMk_riemannianLog hWo hW).contMDiffAt (hP.mem_nhds hxy)
  have hG : ContMDiffAt ((I.prod I).prod 𝓘(ℝ)) I.tangent ∞
      (fun x : (M × M) × ℝ ↦
        (⟨x.1.1, x.2 • riemannianLog I M x.1.1 (Metric.ball 0 r) x.1.2⟩ : TangentBundle I M))
      ((x, y), t) :=
    contMDiffAt_snd.smul_totalSpace (hL.comp ((x, y), t) contMDiffAt_fst)
  have hz : (⟨x, t • riemannianLog I M x (Metric.ball 0 r) y⟩ : TangentBundle I M) ∈
      {z : TangentBundle I M | z.2 ∈ expDomain I M z.proj} := ht
  exact (contMDiffOn_riemannianExp_tangentBundle.contMDiffAt
    (isOpen_setOfPred_mem_expDomain.mem_nhds hz)).comp ((x, y), t) hG

/-- **Short geodesic segments are smooth in both endpoints.** For an open set `W` of points at
which the tangent ball of radius `r` is a normal domain, the radial geodesic segment
`t ↦ exp_x (t • log_x y)`, `t ∈ [0, 1]`, from `x` to `y` depends smoothly on `(x, y, t)` for
`x ∈ W` and `y ∈ exp_x '' B(0, r)`. -/
theorem contMDiffOn_riemannianExp_smul_riemannianLog (hWo : IsOpen W)
    (hW : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r)) :
    ContMDiffOn ((I.prod I).prod 𝓘(ℝ)) I ∞
      (fun x : (M × M) × ℝ ↦
        riemannianExp I M x.1.1 (x.2 • riemannianLog I M x.1.1 (Metric.ball 0 r) x.1.2))
      ({x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} ×ˢ
        Icc (0 : ℝ) 1) := by
  rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩, ht⟩
  exact (contMDiffAt_riemannianExp_smul_riemannianLog hWo hW hx hy ((hW x hx).subset_expDomain
    ((hW x hx).smul_mem (riemannianLog_mem hy) ht.1 ht.2))).contMDiffWithinAt

end Topological

section Metric

variable
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {W : Set M} {r : ℝ}

/-- The pairs `(x, y)` with `x ∈ W` and `y` in the normal neighbourhood `exp_x '' B(0, r)` are the
pairs with `x ∈ W` at distance less than `r`, when the tangent ball of radius `r` at every point
of `W` is a normal domain. -/
theorem setOf_mem_riemannianExp_image_ball_eq
    (hW : ∀ q ∈ W, IsNormalDomain I M q (Metric.ball 0 r)) :
    {x : M × M | x.1 ∈ W ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} =
      {x : M × M | x.1 ∈ W ∧ edist x.1 x.2 < ENNReal.ofReal r} := by
  ext ⟨x, y⟩
  refine and_congr_right fun hx ↦ ?_
  rw [(hW x hx).image_riemannianExp_ball subset_rfl, Metric.mem_eball']

/-- **Short geodesic segments near a compact set.** For a compact set `K` of points of a
Riemannian manifold there is a radius `r > 0` such that the tangent ball of radius `r` at every
point of `K` is a normal domain, and the radial geodesic segment `t ↦ exp_x (t • log_x y)`,
`t ∈ [0, 1]`, from `x` to `y` is smooth in `(x, y, t)` at every `x ∈ K`, every `y` at distance
less than `r` from `x` and every `t ∈ [0, 1]`. -/
theorem _root_.IsCompact.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog {K : Set M}
    (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ (∀ q ∈ K, IsNormalDomain I M q (Metric.ball 0 r)) ∧
      ∀ x ∈ K, ∀ y, edist x y < ENNReal.ofReal r → ∀ t ∈ Icc (0 : ℝ) 1,
        ContMDiffAt ((I.prod I).prod 𝓘(ℝ)) I ∞
          (fun x : (M × M) × ℝ ↦
            riemannianExp I M x.1.1 (x.2 • riemannianLog I M x.1.1 (Metric.ball 0 r) x.1.2))
          ((x, y), t) := by
  obtain ⟨r, hr, U, hUo, hKU, hW⟩ :=
    hK.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball (I := I) (M := M)
  refine ⟨r, hr, fun q hq ↦ hW q (hKU hq), fun x hx y hxy t ht ↦ ?_⟩
  have hy : (x, y) ∈ {x : M × M | x.1 ∈ U ∧ x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} := by
    rw [setOf_mem_riemannianExp_image_ball_eq hW]
    exact ⟨hKU hx, hxy⟩
  exact contMDiffAt_riemannianExp_smul_riemannianLog hUo hW hy.1 hy.2 ((hW x hy.1).subset_expDomain
    ((hW x hy.1).smul_mem (riemannianLog_mem hy.2) ht.1 ht.2))

/-- **Short geodesic segments between nearby points.** On a compact Riemannian manifold there is
a radius `r > 0` such that the tangent ball of radius `r` at every point is a normal domain, and
the radial geodesic segment `t ↦ exp_x (t • log_x y)`, `t ∈ [0, 1]`, from `x` to `y` is smooth in
`(x, y, t)` at every pair of points at distance less than `r` and every `t ∈ [0, 1]`. -/
theorem exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog [CompactSpace M] :
    ∃ r : ℝ, 0 < r ∧ (∀ q : M, IsNormalDomain I M q (Metric.ball 0 r)) ∧
      ∀ x y : M, edist x y < ENNReal.ofReal r → ∀ t ∈ Icc (0 : ℝ) 1,
        ContMDiffAt ((I.prod I).prod 𝓘(ℝ)) I ∞
          (fun x : (M × M) × ℝ ↦
            riemannianExp I M x.1.1 (x.2 • riemannianLog I M x.1.1 (Metric.ball 0 r) x.1.2))
          ((x, y), t) := by
  obtain ⟨r, hr, hW, h⟩ :=
    isCompact_univ.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog (I := I) (M := M)
  exact ⟨r, hr, fun q ↦ hW q (mem_univ q), fun x ↦ h x (mem_univ x)⟩

end Metric

end TauCeti.Manifold
