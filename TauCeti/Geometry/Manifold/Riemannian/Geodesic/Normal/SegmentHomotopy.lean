/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import TauCeti.Topology.VectorBundle.Smul

/-!
# Nearby maps are homotopic through short geodesics

Let `f, g : X → M` be continuous maps into a Riemannian manifold such that, for every `z`, the
tangent ball of radius `r` at `f z` is a normal domain and `g z` lies in the normal neighbourhood
`exp_{f z} '' B(0, r)`. Then `f` and `g` are homotopic through the short geodesic segments
`t ↦ exp_{f z} (t • log_{f z} (g z))`, `t ∈ [0, 1]`, and the homotopy is constant at the points
where `f` and `g` agree. When the distance is the Riemannian one, the condition on `g` says that
`g z` is at distance less than `r` from `f z`; on a compact manifold one radius `r > 0` is a
normal radius at every point, so maps which are uniformly closer than `r` are homotopic. This is
the step of the minimization of length in a free homotopy class of loops showing that a uniform
limit of loops in the class stays in the class.

The continuity of the homotopy rests on that of `(x, y) ↦ (x, log_x y)`. It is smooth over an
open set of base points (`TauCeti.Manifold.contMDiffOn_totalSpaceMk_riemannianLog`); here the
base points are only those at which the tangent ball of radius `r` is a normal domain, which need
not form an open set, and the logarithm is still continuous there: near a pair `(x, y)`, the
local inverse of `(x, v) ↦ (x, exp_x v)` at `(x, log_x y)` keeps the base point and lands in the
tube of vectors of norm less than `r`, where `exp_x` is injective.

## Main results

* `TauCeti.Manifold.continuousOn_totalSpaceMk_riemannianLog`: the logarithm is continuous in both
  points.
* `TauCeti.Manifold.homotopicRel_of_forall_mem_riemannianExp_image_ball`,
  `TauCeti.Manifold.homotopicRel_of_forall_edist_lt`: two maps whose values are joined by short
  geodesic segments are homotopic relative to any set on which they agree.
* `TauCeti.Manifold.exists_pos_forall_homotopic_of_edist_lt`: on a compact Riemannian manifold,
  maps which are uniformly close enough are homotopic.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 12, §2 (closed geodesics in free
  homotopy classes).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6
  (uniformly normal neighbourhoods).
-/

public section

open Bundle Manifold Set Topology
open scoped ContDiff Manifold

universe u

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Topological

variable
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {r : ℝ}

/-- **The Riemannian logarithm is continuous in both points.** The map `(x, y) ↦ (x, log_x y)` to
the tangent bundle is continuous on the pairs such that the tangent ball of radius `r` at `x` is a
normal domain and `y ∈ exp_x '' B(0, r)`. Unlike `contMDiffOn_totalSpaceMk_riemannianLog`, the
base points need not form an open set. -/
theorem continuousOn_totalSpaceMk_riemannianLog :
    ContinuousOn
      (fun x : M × M ↦ (⟨x.1, riemannianLog I M x.1 (Metric.ball 0 r) x.2⟩ : TangentBundle I M))
      {x : M × M | IsNormalDomain I M x.1 (Metric.ball 0 r) ∧
        x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r} := by
  set F := fun z : TangentBundle I M ↦ (z.proj, riemannianExp I M z.proj z.2)
  set S := {z : TangentBundle I M | IsNormalDomain I M z.proj (Metric.ball 0 r) ∧ ‖z.2‖ < r}
  set L := fun x : M × M ↦
    (⟨x.1, riemannianLog I M x.1 (Metric.ball 0 r) x.2⟩ : TangentBundle I M)
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hL : ∀ x ∈ {x : M × M | IsNormalDomain I M x.1 (Metric.ball 0 r) ∧
      x.2 ∈ riemannianExp I M x.1 '' Metric.ball 0 r}, L x ∈ S ∧ F (L x) = x := by
    rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩
    exact ⟨⟨hx₁, mem_ball_zero_iff.1 (riemannianLog_mem hx₂)⟩,
      Prod.ext rfl (riemannianExp_riemannianLog hx₂)⟩
  have hinj : InjOn F S :=
    injOn_prodMk_proj_riemannianExp (W := {q | IsNormalDomain I M q (Metric.ball 0 r)})
      fun q hq ↦ hq.injOn
  intro x hx
  obtain ⟨e, hxe, hFe⟩ := (isLocalDiffeomorphOn_prodMk_proj_riemannianExp
    (W := {q | IsNormalDomain I M q (Metric.ball 0 r)}) (fun q hq ↦ hq.subset_expDomain)
    fun q hq ↦ hq.isLocalDiffeomorphOn).isLocalHomeomorphOn (L x) (hL x hx).1
  have hex : e (L x) = x := by rw [← hFe]; exact (hL x hx).2
  have hcont : ContinuousAt e.symm x := by
    have := e.continuousAt_symm (e.map_source hxe)
    rwa [hex] at this
  have hsrc : ∀ᶠ y in 𝓝 x, e.symm y ∈ {z : TangentBundle I M | ‖z.2‖ < r} := by
    refine hcont.preimage_mem_nhds ?_
    rw [← hex, e.left_inv hxe]
    exact (isOpen_lt (TauCeti.continuous_norm_bundle E _) continuous_const).mem_nhds (hL x hx).1.2
  have htgt : ∀ᶠ y in 𝓝 x, y ∈ e.target := by
    rw [← hex]
    exact e.open_target.mem_nhds (e.map_source hxe)
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_
    ((e.left_inv hxe).symm.trans (congrArg e.symm hex))
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hsrc,
    mem_nhdsWithin_of_mem_nhds htgt] with y hy hys hyt
  have hFy : F (e.symm y) = y := (congrFun hFe (e.symm y)).trans (e.right_inv hyt)
  have hproj : (e.symm y).proj = y.1 := congrArg Prod.fst hFy
  exact hinj (hL y hy).1 ⟨hproj ▸ hy.1, hys⟩ ((hL y hy).2.trans hFy.symm)

/-- **Maps joined by short geodesic segments are homotopic.** Let `f, g : X → M` be continuous
maps such that, for every `z`, the tangent ball of radius `r` at `f z` is a normal domain and
`g z ∈ exp_{f z} '' B(0, r)`. Then `(t, z) ↦ exp_{f z} (t • log_{f z} (g z))` is a homotopy from
`f` to `g`, constant on every set where `f` and `g` agree. -/
theorem homotopicRel_of_forall_mem_riemannianExp_image_ball {X : Type*} [TopologicalSpace X]
    {f g : C(X, M)} {S : Set X} (hf : ∀ z, IsNormalDomain I M (f z) (Metric.ball 0 r))
    (hg : ∀ z, g z ∈ riemannianExp I M (f z) '' Metric.ball 0 r) (hS : ∀ z ∈ S, f z = g z) :
    f.HomotopicRel g S := by
  have hlog := continuousOn_totalSpaceMk_riemannianLog.comp_continuous
    ((f.continuous.comp continuous_snd).prodMk (g.continuous.comp continuous_snd))
    fun p : unitInterval × X ↦ ⟨hf p.2, hg p.2⟩
  have hsmul := (TauCeti.VectorBundle.continuous_smul ℝ E (TangentSpace I : M → Type _)).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hlog)
  refine ⟨{
    toFun := fun p ↦
      riemannianExp I M (f p.2) ((p.1 : ℝ) • riemannianLog I M (f p.2) (Metric.ball 0 r) (g p.2))
    continuous_toFun := continuousOn_riemannianExp_tangentBundle.comp_continuous hsmul fun p ↦
      (hf p.2).subset_expDomain ((hf p.2).smul_mem (riemannianLog_mem (hg p.2)) p.1.2.1 p.1.2.2)
    map_zero_left := fun z ↦ by simp
    map_one_left := fun z ↦ by simp [riemannianExp_riemannianLog (hg z)]
    prop' := fun t z hz ↦ ?_ }⟩
  simp [← hS z hz, (hf z).riemannianLog_self]

end Topological

section Metric

variable
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ}

/-- **Close maps are homotopic.** Let `f, g : X → M` be continuous maps into a Riemannian manifold
such that, for every `z`, the tangent ball of radius `r` at `f z` is a normal domain and `g z` is
at distance less than `r` from `f z`. Then `f` and `g` are homotopic through the short geodesic
segments joining their values, relative to any set on which they agree. -/
theorem homotopicRel_of_forall_edist_lt {X : Type*} [TopologicalSpace X] {f g : C(X, M)}
    {S : Set X} (hf : ∀ z, IsNormalDomain I M (f z) (Metric.ball 0 r))
    (hfg : ∀ z, edist (f z) (g z) < ENNReal.ofReal r) (hS : ∀ z ∈ S, f z = g z) :
    f.HomotopicRel g S :=
  homotopicRel_of_forall_mem_riemannianExp_image_ball hf (fun z ↦ by
    rw [(hf z).image_riemannianExp_ball subset_rfl, Metric.mem_eball']
    exact hfg z) hS

/-- **Close maps into a compact manifold are homotopic.** On a compact Riemannian manifold there is
a radius `r > 0` such that the tangent ball of radius `r` at every point is a normal domain, and
any two continuous maps into the manifold whose values are pointwise at distance less than `r` are
homotopic. -/
theorem exists_pos_forall_homotopic_of_edist_lt [CompactSpace M] :
    ∃ r : ℝ, 0 < r ∧ (∀ q : M, IsNormalDomain I M q (Metric.ball 0 r)) ∧
      ∀ {X : Type u} [TopologicalSpace X] {f g : C(X, M)},
        (∀ z, edist (f z) (g z) < ENNReal.ofReal r) → f.Homotopic g := by
  obtain ⟨r, hr, U, -, hU, hW⟩ :=
    isCompact_univ.exists_pos_exists_isOpen_superset_forall_isNormalDomain_ball (I := I) (M := M)
  have hN (q : M) : IsNormalDomain I M q (Metric.ball 0 r) := hW q (hU (mem_univ q))
  exact ⟨r, hr, hN, fun hfg ↦
    (homotopicRel_of_forall_edist_lt (S := ∅) (fun _ ↦ hN _) hfg fun _ h ↦ h.elim).homotopic⟩

end Metric

end TauCeti.Manifold
