/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
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
    ((continuous_subtypeVal.comp continuous_fst).prodMk hlog)
  refine ⟨{
    toFun := fun p ↦
      riemannianExp I M (f p.2) ((p.1 : ℝ) • riemannianLog I M (f p.2) (Metric.ball 0 r) (g p.2))
    continuous_toFun := continuousOn_riemannianExp_tangentBundle.comp_continuous hsmul fun p ↦
      (hf p.2).subset_expDomain ((hf p.2).smul_mem (riemannianLog_mem
          (hg p.2)) p.1.property.1 p.1.property.2)
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
