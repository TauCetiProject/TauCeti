/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Interpolation

/-!
# Interpolation near a metric of positive scalar curvature

Fix a smooth weight `f : M → [0, 1]`, and write `(1 - f) g + f h` for the interpolation
`Bundle.ContMDiffRiemannianMetric.convexCombinationFun` of two metrics `g` and `h`. Even when `g`
and `h` have positive scalar curvature, the interpolation need not: its scalar curvature involves
the first and second derivatives of `f` and of both metrics, not only the scalar curvatures of `g`
and `h`. Suppose instead that `g` and `h` are both close, in the chart C² topology, to a single
metric `g₀` whose scalar curvature is positive on a compact set `L` of points. For the fixed
weight `f`, interpolation is continuous in the chart C² topology
(`Bundle.ContMDiffRiemannianMetric.continuous_convexCombinationFun`) and fixes `g₀` when both
metrics equal `g₀`, and scalar curvature depends continuously on the metric in that topology.
Hence the scalar curvature of the interpolation on `L` is bounded below by one positive constant
for all such `g` and `h`; this holds on an arbitrary manifold `M`. When `M` itself is
compact, positive scalar curvature is a C²-open condition
(`Bundle.ContMDiffRiemannianMetric.isOpen_setOf_hasPositiveScalarCurvature_chartC2`), so if `g₀`
has positive scalar curvature, then so has the interpolation, at every point of `M`.

This is how a metric of positive scalar curvature is joined across a collar to a C²-close model
metric, such as a product metric near the boundary of a surgery region, with a uniform positive
margin rather than by a partition-of-unity average of two metrics of positive scalar curvature.
There the weight `f` is a cutoff in the collar coordinate.

## Main results

* `IsCompact.exists_pos_eventually_forall_le_scalarCurvature_convexCombinationFun`: if `g₀` has
  positive scalar curvature on a compact set `L`, then for all pairs `(g, h)` close enough to
  `(g₀, g₀)` in the chart C² topology, `(1 - f) g + f h` has scalar curvature on `L` bounded below
  by a common positive constant.
* `HasPositiveScalarCurvature.eventually_hasPositiveScalarCurvature_convexCombinationFun`, in the
  namespace `Bundle.ContMDiffRiemannianMetric`: on a compact manifold, if `g₀` has positive scalar
  curvature, then so has `(1 - f) g + f h` for all pairs `(g, h)` close enough to `(g₀, g₀)` in
  the chart C² topology.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
-/

open Bundle Filter Set
open scoped ContDiff Manifold Topology TauCeti.MetricC2

public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Interpolation near a metric of positive scalar curvature keeps a uniform scalar gap.** Let
`f : M → [0, 1]` be smooth, and let `g₀` have positive scalar curvature at every point of a
compact set `L`. Then there is `ε > 0` such that `(1 - f) g + f h` has scalar curvature at least
`ε` on `L` for all pairs `(g, h)` close enough to `(g₀, g₀)` in the chart C² topology. The
manifold need not be compact. -/
theorem IsCompact.exists_pos_eventually_forall_le_scalarCurvature_convexCombinationFun
    {L : Set M} (hL : IsCompact L)
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hpos : ∀ x ∈ L, 0 < g₀.scalarCurvature x) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ×
        ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) in 𝓝 (g₀, g₀),
      ∀ x ∈ L, ε ≤ (q.1.convexCombinationFun q.2 f hf hf₀ hf₁).scalarCurvature x := by
  obtain ⟨ε, hε, hev⟩ := hL.exists_pos_eventually_forall_le_scalarCurvature_chartC2 hpos
  exact ⟨ε, hε, ((ContMDiffRiemannianMetric.continuous_convexCombinationFun 2 f hf hf₀ hf₁).tendsto'
    (g₀, g₀) g₀ (ContMDiffRiemannianMetric.convexCombinationFun_self g₀ f hf hf₀ hf₁)).eventually
    hev⟩

namespace Bundle.ContMDiffRiemannianMetric

/-- **Interpolation near a metric of positive scalar curvature has positive scalar curvature.**
On a compact manifold, let `g₀` have positive scalar curvature and let `f : M → [0, 1]` be smooth.
Then `(1 - f) g + f h` has positive scalar curvature for all pairs `(g, h)` close enough to
`(g₀, g₀)` in the chart C² topology. -/
theorem HasPositiveScalarCurvature.eventually_hasPositiveScalarCurvature_convexCombinationFun
    [CompactSpace M] {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg₀ : g₀.HasPositiveScalarCurvature) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) :
    ∀ᶠ q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ×
        ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) in 𝓝 (g₀, g₀),
      (q.1.convexCombinationFun q.2 f hf hf₀ hf₁).HasPositiveScalarCurvature :=
  ((continuous_convexCombinationFun 2 f hf hf₀ hf₁).tendsto' (g₀, g₀) g₀
    (convexCombinationFun_self g₀ f hf hf₀ hf₁)).eventually
    (isOpen_setOf_hasPositiveScalarCurvature_chartC2.mem_nhds hg₀)

end Bundle.ContMDiffRiemannianMetric
