/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.EVariationComparison
public import TauCeti.Topology.MetricSpace.Length

/-!
# A Riemannian manifold is a length space

The Riemannian distance between two points is the infimum of the *Riemannian* lengths of the `C¹`
paths joining them. Being a length space asks for the same infimum taken over the *metric* lengths
— total variations — of all *continuous* paths joining them. The two agree: a continuous path is
never shorter than the distance between its endpoints, and on a `C¹` path the metric length is the
Riemannian one, by `TauCeti.Manifold.eVariationOn_eq_pathELength`, so the `C¹` paths already
realise the infimum.

This is what makes the purely metric notions of `TauCeti/Topology/MetricSpace/Length.lean`
available on a Riemannian manifold. No completeness is needed here; it is the refinement in which
the infimum is attained, `TauCeti.Manifold.isGeodesicSpace_of_completeSpace`, that needs it.

## Main results

* `TauCeti.Manifold.isLengthSpace`: a manifold whose extended distance is the Riemannian distance
  is a length space.

## References

* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001, Section 2.4.
-/

public section

open Bundle Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

variable (I) in
include I in
/-- **A Riemannian manifold is a length space.** If the extended distance of `M` is the Riemannian
distance, it is the infimum of the total variations of the continuous curves joining two points.
The model `I` cannot be inferred from the conclusion, so it is an explicit argument. -/
theorem isLengthSpace : IsLengthSpace M := by
  refine IsLengthSpace.of_exists_eVariationOn_lt fun x y c hc ↦ ?_
  rw [IsRiemannianManifold.out (I := I) x y] at hc
  obtain ⟨γ, hx, hy, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hc
  exact ⟨γ, ⟨hγ.continuousOn, hx, hy⟩, (eVariationOn_eq_pathELength hγ).trans_lt hlen⟩

end TauCeti.Manifold
