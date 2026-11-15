/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Orientation.Family

/-!
# Flows of complete vector fields preserve orientation

Let `v` be a complete `C¹` vector field on an oriented boundaryless manifold `M`. Its global flow
`t ↦ globalFlow v hv hcomplete t` is a jointly `C¹` family of diffeomorphisms parametrized by the
connected space `ℝ`, starting at the identity at time `0`. Hence every time-`t` map preserves every
orientation of `M` at every point
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_globalFlow`).

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_globalFlow`: the time-`t` map of the
  global flow of a complete `C¹` vector field preserves orientation at every point.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (orientations and flows).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M] {ι : Type*} [Fintype ι]

/-- **Flows preserve orientation.** For a complete `C¹` vector field `v` on a boundaryless manifold
`M`, every time-`t` map of its global flow preserves every orientation of `M` at every point. -/
theorem isOrientationPreservingAt_globalFlow (o : Manifold.Orientation I M ι)
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v) (t : ℝ) (x : M) :
    IsOrientationPreservingAt o o (globalFlow v hv hcomplete t) x := by
  refine isOrientationPreservingAt_family_of_id (L := 𝓘(ℝ, ℝ)) o
    (contMDiff_globalFlow_uncurry hcomplete (n := 1) le_rfl hv) x (fun s ↦ ?_)
    (Flow.map_zero_apply _) t
  have hcoe := coe_globalFlowDiffeomorph hcomplete (n := 1) le_rfl hv s
  have hinv := (globalFlowDiffeomorph hcomplete (n := 1) le_rfl hv s).isInvertible_mfderiv
    one_ne_zero (x := x)
  rwa [hcoe] at hinv

end TauCeti.Manifold.Orientation
