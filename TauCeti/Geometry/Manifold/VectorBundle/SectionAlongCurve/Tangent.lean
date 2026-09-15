/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Coordinates of tangent fields along curves in two charts

For a tangent field along a curve, the coordinate readings `TauCeti.Manifold.sectionCoord` in the
preferred tangent-bundle trivializations at two points differ by the tangent coordinate change
between the two charts, wherever the curve lies in both base sets.

## Main results

* `TauCeti.Manifold.sectionCoord_coordChange`: two chart readings of a tangent field along a curve
  differ by the tangent coordinate change.
* `TauCeti.Manifold.sectionCoord_eventuallyEq_coordChange`: the same relation near a parameter
  whose image lies in both base sets.
-/

public section

open Bundle Filter
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (γ : 𝕜 → M) (V : Π t, TangentSpace I (γ t))

/-- The coordinate readings of a tangent field along a curve in the trivializations at two points
whose base sets contain `γ r` differ by the tangent coordinate change between them. -/
theorem sectionCoord_coordChange {x y : M} {r : 𝕜}
    (hx : γ r ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hy : γ r ∈ (trivializationAt E (TangentSpace I) y).baseSet) :
    sectionCoord (F := E) γ V y r =
      tangentCoordChange I x y (γ r) (sectionCoord (F := E) γ V x r) := by
  rw [sectionCoord_apply, sectionCoord_apply, ← continuousLinearMapAt_symmL_coordChange hx hy,
    (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := 𝕜) hx]

/-- Near a parameter whose image lies in two base sets, the coordinate readings of a tangent field
along a curve are related by the tangent coordinate change. -/
theorem sectionCoord_eventuallyEq_coordChange {x y : M} {s : Set 𝕜} {r : 𝕜}
    (hγ : ContinuousWithinAt γ s r)
    (hx : γ r ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hy : γ r ∈ (trivializationAt E (TangentSpace I) y).baseSet) :
    sectionCoord (F := E) γ V y =ᶠ[𝓝[s] r]
      fun q ↦ tangentCoordChange I x y (γ q) (sectionCoord (F := E) γ V x q) := by
  filter_upwards
    [hγ.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx),
    hγ.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) y).open_baseSet.mem_nhds hy)] with q hqx hqy
  exact sectionCoord_coordChange γ V hqx hqy

end TauCeti.Manifold
