/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Tangent vectors with constant coordinates in a chart

Fix a point `x₀` of a manifold `M` and a vector `u` of the model space `E`. Near `x₀`, the tangent
vector at `x` whose coordinates in the chart at `x₀` are `u` is `tangentCoordChange I x₀ x x u`,
read in the chart at `x`. These tangent vectors converge to `u` at `x₀` in the tangent bundle
(`TangentBundle.tendsto_mk_tangentCoordChange`): in the canonical trivialization at `x₀` their
fibre coordinates are eventually constant, equal to `u`.
-/

public section

open Filter Topology
open scoped Manifold

namespace TangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **Tangent vectors with constant coordinates in the chart at `x₀`** converge in the tangent
bundle: `(x, B x u) → (x₀, u)` as `x → x₀`, where `B x` is the tangent coordinate change from the
chart at `x₀` to the chart at `x`. -/
theorem tendsto_mk_tangentCoordChange (x₀ : M) (u : E) :
    Tendsto (fun x ↦ (⟨x, tangentCoordChange I x₀ x x u⟩ : TangentBundle I M)) (𝓝 x₀)
      (𝓝 ⟨x₀, u⟩) := by
  set T := trivializationAt E (TangentSpace I) x₀
  refine (T.tendsto_mk_nhds_mk_iff 𝕜 (FiberBundle.mem_baseSet_trivializationAt E _ x₀)).2
    ⟨tendsto_id, tendsto_nhds_of_eventually_eq ?_⟩
  -- On the chart at `x₀`, the fibre coordinate in `T` is the tangent coordinate change back.
  filter_upwards [extChartAt_source_mem_nhds (I := I) x₀] with x hx
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) T
    (mem_trivializationAt_baseSet_of_mem_extChartAt_source hx) _).trans
    ((trivializationAt_snd_eq_tangentCoordChange _).trans
      ((TauCeti.tangentCoordChange_tangentCoordChange hx (mem_extChartAt_source x) u).trans
        (TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self x₀ u).symm))

end TangentBundle
