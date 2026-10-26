/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Tangent images of graphs

Under the canonical identification of product tangent spaces, the tangent image of
`x ↦ (x, f x)` is the linear graph of `df`. This is the bridge between linear graph
criteria and geometric conditions on embedded graphs, including Lagrangian graphs.
The calculation uses Mathlib's product derivative and `LinearMap.graph_eq_range_prod`.
-/

public section

open scoped Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 F H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- The tangent image of a graph, read in the product tangent spaces, is the graph of the
original map's differential. -/
@[simp]
theorem map_range_mfderiv_graph {f : M → N} {x : M} (hf : MDifferentiableAt I J f x) :
    (LinearMap.range (mfderiv I (I.prod J) (fun y ↦ (y, f y)) x).toLinearMap).map
        (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (x, f x)).toLinearEquiv.toLinearMap =
      (mfderiv I J f x).toLinearMap.graph := by
  have hd : (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (x, f x)).toLinearEquiv.toLinearMap ∘ₗ
      (mfderiv I (I.prod J) (fun y ↦ (y, f y)) x).toLinearMap =
      LinearMap.id.prod (mfderiv I J f x).toLinearMap := by
    -- Native product derivatives use definitionally equal product tangent synonyms.
    erw [mfderiv_prodMk mdifferentiableAt_id hf, mfderiv_id]
    apply LinearMap.ext
    intro v
    exact Manifold.tangentSpaceProdEquiv_apply (I := I) (J := J) (x, f x)
      (((ContinuousLinearMap.id 𝕜 (TangentSpace I x)).prod (mfderiv I J f x)) v)
  rw [← LinearMap.range_comp, hd, ← LinearMap.graph_eq_range_prod]

end TauCeti.Manifold
