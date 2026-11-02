/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Tangent images of graphs and product maps

Under the canonical identification of product tangent spaces, the tangent image of
`x ↦ (x, f x)` is the linear graph of `df`, and the tangent image of a product map `f × g` at
`(x, y)` is the product of the tangent images of `f` at `x` and of `g` at `y`. These are the
bridges between linear criteria for graphs and products of subspaces and geometric conditions on
embedded graphs and products of submanifolds, including Lagrangian ones. The calculations use
Mathlib's product derivatives, `LinearMap.graph_eq_range_prod` and `LinearMap.range_prodMap`.
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

/-- The tangent image of a product of differentiable maps, read in the product tangent spaces, is
the product of the tangent images of the factors. -/
@[simp]
theorem map_range_mfderiv_prodMap
    {E' F' G G' M' N' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace G]
    {I' : ModelWithCorners 𝕜 E' G} [TopologicalSpace M'] [ChartedSpace G M']
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [TopologicalSpace G']
    {J' : ModelWithCorners 𝕜 F' G'} [TopologicalSpace N'] [ChartedSpace G' N']
    {f : M → M'} {g : N → N'} {p : M × N} (hf : MDifferentiableAt I I' f p.1)
    (hg : MDifferentiableAt J J' g p.2) :
    (LinearMap.range (mfderiv (I.prod J) (I'.prod J') (Prod.map f g) p).toLinearMap).map
        (Manifold.tangentSpaceProdEquiv (I := I') (J := J')
          (Prod.map f g p)).toLinearEquiv.toLinearMap =
      (LinearMap.range (mfderiv I I' f p.1).toLinearMap).prod
        (LinearMap.range (mfderiv J J' g p.2).toLinearMap) := by
  have hd : (Manifold.tangentSpaceProdEquiv (I := I') (J := J')
        (Prod.map f g p)).toLinearEquiv.toLinearMap ∘ₗ
      (mfderiv (I.prod J) (I'.prod J') (Prod.map f g) p).toLinearMap =
      ((mfderiv I I' f p.1).toLinearMap.prodMap (mfderiv J J' g p.2).toLinearMap) ∘ₗ
        (Manifold.tangentSpaceProdEquiv (I := I) (J := J) p).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, tangentSpaceProdEquiv_apply]
    -- Native product derivatives use definitionally equal product tangent synonyms.
    erw [mfderiv_prodMap hf hg]
    rfl
  rw [← LinearMap.range_comp, hd, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.range_prodMap]

end TauCeti.Manifold
