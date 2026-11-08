/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Tangent images of graphs and product maps

Under the canonical identification of product tangent spaces, the tangent image of
`x ↦ (f x, g x)` is the range of `df × dg`, that of `x ↦ (x, f x)` is the linear graph of `df`,
and the tangent image of a product map `f × g` at `(x, y)` is the product of the tangent images
of `f` at `x` and of `g` at `y`. These are the
bridges between linear criteria for graphs and products of subspaces and geometric conditions on
embedded graphs and products of submanifolds, including Lagrangian ones. The calculations use
Mathlib's product derivatives, `LinearMap.graph_eq_range_prod` and `LinearMap.range_prodMap`.
The coordinates of the differential of a graph are computed by `mfderiv_graph_fst_apply` and
`mfderiv_graph_snd_apply`.
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

/-- The differential of the graph `y ↦ (y, f y)` has first coordinate `v`. -/
@[simp]
theorem mfderiv_graph_fst_apply {f : M → N} {x : M} (hf : MDifferentiableAt I J f x)
    (v : TangentSpace I x) : (mfderiv I (I.prod J) (fun y ↦ (y, f y)) x v).1 = v := by
  have hg : MDifferentiableAt I (I.prod J) (fun y ↦ (y, f y)) x := mdifferentiableAt_id.prodMk hf
  rw [← hg.mfderiv_fst_apply]
  -- The first coordinate of `y ↦ (y, f y)` is the identity by definition.
  exact DFunLike.congr_fun (mfderiv_id (I := I) (x := x)) v

/-- The differential of the graph `y ↦ (y, f y)` has second coordinate `df v`. -/
@[simp]
theorem mfderiv_graph_snd_apply {f : M → N} {x : M} (hf : MDifferentiableAt I J f x)
    (v : TangentSpace I x) :
    (mfderiv I (I.prod J) (fun y ↦ (y, f y)) x v).2 = mfderiv I J f x v := by
  have hg : MDifferentiableAt I (I.prod J) (fun y ↦ (y, f y)) x := mdifferentiableAt_id.prodMk hf
  exact (hg.mfderiv_snd_apply v).symm

/-- The tangent image of a map `y ↦ (f y, g y)` into a product, read in the product tangent
spaces, is the range of the product of the differentials of its two coordinates. -/
theorem map_range_mfderiv_prodMk {E' H'' N' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H''] {J' : ModelWithCorners 𝕜 E' H''} [TopologicalSpace N']
    [ChartedSpace H'' N'] {f : M → N} {g : M → N'} {x : M} (hf : MDifferentiableAt I J f x)
    (hg : MDifferentiableAt I J' g x) :
    (LinearMap.range (mfderiv I (J.prod J') (fun y ↦ (f y, g y)) x).toLinearMap).map
        (Manifold.tangentSpaceProdEquiv (I := J) (J := J') (f x, g x)).toLinearEquiv.toLinearMap =
      LinearMap.range ((mfderiv I J f x).toLinearMap.prod (mfderiv I J' g x).toLinearMap) := by
  have hd : (Manifold.tangentSpaceProdEquiv (I := J) (J := J') (f x, g x)).toLinearEquiv.toLinearMap
      ∘ₗ (mfderiv I (J.prod J') (fun y ↦ (f y, g y)) x).toLinearMap =
      (mfderiv I J f x).toLinearMap.prod (mfderiv I J' g x).toLinearMap := by
    -- Native product derivatives use definitionally equal product tangent synonyms.
    erw [mfderiv_prodMk hf hg]
    apply LinearMap.ext
    intro v
    exact Manifold.tangentSpaceProdEquiv_apply (I := J) (J := J') (f x, g x)
      (((mfderiv I J f x).prod (mfderiv I J' g x)) v)
  rw [← LinearMap.range_comp, hd]

/-- The tangent image of a graph, read in the product tangent spaces, is the graph of the
original map's differential. -/
@[simp]
theorem map_range_mfderiv_graph {f : M → N} {x : M} (hf : MDifferentiableAt I J f x) :
    (LinearMap.range (mfderiv I (I.prod J) (fun y ↦ (y, f y)) x).toLinearMap).map
        (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (x, f x)).toLinearEquiv.toLinearMap =
      (mfderiv I J f x).toLinearMap.graph := by
  rw [map_range_mfderiv_prodMk (f := fun y ↦ y) mdifferentiableAt_id hf,
    LinearMap.graph_eq_range_prod]
  congr
  exact congrArg ContinuousLinearMap.toLinearMap mfderiv_id

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
