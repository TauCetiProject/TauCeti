/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TangentCone
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Tangent cones of products of sets

The tangent cone of a product `A ×ˢ B` of subsets of manifolds `M` and `N`, at a point `(a, b)` with
`a ∈ A` and `b ∈ B`, contains the tangent cone of `A` at `a` in the first factor and that of `B` at
`b` in the second. So the tangent space of `A ×ˢ B`, the span of its tangent cone, contains the
product of the tangent spaces of `A` and of `B`. This is the manifold form of Mathlib's
`subset_tangentConeAt_prod_left` and `subset_tangentConeAt_prod_right`, read in the product of the
preferred charts. It is what makes transversality pass to products: if `A` and `A'` are transverse
in `M` and `B` and `B'` in `N`, then `A ×ˢ B` and `A' ×ˢ B'` are transverse in `M × N`.

## Main results

* `TauCeti.prod_span_mtangentConeAt_le`: the product of the tangent spaces of `A` at `a` and of `B`
  at `b` lies in the tangent space of `A ×ˢ B` at `(a, b)`.
-/

public section

open Set

namespace TauCeti

variable {𝕜 E E' H H' M N : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

/-- **The tangent space of a product of sets contains the product of their tangent spaces.** For
`a ∈ A` and `b ∈ B`, the span of the tangent cone of `A ×ˢ B` at `(a, b)` contains the product of
the spans of the tangent cones of `A` at `a` and of `B` at `b`. -/
theorem prod_span_mtangentConeAt_le {A : Set M} {B : Set N} {a : M} {b : N} (ha : a ∈ A)
    (hb : b ∈ B) :
    (Submodule.span 𝕜 (mtangentConeAt I A a)).prod (Submodule.span 𝕜 (mtangentConeAt I' B b)) ≤
      Submodule.span 𝕜 (mtangentConeAt (I.prod I') (A ×ˢ B) (a, b)) := by
  have hset : (extChartAt (I.prod I') (a, b)).symm ⁻¹' (A ×ˢ B) ∩ range (I.prod I') =
      ((extChartAt I a).symm ⁻¹' A ∩ range I) ×ˢ ((extChartAt I' b).symm ⁻¹' B ∩ range I') := by
    rw [extChartAt_prod, ModelWithCorners.range_prod]
    ext ⟨u, v⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe]
    tauto
  rw [mtangentConeAt_def, mtangentConeAt_def, mtangentConeAt_def, hset, extChartAt_prod,
    PartialEquiv.prod_coe, ← LinearMap.span_inl_union_inr]
  refine Submodule.span_mono (union_subset (subset_tangentConeAt_prod_left (subset_closure ?_))
    (subset_tangentConeAt_prod_right (subset_closure ?_)))
  · exact ⟨by rwa [mem_preimage, extChartAt_to_inv],
      extChartAt_target_subset_range b (mem_extChartAt_target b)⟩
  · exact ⟨by rwa [mem_preimage, extChartAt_to_inv],
      extChartAt_target_subset_range a (mem_extChartAt_target a)⟩

end TauCeti
