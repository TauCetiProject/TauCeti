/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TangentCone.Basic
import TauCeti.Analysis.Calculus.TangentCone.Prod

/-!
# Tangent cones of products of sets

The tangent cone of a product `A ×ˢ B` of subsets of manifolds `M` and `N` at `(a, b)` lies in the
product of the tangent cones of `A` at `a` and of `B` at `b`. When `a` is in the closure of `A` and
`b` in that of `B`, it contains the tangent cone of `A` in the first factor and that of `B` in the
second. So the tangent space of `A ×ˢ B`, the span of its tangent cone, is the product of the
tangent spaces of `A` and of `B`. These are the manifold forms of
`TauCeti.tangentConeAt_prod_subset` and `TauCeti.prod_span_tangentConeAt_le`, read in the product
of the preferred charts. They make
transversality pass to products: if `A` and `A'` are transverse in `M` and `B` and `B'` in `N`,
then `A ×ˢ B` and `A' ×ˢ B'` are transverse in `M × N`.

## Main results

* `TauCeti.mtangentConeAt_prod_subset`: the tangent cone of `A ×ˢ B` at `(a, b)` lies in the
  product of the tangent cones.
* `TauCeti.prod_span_mtangentConeAt_le`: the product of the tangent spaces of `A` at `a` and of `B`
  at `b` lies in the tangent space of `A ×ˢ B` at `(a, b)`.
* `TauCeti.span_mtangentConeAt_prod`: the tangent space of `A ×ˢ B` at `(a, b)` is the product of
  the tangent spaces of `A` at `a` and of `B` at `b`.
-/

public section

open Set

namespace TauCeti

variable {𝕜 E E' H H' M N : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {A : Set M} {B : Set N} {a : M} {b : N}

/-- The tangent cone of `A ×ˢ B` at `(a, b)` is that of the product of the chart images of `A` and
of `B`, at the product of the chart images of `a` and `b`. -/
private theorem mtangentConeAt_prod_eq :
    mtangentConeAt (I.prod I') (A ×ˢ B) (a, b) =
      tangentConeAt 𝕜 (((extChartAt I a).symm ⁻¹' A ∩ range I) ×ˢ
        ((extChartAt I' b).symm ⁻¹' B ∩ range I')) (extChartAt I a a, extChartAt I' b b) := by
  have hset : (extChartAt (I.prod I') (a, b)).symm ⁻¹' (A ×ˢ B) ∩ range (I.prod I') =
      ((extChartAt I a).symm ⁻¹' A ∩ range I) ×ˢ ((extChartAt I' b).symm ⁻¹' B ∩ range I') := by
    rw [extChartAt_prod, ModelWithCorners.range_prod]
    ext ⟨u, v⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe]
    tauto
  rw [mtangentConeAt_def, hset, extChartAt_prod, PartialEquiv.prod_coe]

/-- **The tangent cone of a product of sets lies in the product of their tangent cones.** -/
theorem mtangentConeAt_prod_subset :
    mtangentConeAt (I.prod I') (A ×ˢ B) (a, b) ⊆ mtangentConeAt I A a ×ˢ mtangentConeAt I' B b := by
  rw [mtangentConeAt_prod_eq, mtangentConeAt_def, mtangentConeAt_def]
  exact tangentConeAt_prod_subset

/-- **The tangent space of a product of sets contains the product of their tangent spaces.** For
`a` in the closure of `A` and `b` in that of `B`, the span of the tangent cone of `A ×ˢ B` at
`(a, b)` contains the product of the spans of the tangent cones of `A` at `a` and of `B` at `b`. -/
theorem prod_span_mtangentConeAt_le (ha : a ∈ closure A) (hb : b ∈ closure B) :
    (Submodule.span 𝕜 (mtangentConeAt I A a)).prod (Submodule.span 𝕜 (mtangentConeAt I' B b)) ≤
      Submodule.span 𝕜 (mtangentConeAt (I.prod I') (A ×ˢ B) (a, b)) := by
  rw [mtangentConeAt_prod_eq, mtangentConeAt_def, mtangentConeAt_def]
  exact prod_span_tangentConeAt_le (extChartAt_mem_closure_preimage_symm_inter_range ha)
    (extChartAt_mem_closure_preimage_symm_inter_range hb)

/-- **The tangent space of a product of sets is the product of their tangent spaces.** For `a` in
the closure of `A` and `b` in that of `B`, the span of the tangent cone of `A ×ˢ B` at `(a, b)` is
the product of the spans of the tangent cones of `A` at `a` and of `B` at `b`. -/
@[simp]
theorem span_mtangentConeAt_prod (ha : a ∈ closure A) (hb : b ∈ closure B) :
    Submodule.span 𝕜 (mtangentConeAt (I.prod I') (A ×ˢ B) (a, b)) =
      (Submodule.span 𝕜 (mtangentConeAt I A a)).prod (Submodule.span 𝕜 (mtangentConeAt I' B b)) :=
  le_antisymm (Submodule.span_le.2 fun _ hv ↦ Submodule.mem_prod.2
      ⟨Submodule.subset_span (mtangentConeAt_prod_subset hv).1,
        Submodule.subset_span (mtangentConeAt_prod_subset hv).2⟩)
    (prod_span_mtangentConeAt_le ha hb)

end TauCeti
