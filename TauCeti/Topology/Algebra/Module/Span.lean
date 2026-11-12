/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Dense spans

A generating family, regarded as a family in the closure of its span, has dense span there.
This lets constructions on densely spanning families apply to arbitrary closed spans.
Conversely, a densely spanning family stays densely spanning when pushed forward along a
continuous linear map with dense range, such as the projection onto a quotient module, so that a
quotient of a module spanned densely by a countable family is again spanned densely by one.
No norm, separation, or completeness assumptions are needed.
-/

public section

namespace TauCeti

open Set Submodule

/-- A family of vectors in the closure of its span still has dense span there. -/
theorem dense_span_in_topologicalClosure {R ι M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul R M] (v : ι → M) :
    Dense (span R (range (fun i ↦
      (⟨v i, (span R (range v)).le_topologicalClosure (subset_span (mem_range_self i))⟩ :
        (span R (range v)).topologicalClosure))) :
      Set (span R (range v)).topologicalClosure) := by
  rw [Subtype.dense_iff]
  have hspan := congrArg (fun p : Submodule R M ↦ (p : Set M))
    (Submodule.map_span (span R (range v)).topologicalClosure.subtype
      (range (fun i ↦
        (⟨v i, (span R (range v)).le_topologicalClosure (subset_span (mem_range_self i))⟩ :
          (span R (range v)).topologicalClosure))))
  simp only [Submodule.map_coe, Submodule.coe_subtype, ← range_comp, Function.comp_def,
    Submodule.subtype_apply] at hspan
  exact closure_mono hspan.symm.subset

end TauCeti

/-- The image of a densely spanning family under a continuous linear map with dense range has
dense span. For instance, the image of a densely spanning family in a quotient module `M ⧸ p`
(take `f = p.mkQ`) has dense span. -/
theorem DenseRange.dense_span_range_comp {R M N ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [AddCommMonoid N] [Module R N]
    [TopologicalSpace N] {f : M →ₗ[R] N} (hf : DenseRange f) (hfc : Continuous f) {v : ι → M}
    (hv : Dense (Submodule.span R (Set.range v) : Set M)) :
    Dense (Submodule.span R (Set.range (f ∘ v)) : Set N) := by
  rw [Set.range_comp, ← Submodule.map_span, Submodule.map_coe]
  exact hf.dense_image hfc hv
