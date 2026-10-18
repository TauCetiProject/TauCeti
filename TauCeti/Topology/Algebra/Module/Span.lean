/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Dense span inside a closed span

A generating family, regarded as a family in the closure of its span, has dense span there.
This lets constructions on densely spanning families apply to arbitrary closed spans.
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
