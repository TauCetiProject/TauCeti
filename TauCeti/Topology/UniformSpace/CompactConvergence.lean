/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Totally bounded families for compact convergence

For a topological space `X` and a uniform space `E`, the continuous maps `C(X, E)` carry the
uniformity of compact convergence (`ContinuousMap.compactConvergenceUniformSpace`). This file
shows that a totally bounded family of continuous maps takes totally bounded sets of values on
each compact subset of `X`. For a seminormed group target this bounds the norms of the whole
family on each compact set at once, which is how relatively compact families of continuous maps
are shown to be locally bounded.

The proof adapts the finite-cover argument behind Mathlib's `TotallyBounded.isBounded` to compact
convergence: finitely many maps approximate the whole family uniformly on `K`, and each of them
has a compact, hence totally bounded, image of `K`.

## Main results

* `ContinuousMap.totallyBounded_biUnion_image`: if `A ⊆ C(X, E)` is totally bounded and
  `K ⊆ X` is compact, then the set `⋃ g ∈ A, g '' K` of all values on `K` is totally bounded.
-/

public section

open Set Uniformity

namespace ContinuousMap

variable {X E : Type*} [TopologicalSpace X] [UniformSpace E]

/-- The values on a compact set `K` of a totally bounded family `A` of continuous maps, for the
uniformity of compact convergence, form a totally bounded set. -/
theorem totallyBounded_biUnion_image {A : Set C(X, E)} (hA : TotallyBounded A) {K : Set X}
    (hK : IsCompact K) : TotallyBounded (⋃ g ∈ A, g '' K) := by
  intro V hV
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  -- Finitely many maps `g ∈ t` approximate every member of `A` within `W`, uniformly on `K`.
  obtain ⟨t, ht, hAt⟩ :=
    hasBasis_compactConvergenceUniformity.totallyBounded_iff.mp hA (K, W) ⟨hK, hW⟩
  -- Their values on `K` form a compact, hence totally bounded, set.
  obtain ⟨s, hs, hts⟩ :=
    (ht.isCompact_biUnion fun g _ => hK.image g.continuous).totallyBounded W hW
  refine ⟨s, hs, iUnion₂_subset fun f hf => ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hAt hf)
  obtain ⟨y, hy, hgy⟩ := mem_iUnion₂.mp (hts (mem_biUnion hg (mem_image_of_mem g hx)))
  exact mem_biUnion hy (hWV ⟨g x, hfg x hx, hgy⟩)

end ContinuousMap
