/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Extension

/-!
# Smooth ambient extensions of boundary data

A vector-valued function of class `C^k` on the intrinsic boundary of a smooth manifold
extends with the same regularity to the ambient manifold, by the extension theorem for
closed smooth embeddings.
-/

public section

open Set
open scoped ContDiff ENat Manifold

namespace ContMDiff

variable {n : ℕ} {k : ℕ∞} {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Every vector-valued `C^k` function on the boundary of a smooth manifold is the
restriction of a global `C^k` function. -/
theorem exists_extension_boundary {f : (𝓡∂ (n + 1)).boundary M → V}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, V) k f) :
    ∃ F : M → V, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, V) k F ∧ F ∘ Subtype.val = f := by
  have hi := TauCeti.isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M
  refine hi.exists_contMDiff_extension_of_isClosed_range ?_ hf
  rw [Subtype.range_coe]
  exact (𝓡∂ (n + 1)).isClosed_boundary (M := M) one_ne_zero

end ContMDiff
