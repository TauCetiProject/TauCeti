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

A vector-valued function of class `C^k` on a closed embedded submanifold extends with the
same regularity to the ambient manifold. Applying this to the boundary inclusion gives
extensions of boundary data.
-/

public section

open Set
open scoped ContDiff ENat Manifold

namespace Manifold.IsSmoothEmbedding

variable {E E' H H' S M V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ∞}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H S] [TopologicalSpace M] [ChartedSpace H' M]
  [I.Boundaryless] [IsManifold J ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- A vector-valued function of class `C^k` on a closed embedded submanifold extends to
a function of the same class on the ambient manifold. -/
theorem exists_contMDiff_extension_of_isClosed_range {i : S → M}
    (hi : IsSmoothEmbedding I J k i) (hclosed : IsClosed (range i))
    {f : S → V} (hf : ContMDiff I 𝓘(ℝ, V) k f) :
    ∃ F : M → V, ContMDiff J 𝓘(ℝ, V) k F ∧ F ∘ i = f := by
  let e := TauCeti.SmoothEmbedding.ofIsSmoothEmbedding i hi
  have hK : IsClosed (e '' (univ : Set S)) := by
    simpa [e] using hclosed
  obtain ⟨F, hF, -⟩ := e.exists_contMDiffMap_extension ⟨f, hf⟩
    hK isOpen_univ (subset_univ _)
  refine ⟨F, F.contMDiff, funext fun x ↦ ?_⟩
  simpa [e, Function.comp_apply] using hF (mem_univ x)

end Manifold.IsSmoothEmbedding

namespace TauCeti.Manifold

variable {n : ℕ} {k : ℕ∞} {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Every vector-valued `C^k` function on the boundary of a smooth manifold is the
restriction of a global `C^k` function. -/
theorem exists_contMDiff_extension_boundary {f : (𝓡∂ (n + 1)).boundary M → V}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, V) k f) :
    ∃ F : M → V, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, V) k F ∧ F ∘ Subtype.val = f := by
  have hi := isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M
  refine hi.exists_contMDiff_extension_of_isClosed_range ?_ hf
  rw [Subtype.range_coe]
  exact (𝓡∂ (n + 1)).isClosed_boundary (M := M) one_ne_zero

end TauCeti.Manifold
