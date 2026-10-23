/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Extension

/-!
# Smooth maps with values in the intrinsic boundary

A map to the actual boundary manifold is smooth exactly when its composite with the boundary
inclusion is smooth. The reverse implication uses the existing local smooth retractions of a
smooth embedding with boundaryless source.
-/

public section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] {k : ℕ∞ω}
  [IsManifold (𝓡∂ (n + 1)) k M]
  {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]

/-- A map to the induced boundary manifold is smooth within a set precisely when its ambient
inclusion is smooth within that set. The evaluation point need not belong to the set. -/
theorem contMDiffWithinAt_iff_comp_subtypeVal_boundary (hk : k ≠ 0)
    {f : X → (𝓡∂ (n + 1)).boundary M} {s : Set X} {x : X} :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ContMDiffWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k f s x ↔
      ContMDiffWithinAt I (𝓡∂ (n + 1)) k (Subtype.val ∘ f) s x := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  let hi := isSmoothEmbedding_subtypeVal_boundary (n := n) M hk
  refine ⟨fun hf ↦ hi.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hf, fun hf ↦ ?_⟩
  obtain ⟨V, hV, hxV, r, hr, hrf⟩ :=
    (hi.isImmersion.isImmersionAt (f x)).exists_contMDiffOn_retraction hi.isEmbedding
  have hrc := (hr _ hxV).contMDiffAt (hV.mem_nhds hxV)
  have hh := hrc.comp_contMDiffWithinAt x hf
  apply hh.congr_of_eventuallyEq
  · filter_upwards [hf.continuousWithinAt.preimage_mem_nhdsWithin (hV.mem_nhds hxV)] with y hy
    exact (hrf (f y) hy).symm
  · exact (hrf (f x) hxV).symm

/-- Smoothness of a map into the intrinsic boundary can be checked after ambient inclusion. -/
theorem contMDiff_iff_comp_subtypeVal_boundary (hk : k ≠ 0)
    {f : X → (𝓡∂ (n + 1)).boundary M} :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k f ↔
      ContMDiff I (𝓡∂ (n + 1)) k (Subtype.val ∘ f) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  simp only [ContMDiff, ← contMDiffWithinAt_univ,
    contMDiffWithinAt_iff_comp_subtypeVal_boundary hk]

end TauCeti
