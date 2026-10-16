/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Extending smooth data from an embedded submanifold

A smooth embedding of a boundaryless manifold admits local smooth retractions.
Consequently, vector-valued smooth data on its source extend to the ambient
manifold along any closed portion of its image. The ambient extension can be
supported inside a prescribed open neighbourhood, and has compact support when
the portion is compact. Neither the full embedded image nor the source needs to
be compact or closed.

These are the local-coordinate and partition-of-unity steps in extending an
isotopy's velocity to an ambient vector field. The local retraction uses
Mathlib's immersion normal form, projecting `(u, v)` to `u`; gluing uses
`IsClosed.exists_contMDiffMap_eqOn`. The source must be boundaryless because
that projection must land in an open source-chart target.

Reference: M. Hirsch, *Differential Topology*, Chapter 8, §1 (isotopy extension).
-/

public section

noncomputable section

open Set Function Topology Manifold
open scoped Manifold ContDiff

namespace Manifold.IsImmersionAt

section Local

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] {n : ℕ∞ω} {f : M → N} {x : M}

/-- A topological embedding with a `C^n` immersion normal form at `x` admits a
local `C^n` retraction to its boundaryless source. Its left-inverse law holds for
every source point whose image is in the chosen neighbourhood, not just for one
source chart. No immersion or smoothness hypothesis is needed away from `x`. -/
theorem exists_contMDiffOn_retraction (h : IsImmersionAt I J n f x) (hf : IsEmbedding f) :
    ∃ V : Set N, IsOpen V ∧ f x ∈ V ∧ ∃ r : N → M,
      ContMDiffOn J I n r V ∧ ∀ y, f y ∈ V → r (f y) = y := by
  let q : N → E := fun z => (h.equiv.symm ((h.codChart.extend J) z)).1
  have hq : ContMDiffOn J 𝓘(𝕜, E) n q h.codChart.source :=
    (ContinuousLinearMap.fst 𝕜 E h.complement).contDiff.contMDiff.comp_contMDiffOn
      (h.equiv.symm.contDiff.contMDiff.comp_contMDiffOn
        (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas))
  have hqf : ∀ y ∈ h.domChart.source, q (f y) = (h.domChart.extend I) y := by
    intro y hy
    have hy' : y ∈ (h.domChart.extend I).source := by
      rwa [h.domChart.extend_source]
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv hy'] at hw
    simp only [q, hw, ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨W, hW, hWf⟩ := hf.isInducing.isOpen_iff.mp h.domChart.open_source
  let V := (h.codChart.source ∩ q ⁻¹' (h.domChart.extend I).target) ∩ W
  have hV : IsOpen V :=
    (hq.continuousOn.isOpen_inter_preimage h.codChart.open_source
      h.domChart.isOpen_extend_target).inter hW
  have hxV : f x ∈ V := by
    refine ⟨⟨h.mem_codChart_source, ?_⟩, ?_⟩
    · rw [mem_preimage, hqf x h.mem_domChart_source]
      exact (h.domChart.extend I).map_source (by
        simpa only [h.domChart.extend_source] using h.mem_domChart_source)
    · have hx := h.mem_domChart_source
      rw [← hWf] at hx
      exact hx
  refine ⟨V, hV, hxV, (h.domChart.extend I).symm ∘ q, ?_, ?_⟩
  · have hi := contMDiffOn_extend_symm h.domChart_mem_maximalAtlas
    rw [← h.domChart.extend_target'] at hi
    exact hi.comp (hq.mono fun _ hz => hz.1.1) fun _ hz => hz.1.2
  · intro y hy
    have hydom : y ∈ h.domChart.source := by
      rw [← hWf]
      exact hy.2
    rw [Function.comp_apply, hqf y hydom]
    exact (h.domChart.extend I).left_inv (by rwa [h.domChart.extend_source])

end Local

end Manifold.IsImmersionAt

namespace TauCeti.SmoothEmbedding

section Global

variable {E E' F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N] {n : ℕ∞}

/-- Extend smooth vector-valued data along a closed portion of an embedded
boundaryless manifold, with topological support inside a prescribed open set.
Closedness is required only of the portion of the image where agreement is requested. -/
theorem exists_contMDiffMap_extension (f : SmoothEmbedding I J n M N)
    (g : C^n⟮I, M; 𝓘(ℝ, F), F⟯) {K : Set M} (hK : IsClosed (f '' K))
    {U : Set N} (hU : IsOpen U) (hKU : f '' K ⊆ U) :
    ∃ G : C^n⟮J, N; 𝓘(ℝ, F), F⟯, EqOn (G ∘ f) g K ∧ tsupport G ⊆ U := by
  classical
  let a : N → F := fun z => if hz : z ∈ f '' K then g (Classical.choose hz) else 0
  have ha (x : M) (hx : x ∈ K) : a (f x) = g x := by
    have hz : f x ∈ f '' K := mem_image_of_mem f hx
    dsimp only [a]
    rw [dite_eq_left hz]
    exact congrArg g (f.isEmbedding.injective (Classical.choose_spec hz).2)
  have hloc : ∀ z ∈ f '' K, ∃ V : Set N, IsOpen V ∧ z ∈ V ∧
      ∃ a' : N → F, ContMDiffOn J 𝓘(ℝ, F) n a' V ∧ EqOn a' a ((f '' K) ∩ V) := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := hz
    obtain ⟨V, hV, hxV, r, hr, hrf⟩ :=
      (f.isImmersion.isImmersionAt x).exists_contMDiffOn_retraction f.isEmbedding
    refine ⟨V, hV, hxV, g ∘ r, g.contMDiff.comp_contMDiffOn hr, ?_⟩
    rintro _ ⟨⟨y, hy, rfl⟩, hfy⟩
    rw [Function.comp_apply, hrf y hfy, ha y hy]
  obtain ⟨G, hGa, hGU⟩ := hK.exists_contMDiffMap_eqOn (I := J) hU hKU hloc
  exact ⟨G, fun x hx => (hGa (mem_image_of_mem f hx)).trans (ha x hx), hGU⟩

/-- Data on a compact portion of an embedded boundaryless manifold admit a
compactly supported smooth ambient extension inside any prescribed open neighbourhood. -/
theorem exists_contMDiffMap_extension_hasCompactSupport (f : SmoothEmbedding I J n M N)
    (g : C^n⟮I, M; 𝓘(ℝ, F), F⟯) {K : Set M} (hK : IsCompact K)
    {U : Set N} (hU : IsOpen U) (hKU : f '' K ⊆ U) :
    ∃ G : C^n⟮J, N; 𝓘(ℝ, F), F⟯,
      EqOn (G ∘ f) g K ∧ HasCompactSupport G ∧ tsupport G ⊆ U := by
  have : LocallyCompactSpace H' := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  obtain ⟨V, hV, hKV, hVU, hcV⟩ :=
    exists_open_between_and_isCompact_closure (hK.image f.contMDiff.continuous) hU hKU
  obtain ⟨G, hG, hGV⟩ := f.exists_contMDiffMap_extension g
    (hK.image f.contMDiff.continuous).isClosed hV hKV
  exact ⟨G, hG, hcV.of_isClosed_subset isClosed_closure (hGV.trans subset_closure),
    hGV.trans (subset_closure.trans hVU)⟩

end Global

end TauCeti.SmoothEmbedding
