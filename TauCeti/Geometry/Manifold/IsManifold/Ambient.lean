/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Manifold structures read through an ambient manifold

Let `M` be a charted space over `H`, with model `I : ModelWithCorners 𝕜 E H`, and let `j : M → N`
be a map into a charted space `N` over `I'`. Say that `j` *reads the chart `e` of `M` smoothly*
when there are maps `F : N → E` and `G : E → N`, `C^n` on sets `U ⊆ N` and `V ⊆ E`, such that
for every point `z` of the source of `e`, `j z ∈ U`, `I (e z) ∈ V`, `F (j z) = I (e z)` and
`G (I (e z)) = j z`. Thus `F` reads `I ∘ e` off `j`, and `G` reads `j` back off the coordinates.

If `j` reads every chart of `M` smoothly, then the transition map from `e` to `e'`, written in the
model vector space, is `F' ∘ G` on its domain, so it is `C^n`: the atlas of `M` is a `C^n` manifold
(`TauCeti.isManifold_of_forall_mem_atlas_exists_contMDiffOn`), and `j` is `C^n` for it
(`TauCeti.contMDiff_of_forall_mem_atlas_exists_contMDiffOn`).

The charts of `M` need not belong to the model of `N`, and `j` need not be injective. A typical
use is a subset of a boundaryless manifold, such as one side of a hypersurface, charted on a
half-space: its charts are not charts of the ambient manifold, but they are compared through it,
with `j` the inclusion. The map `F` may extend `I ∘ e` beyond `j` of the source of `e`, which is
how coordinates that are only one-sided in `M` are seen to be smooth.
-/

public section

open Set Topology

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- **Atlases read smoothly through an ambient manifold.** If a map `j : M → N` reads every chart
`e` of `M` through maps `F : N → E` and `G : E → N` which are `C^n` on sets `U` and `V`, in the
sense that every point `z` of the source of `e` has `j z ∈ U`, `I (e z) ∈ V`, `F (j z) = I (e z)`
and `G (I (e z)) = j z`, then `M` is a `C^n` manifold. -/
theorem isManifold_of_forall_mem_atlas_exists_contMDiffOn (j : M → N)
    (h : ∀ e ∈ atlas H M, ∃ (F : N → E) (G : E → N) (U : Set N) (V : Set E),
      ContMDiffOn I' 𝓘(𝕜, E) n F U ∧ ContMDiffOn 𝓘(𝕜, E) I' n G V ∧
        ∀ z ∈ e.source, j z ∈ U ∧ I (e z) ∈ V ∧ F (j z) = I (e z) ∧ G (I (e z)) = j z) :
    IsManifold I n M := by
  refine isManifold_of_contDiffOn I n M fun e₁ e₂ he₁ he₂ => ?_
  obtain ⟨_, G, _, V, -, hG, hGe⟩ := h e₁ he₁
  obtain ⟨F, _, U, _, hF, -, hFe⟩ := h e₂ he₂
  -- A point of the domain is `I (e₁ z)` with `z` in the sources of `e₁` and `e₂`; there the
  -- transition map is `F ∘ G`.
  have hdom : ∀ v ∈ I.symm ⁻¹' (e₁.symm ≫ₕ e₂).source ∩ range I, ∃ z ∈ e₁.source,
      z ∈ e₂.source ∧ I (e₁ z) = v := by
    rintro v ⟨hv, x, rfl⟩
    rw [mem_preimage, I.left_inv, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      OpenPartialHomeomorph.symm_source] at hv
    exact ⟨e₁.symm x, e₁.map_target hv.1, hv.2, by rw [e₁.right_inv hv.1]⟩
  rw [← contMDiffOn_iff_contDiffOn]
  refine (hF.comp (hG.mono fun v hv => ?_) fun v hv => ?_).congr fun v hv => ?_
  · obtain ⟨z, hz, -, rfl⟩ := hdom v hv
    exact (hGe z hz).2.1
  · obtain ⟨z, hz, hz₂, rfl⟩ := hdom v hv
    rw [mem_preimage, (hGe z hz).2.2.2]
    exact (hFe z hz₂).1
  · obtain ⟨z, hz, hz₂, rfl⟩ := hdom v hv
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, I.left_inv,
      e₁.left_inv hz, (hGe z hz).2.2.2, (hFe z hz₂).2.2.1]

/-- **Maps reading an atlas smoothly are smooth.** Under the hypotheses of
`TauCeti.isManifold_of_forall_mem_atlas_exists_contMDiffOn`, the map `j : M → N` is `C^n` for the
`C^n` manifold structure of `M`. -/
theorem contMDiff_of_forall_mem_atlas_exists_contMDiffOn (j : M → N)
    (h : ∀ e ∈ atlas H M, ∃ (F : N → E) (G : E → N) (U : Set N) (V : Set E),
      ContMDiffOn I' 𝓘(𝕜, E) n F U ∧ ContMDiffOn 𝓘(𝕜, E) I' n G V ∧
        ∀ z ∈ e.source, j z ∈ U ∧ I (e z) ∈ V ∧ F (j z) = I (e z) ∧ G (I (e z)) = j z) :
    ContMDiff I I' n j := by
  have := isManifold_of_forall_mem_atlas_exists_contMDiffOn j h
  intro z
  obtain ⟨_, G, _, V, -, hG, hGe⟩ := h _ (chart_mem_atlas H z)
  rw [contMDiffAt_iff_source_of_mem_source (mem_chart_source H z)]
  -- A point of the target of the extended chart at `z` is `I (e y)` for `y` in the source of the
  -- chart `e` at `z`; there `j` read in `e` is `G`.
  have htarget : ∀ v ∈ (extChartAt I z).target, ∃ y ∈ (chartAt H z).source,
      I (chartAt H z y) = v := by
    rintro v hv
    rw [extChartAt_target, mem_inter_iff, mem_preimage] at hv
    obtain ⟨hv, x, rfl⟩ := hv
    rw [I.left_inv] at hv
    exact ⟨(chartAt H z).symm x, (chartAt H z).map_target hv, by
      rw [(chartAt H z).right_inv hv]⟩
  have hV : (extChartAt I z).target ⊆ V := fun v hv => by
    obtain ⟨y, hy, rfl⟩ := htarget v hv
    exact (hGe y hy).2.1
  have hmem : (extChartAt I z).target ∈ 𝓝[range I] (extChartAt I z z) :=
    extChartAt_target_mem_nhdsWithin z
  refine ((hG _ (hV (mem_extChartAt_target z))).mono_of_mem_nhdsWithin
    (Filter.mem_of_superset hmem hV)).congr_of_eventuallyEq_of_mem ?_ (mem_range_self _)
  filter_upwards [hmem] with v hv
  obtain ⟨y, hy, rfl⟩ := htarget v hv
  simp only [Function.comp_apply, extChartAt_coe_symm, I.left_inv, (chartAt H z).left_inv hy,
    (hGe y hy).2.2.2]

end TauCeti
