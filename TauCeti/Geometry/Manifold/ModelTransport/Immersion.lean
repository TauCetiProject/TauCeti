/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless

/-!
# Immersions under boundaryless model transport

Replacing a boundaryless model `I : ModelWithCorners 𝕜 E H` of `M` by its vector space `E`, as in
`TauCeti.BoundarylessModel I M`, neither creates nor destroys immersions or smooth embeddings, on
either the source or the target side.

The comparison is made chart by chart. An `H`-valued chart `c` of `M` and the `E`-valued chart
`TauCeti.BoundarylessModel.chart I c` of the copy have the same extended coordinates, and every
maximal chart of the copy arises in this way from `TauCeti.BoundarylessModel.originalChart`. So a
normal form `u ↦ (u, 0)` of a map in one pair of charts is literally a normal form of the
transported map in the corresponding pair, with the same complement and the same linear
equivalence. In particular no composition theorem for immersions is used: Mathlib's
`Manifold.IsImmersionAtOfComplement.comp_diffeomorph` only treats diffeomorphisms for a single
model, and the identity `M → BoundarylessModel I M` changes the model from `H` to `E`.

This lets an immersion constructed on a self-modelled manifold, for instance from an
implicit-function chart, be read as an immersion into the original manifold.

## Main results

* `TauCeti.BoundarylessModel.isImmersionAtOfComplement_target_iff` and
  `TauCeti.BoundarylessModel.isImmersionAtOfComplement_source_iff`: the pointwise normal form with
  a fixed complement is preserved by changing the target or the source model.
* The corresponding statements for `Manifold.IsImmersionAt`, `Manifold.IsImmersionOfComplement`,
  `Manifold.IsImmersion` and `Manifold.IsSmoothEmbedding`.
-/

public section

open Function Set Manifold
open scoped ContDiff Manifold

namespace TauCeti

namespace BoundarylessModel

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' G : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 E' G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

/-- **Changing the target model preserves the immersion normal form at a point.** A map `g` into
`M` is an immersion at `x` with complement `F` exactly when it is one as a map into the
self-modelled copy of `M`. The charts of the two normal forms correspond under
`TauCeti.BoundarylessModel.chart` and `TauCeti.BoundarylessModel.originalChart`, with the same
linear equivalence. -/
@[simp]
theorem isImmersionAtOfComplement_target_iff {g : N → M} {x : N} :
    IsImmersionAtOfComplement F J 𝓘(𝕜, E) n (homeomorph I M ∘ g) x ↔
      IsImmersionAtOfComplement F J I n g x := by
  constructor
  · intro h
    refine IsImmersionAtOfComplement.mk_of_charts h.equiv h.domChart
      (originalChart I h.codChart) h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas
      ((originalChart_mem_maximalAtlas_iff I _ n).2 h.codChart_mem_maximalAtlas) ?_ ?_
    · rw [originalChart_source]
      exact h.mem_codChart_source
    · rw [originalChart_source]
      exact h.source_subset_preimage_source
    · intro y hy
      rw [comp_apply, comp_apply, originalChart_extend_apply]
      simpa only [comp_apply, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
        id_eq] using h.writtenInCharts hy
  · intro h
    refine IsImmersionAtOfComplement.mk_of_charts h.equiv h.domChart (chart I h.codChart)
      h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas
      ((chart_mem_maximalAtlas_iff I _ n).2 h.codChart_mem_maximalAtlas) ?_ ?_
    · rw [chart_source, mem_preimage, comp_apply, Homeomorph.symm_apply_apply]
      exact h.mem_codChart_source
    · rw [chart_source, ← preimage_comp, ← comp_assoc, Homeomorph.symm_comp_self, id_comp]
      exact h.source_subset_preimage_source
    · intro y hy
      simpa only [comp_apply, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, id_eq,
        chart_apply, Homeomorph.symm_apply_apply] using h.writtenInCharts hy

/-- Changing the target model preserves immersions with a fixed complement. -/
@[simp]
theorem isImmersionOfComplement_target_iff {g : N → M} :
    IsImmersionOfComplement F J 𝓘(𝕜, E) n (homeomorph I M ∘ g) ↔
      IsImmersionOfComplement F J I n g :=
  ⟨fun h x ↦ isImmersionAtOfComplement_target_iff.1 (h x),
    fun h x ↦ isImmersionAtOfComplement_target_iff.2 (h x)⟩

/-- Changing the target model preserves being an immersion at a point. -/
@[simp]
theorem isImmersionAt_target_iff {g : N → M} {x : N} :
    IsImmersionAt J 𝓘(𝕜, E) n (homeomorph I M ∘ g) x ↔ IsImmersionAt J I n g x :=
  ⟨fun h ↦
      (isImmersionAtOfComplement_target_iff.1 h.isImmersionAtOfComplement_complement).isImmersionAt,
    fun h ↦
      (isImmersionAtOfComplement_target_iff.2 h.isImmersionAtOfComplement_complement).isImmersionAt⟩

/-- Changing the target model preserves immersions. -/
@[simp]
theorem isImmersion_target_iff {g : N → M} :
    IsImmersion J 𝓘(𝕜, E) n (homeomorph I M ∘ g) ↔ IsImmersion J I n g :=
  ⟨fun h ↦ (isImmersionOfComplement_target_iff.1 h.isImmersionOfComplement_complement).isImmersion,
    fun h ↦ (isImmersionOfComplement_target_iff.2 h.isImmersionOfComplement_complement).isImmersion⟩

/-- Changing the target model preserves smooth embeddings. -/
@[simp]
theorem isSmoothEmbedding_target_iff {g : N → M} :
    IsSmoothEmbedding J 𝓘(𝕜, E) n (homeomorph I M ∘ g) ↔ IsSmoothEmbedding J I n g := by
  rw [isSmoothEmbedding_iff, isSmoothEmbedding_iff, isImmersion_target_iff,
    Homeomorph.comp_isEmbedding_iff]

/-- **Changing the source model preserves the immersion normal form at a point.** A map `g` on
`M` is an immersion at a point with complement `F` exactly when it is one as a map on the
self-modelled copy of `M`. The charts of the two normal forms correspond under
`TauCeti.BoundarylessModel.chart` and `TauCeti.BoundarylessModel.originalChart`, with the same
linear equivalence. -/
@[simp]
theorem isImmersionAtOfComplement_source_iff {g : M → N} {x : BoundarylessModel I M} :
    IsImmersionAtOfComplement F 𝓘(𝕜, E) J n (g ∘ (homeomorph I M).symm) x ↔
      IsImmersionAtOfComplement F I J n g ((homeomorph I M).symm x) := by
  constructor
  · intro h
    refine IsImmersionAtOfComplement.mk_of_charts h.equiv (originalChart I h.domChart)
      h.codChart ?_ h.mem_codChart_source
      ((originalChart_mem_maximalAtlas_iff I _ n).2 h.domChart_mem_maximalAtlas)
      h.codChart_mem_maximalAtlas ?_ ?_
    · rw [originalChart_source, mem_preimage, Homeomorph.apply_symm_apply]
      exact h.mem_domChart_source
    · rw [originalChart_source]
      intro y hy
      have hy' := h.source_subset_preimage_source hy
      rwa [mem_preimage, comp_apply, Homeomorph.symm_apply_apply] at hy'
    · intro v hv
      rw [originalChart_extend_target] at hv
      have hv' : v ∈ (h.domChart.extend 𝓘(𝕜, E)).target := by
        simpa [OpenPartialHomeomorph.extend_target] using hv
      rw [comp_apply, comp_apply, originalChart_extend_symm_apply]
      simpa only [comp_apply, OpenPartialHomeomorph.extend_coe_symm,
        modelWithCornersSelf_coe_symm, id_eq] using h.writtenInCharts hv'
  · intro h
    refine IsImmersionAtOfComplement.mk_of_charts h.equiv (chart I h.domChart) h.codChart
      ?_ h.mem_codChart_source ((chart_mem_maximalAtlas_iff I _ n).2 h.domChart_mem_maximalAtlas)
      h.codChart_mem_maximalAtlas ?_ ?_
    · rw [chart_source]
      exact h.mem_domChart_source
    · rw [chart_source, preimage_comp]
      exact preimage_mono h.source_subset_preimage_source
    · intro v hv
      have hv' : v ∈ (h.domChart.extend I).target := by
        simpa [OpenPartialHomeomorph.extend_target, I.range_eq_univ] using hv
      simpa only [comp_apply, OpenPartialHomeomorph.extend_coe_symm,
        OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe_symm, id_eq, chart_symm_apply,
        Homeomorph.symm_apply_apply] using h.writtenInCharts hv'

/-- Changing the source model preserves immersions with a fixed complement. -/
@[simp]
theorem isImmersionOfComplement_source_iff {g : M → N} :
    IsImmersionOfComplement F 𝓘(𝕜, E) J n (g ∘ (homeomorph I M).symm) ↔
      IsImmersionOfComplement F I J n g :=
  ⟨fun h x ↦ by
      simpa only [Homeomorph.symm_apply_apply] using
        isImmersionAtOfComplement_source_iff.1 (h (homeomorph I M x)),
    fun h x ↦ isImmersionAtOfComplement_source_iff.2 (h _)⟩

/-- Changing the source model preserves being an immersion at a point. -/
@[simp]
theorem isImmersionAt_source_iff {g : M → N} {x : BoundarylessModel I M} :
    IsImmersionAt 𝓘(𝕜, E) J n (g ∘ (homeomorph I M).symm) x ↔
      IsImmersionAt I J n g ((homeomorph I M).symm x) :=
  ⟨fun h ↦
      (isImmersionAtOfComplement_source_iff.1 h.isImmersionAtOfComplement_complement).isImmersionAt,
    fun h ↦
      (isImmersionAtOfComplement_source_iff.2 h.isImmersionAtOfComplement_complement).isImmersionAt⟩

/-- Changing the source model preserves immersions. -/
@[simp]
theorem isImmersion_source_iff {g : M → N} :
    IsImmersion 𝓘(𝕜, E) J n (g ∘ (homeomorph I M).symm) ↔ IsImmersion I J n g :=
  ⟨fun h ↦ (isImmersionOfComplement_source_iff.1 h.isImmersionOfComplement_complement).isImmersion,
    fun h ↦ (isImmersionOfComplement_source_iff.2 h.isImmersionOfComplement_complement).isImmersion⟩

/-- Changing the source model preserves smooth embeddings. -/
@[simp]
theorem isSmoothEmbedding_source_iff {g : M → N} :
    IsSmoothEmbedding 𝓘(𝕜, E) J n (g ∘ (homeomorph I M).symm) ↔ IsSmoothEmbedding I J n g := by
  rw [isSmoothEmbedding_iff, isSmoothEmbedding_iff, isImmersion_source_iff,
    Homeomorph.isEmbedding_comp_iff]

end BoundarylessModel

end TauCeti
