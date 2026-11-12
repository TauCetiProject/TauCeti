/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Complete
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.FiniteAtlas

/-!
# The Banach space of `C^k` maps on a compact manifold

Let `M` be a manifold and `k` a natural number. A finite chart atlas with compact coordinate
pieces whose relative interiors cover `M` defines the finite-atlas `C^k` norm
`ContMDiffMap.finiteAtlasSeminorm`. This file packages it as a normed space structure on the
vector-valued `C^k` maps (`ContMDiffMap.finiteAtlasNormedAddCommGroup`,
`ContMDiffMap.finiteAtlasNormedSpace`) whose topology is, by definition, the weak Whitney
topology, and proves that this normed space is complete when `M` is boundaryless and modelled
on a locally compact space over `ℝ` or `ℂ` and the target is complete
(`ContMDiffMap.completeSpace_finiteAtlas`). Such atlases exist on every compact manifold modelled
on a locally compact space (`TauCeti.exists_finite_compact_chart_cover`), and any two of them give
equivalent norms (`ContMDiffMap.exists_finiteAtlasSeminorm_le`).

This is the Banach space of `C^k` functions on a closed manifold to which Banach-space methods,
such as the Sard–Smale theorem for the universal section `(f, x) ↦ df_x`, apply.

The structures are definitions rather than instances, since they depend on the chosen atlas.
Use them with `letI` together with `open scoped TauCeti.ManifoldWeakWhitney`.

## Main definitions

* `ContMDiffMap.finiteAtlasNormedAddCommGroup`: the normed group of `C^k` maps with the
  finite-atlas norm and the weak Whitney topology.
* `ContMDiffMap.finiteAtlasNormedSpace`: the corresponding normed space structure.

## Main results

* `ContMDiffMap.norm_finiteAtlas`: the norm is the finite-atlas seminorm.
* `ContMDiffMap.completeSpace_finiteAtlas`: the normed space is complete.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} [Fintype ι] {c : ι → M}
  {K : ∀ i, TopologicalSpace.Compacts (extChartAt I (c i)).target}
  (k : ℕ) [IsManifold I k M]
  (hK : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (c i)).source,
    (⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ :
      (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

/-- The normed group of vector-valued `C^k` maps with the `C^k` norm of a finite atlas whose
compact pieces have relative interiors covering the manifold. Its topology is the weak Whitney
topology. -/
noncomputable abbrev finiteAtlasNormedAddCommGroup :
    NormedAddCommGroup C^k⟮I, M; 𝓘(𝕜, F), F⟯ := by
  let _ : Norm C^k⟮I, M; 𝓘(𝕜, F), F⟯ := ⟨finiteAtlasSeminorm c K k le_rfl⟩
  let core : NormedSpace.Core 𝕜 C^k⟮I, M; 𝓘(𝕜, F), F⟯ :=
    { norm_nonneg f := apply_nonneg _ f
      norm_smul a f := map_smul_eq_mul _ a f
      norm_triangle f g := map_add_le_add _ f g
      norm_eq_zero_iff f := finiteAtlasSeminorm_eq_zero_iff
        (fun y ↦ (hK y).imp fun _ ⟨hy, hyK⟩ ↦ ⟨hy, interior_subset hyK⟩) k le_rfl f }
  refine NormedAddCommGroup.ofCoreReplaceTopology core ?_
  rw [(withSeminorms_finiteAtlasSeminorm k hK).topologicalSpace_eq_iInf, ciInf_unique]

/-- The normed space of vector-valued `C^k` maps with the `C^k` norm of a finite atlas. -/
noncomputable abbrev finiteAtlasNormedSpace :
    letI := finiteAtlasNormedAddCommGroup (F := F) k hK
    NormedSpace 𝕜 C^k⟮I, M; 𝓘(𝕜, F), F⟯ :=
  letI := finiteAtlasNormedAddCommGroup (F := F) k hK
  { norm_smul_le a f := (map_smul_eq_mul (finiteAtlasSeminorm c K k le_rfl) a f).le }

/-- The norm of the finite-atlas normed group is the finite-atlas seminorm. -/
theorem norm_finiteAtlas (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯) :
    letI := finiteAtlasNormedAddCommGroup (F := F) k hK
    ‖f‖ = finiteAtlasSeminorm c K k le_rfl f :=
  rfl

/-- **The Banach space of `C^k` maps.** On a boundaryless manifold modelled on a locally compact
space over `ℝ` or `ℂ`, the vector-valued `C^k` maps with values in a Banach space form a complete
normed space for the finite-atlas norm. -/
theorem completeSpace_finiteAtlas [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E]
    [I.Boundaryless] [CompleteSpace F] :
    letI := finiteAtlasNormedAddCommGroup (F := F) k hK
    CompleteSpace C^k⟮I, M; 𝓘(𝕜, F), F⟯ := by
  let _ := finiteAtlasNormedAddCommGroup (F := F) k hK
  -- The norm uniformity and the topological-group uniformity are uniform additive group
  -- structures with the same topology, hence equal.
  have e : (PseudoMetricSpace.toUniformSpace : UniformSpace C^k⟮I, M; 𝓘(𝕜, F), F⟯) =
      IsTopologicalAddGroup.rightUniformSpace C^k⟮I, M; 𝓘(𝕜, F), F⟯ :=
    IsUniformAddGroup.ext inferInstance isUniformAddGroup_of_addCommGroup rfl
  rw [e]
  exact completeSpace_manifoldWeakWhitney

end ContMDiffMap
