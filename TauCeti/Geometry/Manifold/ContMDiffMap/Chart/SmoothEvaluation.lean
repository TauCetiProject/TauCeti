/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import TauCeti.Analysis.Calculus.ContDiff.OperatorFamily

/-!
# Evaluation on the Banach space of `C^k` maps is `C^k`

Let `M` be a boundaryless manifold modelled on a locally compact space over `ℝ` or `ℂ`, and give
the vector-valued `C^k` maps on `M` the norm of a finite chart atlas whose compact pieces have
relative interiors covering `M` (`ContMDiffMap.finiteAtlasNormedAddCommGroup`). This file proves
that the evaluation map `(f, x) ↦ f x` is `C^k` on the product of this normed space with `M`
(`ContMDiffMap.contMDiff_eval_finiteAtlas`).

The regularity is sharp, and it is better than what composition with the dual space gives: for
the `C^k` norm, `x ↦ (f ↦ f x)` is in general only `C^(k - 1)` into the dual space, because the
`k`th derivatives of the unit ball are not equicontinuous. In a chart the statement is the joint
regularity theorem for pointwise smooth families of operators,
`TauCeti.contDiffOn_apply_of_forall_norm_iteratedFDeriv_le`, applied to evaluation at the points
of the chart: the finite-atlas norm bounds the coordinate derivatives of order at most `k` on
every compact subset of a chart target.

Joint regularity of evaluation is what makes universal constructions over spaces of `C^k` maps
smooth, such as the section `(f, x) ↦ df_x` over the product of `C^k` functions on a compact
manifold with the manifold, whose regular zeros give Morse functions by the Sard–Smale theorem.

## Main results

* `ContMDiffMap.exists_norm_iteratedFDeriv_extChartAt_symm_le`: near each point of a chart target,
  the finite-atlas norm bounds the coordinate derivatives of order at most `k`.
* `ContMDiffMap.contMDiff_eval_finiteAtlas`: evaluation is `C^k` for the finite-atlas `C^k` norm.

## References

* R. Abraham and J. Robbin, *Transversal mappings and flows*, W. A. Benjamin, 1967, Chapter II
  (the evaluation map of a space of `C^k` maps is `C^k`).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} [Fintype ι] {c : ι → M}
  {K : ∀ i, TopologicalSpace.Compacts (extChartAt I (c i)).target}
  (k : ℕ) [IsManifold I k M]
  (hK : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (c i)).source,
    (⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ :
      (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

omit [IsRCLikeNormedField 𝕜] in
include hK in
/-- **Coordinate derivatives are locally bounded by the finite-atlas norm.** Near each point of a
chart target, the coordinate derivatives of order at most `k` of the vector-valued `C^k` maps are
bounded by one multiple of their finite-atlas seminorms. -/
theorem exists_norm_iteratedFDeriv_extChartAt_symm_le (x : M) {w₀ : E}
    (hw₀ : w₀ ∈ (extChartAt I x).target) {m : ℕ} (hm : m ≤ k) :
    ∃ C, ∀ᶠ z in 𝓝 w₀, ∀ f : C^k⟮I, M; 𝓘(𝕜, F), F⟯,
      ‖iteratedFDeriv 𝕜 m (fun w ↦ f ((extChartAt I x).symm w)) z‖ ≤
        C * finiteAtlasSeminorm c K k le_rfl f := by
  have ht : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  -- A compact neighbourhood of `w₀` in the chart target gives a compact chart seminorm.
  obtain ⟨L, hL, hw₀L, hLt⟩ := exists_compact_subset ht hw₀
  let L' : TopologicalSpace.Compacts (extChartAt I x).target := ⟨Subtype.val ⁻¹' L,
    Topology.IsEmbedding.subtypeVal.isCompact_iff.2 (by
      rwa [Subtype.image_preimage_coe, inter_eq_right.2 hLt])⟩
  obtain ⟨C, -, hC⟩ := exists_chartCkSeminorm_le_finiteAtlasSeminorm (F := F) hK x L' k le_rfl
  refine ⟨C, ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.1 hw₀L] with z hz f
  have hz' := (chartCkSeminorm_le_iff x L' k le_rfl f (apply_nonneg _ _)).mp le_rfl m hm
    ⟨z, hLt hz⟩ hz
  rw [chartIteratedFDeriv_self_target_apply, iteratedFDerivWithin_of_isOpen m ht (hLt hz)]
    at hz'
  exact hz'.trans (hC f)

include hK in
/-- **Evaluation is `C^k`.** Let `M` be a boundaryless manifold modelled on a locally compact
space, and give the vector-valued `C^k` maps on `M` the norm of a finite atlas whose compact pieces
have relative interiors covering `M`. Then the evaluation map `(f, x) ↦ f x` is `C^k` on the
product of this normed space with `M`. -/
theorem contMDiff_eval_finiteAtlas :
    letI := finiteAtlasNormedAddCommGroup (F := F) k hK
    letI := finiteAtlasNormedSpace (F := F) k hK
    ContMDiff (𝓘(𝕜, C^k⟮I, M; 𝓘(𝕜, F), F⟯).prod I) 𝓘(𝕜, F) k
      (fun p : C^k⟮I, M; 𝓘(𝕜, F), F⟯ × M ↦ p.1 p.2) := by
  let := finiteAtlasNormedAddCommGroup (F := F) k hK
  let := finiteAtlasNormedSpace (F := F) k hK
  have hnorm (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯) : ‖f‖ = finiteAtlasSeminorm c K k le_rfl f :=
    norm_finiteAtlas k hK f
  rintro ⟨f₀, x₀⟩
  set φ := extChartAt I x₀
  have hφt : IsOpen φ.target := isOpen_extChartAt_target x₀
  -- Evaluation at the points of the chart, as a family of continuous linear maps.
  let Φ : E → C^k⟮I, M; 𝓘(𝕜, F), F⟯ →L[𝕜] F := fun w ↦
    LinearMap.mkContinuous
      { toFun := fun f ↦ f (φ.symm w)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl } 1 fun f ↦ by
      rw [one_mul, hnorm]
      exact norm_apply_le_finiteAtlasSeminorm
        (fun y ↦ (hK y).imp fun _ ⟨hy, hyK⟩ ↦ ⟨hy, interior_subset hyK⟩) k le_rfl f (φ.symm w)
  have hΦ (w : E) (f : C^k⟮I, M; 𝓘(𝕜, F), F⟯) : Φ w f = f (φ.symm w) := rfl
  have hbd : ∀ m ≤ k, ∀ w₀ ∈ φ.target, ∃ C, ∀ᶠ z in 𝓝 w₀, ∀ f : C^k⟮I, M; 𝓘(𝕜, F), F⟯,
      ‖iteratedFDeriv 𝕜 m (fun w ↦ Φ w f) z‖ ≤ C * ‖f‖ := fun m hm w₀ hw₀ ↦ by
    simpa only [hΦ, hnorm] using exists_norm_iteratedFDeriv_extChartAt_symm_le k hK x₀ hw₀ hm
  have hG := TauCeti.contDiffOn_apply_of_forall_norm_iteratedFDeriv_le hφt
    (fun f ↦ (f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀)).contDiffOn) hbd
  -- Near `(f₀, x₀)`, evaluation is the composite of `(f, x) ↦ (f, φ x)` and this smooth map.
  have hfst : ContMDiffAt (𝓘(𝕜, C^k⟮I, M; 𝓘(𝕜, F), F⟯).prod I) 𝓘(𝕜, C^k⟮I, M; 𝓘(𝕜, F), F⟯) k
      Prod.fst (f₀, x₀) := contMDiffAt_fst
  have hsnd : ContMDiffAt (𝓘(𝕜, C^k⟮I, M; 𝓘(𝕜, F), F⟯).prod I) 𝓘(𝕜, E) k
      (fun p : C^k⟮I, M; 𝓘(𝕜, F), F⟯ × M ↦ φ p.2) (f₀, x₀) :=
    contMDiffAt_extChartAt.comp (f₀, x₀) contMDiffAt_snd
  have hGa : ContMDiffAt 𝓘(𝕜, C^k⟮I, M; 𝓘(𝕜, F), F⟯ × E) 𝓘(𝕜, F) k
      (fun p : C^k⟮I, M; 𝓘(𝕜, F), F⟯ × E ↦ Φ p.2 p.1) (f₀, φ x₀) :=
    (hG.contDiffAt ((isOpen_univ.prod hφt).mem_nhds
      ⟨mem_univ f₀, mem_extChartAt_target x₀⟩)).contMDiffAt
  refine (hGa.comp (f₀, x₀) (hfst.prodMk_space hsnd)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_univ.prod (isOpen_extChartAt_source (I := I) x₀)).mem_nhds
    ⟨mem_univ f₀, mem_extChartAt_source (I := I) x₀⟩] with p hp
  simp only [Function.comp_apply, hΦ, φ.left_inv hp.2]

end ContMDiffMap
