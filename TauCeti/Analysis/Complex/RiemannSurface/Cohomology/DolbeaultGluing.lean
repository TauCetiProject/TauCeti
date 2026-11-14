/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
import TauCeti.Geometry.Manifold.PartitionOfUnity.CechSplitting

/-!
# Smooth data with holomorphic differences on a chart disc of a Riemann surface

Let `X` be a Riemann surface, and let `g k` be smooth functions on open sets `V k ⊆ X` whose
pairwise differences are holomorphic. On the preimage `B` of a disc under a holomorphic chart of
`X` (any member of the maximal atlas), covered by the `V k`, there
is one smooth `f` with every `f - g k` holomorphic on `B ∩ V k`. In the chart this is
`TauCeti.exists_contDiffOn_differentiableOn_sub_of_eball`, the Dolbeault lemma applied to the glued
conjugate Wirtinger derivatives.

Applied on each disc of a cover, this gives Forster, *Lectures on Riemann Surfaces*, 14.7: let
`V i ⊆ U i` be open, the `V i` covering `X` and each `U i` a chart disc. A holomorphic Čech
`1`-cocycle `ξ` on the `V i` splits smoothly, `ξ i j = g j - g i` (a partition of unity); the
lemma above on `U i` gives `f i` with `f i - g k` holomorphic, and then `ζ i j = f j - f i` is a
holomorphic cocycle on the `U i` with `ζ = ξ + δη` on the `V i`, where `η i = f i - g i`.
When `closure (V i)` is compact in `U i` and the `ξ k i` are bounded, `η i` is bounded on `V i`:
this is the estimate that lets the lifting be used on spaces of bounded or square-integrable
cochains in the proof that `H¹` of the structure sheaf of a compact Riemann surface is finite
dimensional (Forster §14.9).

## Main results

* `TauCeti.exists_contMDiffOn_mdifferentiableOn_sub_of_chart_eball`: the gluing on one chart disc.
* `TauCeti.exists_mdifferentiableOn_cocycle_eq_add_sub_of_chart_eball`: Forster §14.7, every
  holomorphic `1`-cocycle on the `V i` extends, up to a holomorphic coboundary, to a holomorphic
  `1`-cocycle on the chart discs `U i`.

Smoothness is for the underlying real manifold, modelled on `𝓘(ℝ, ℂ)` (see
`IsManifold.restrictScalars_of_ne_zero`); holomorphy is for the model `𝓘(ℂ)`.
-/

public section

open Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- **Smooth data with holomorphic differences glue on a chart disc.** Let `e` be a holomorphic
chart of `X` whose target contains the disc `eball c R`, `R ≤ ∞`, and write
`B = e.source ∩ e ⁻¹' eball c R` for its preimage in the chart source. If `g k` is smooth on the
open set `V k`, the `g k - g l` are holomorphic on `V k ∩ V l`, and the `V k` cover `B`, then
some `f`, smooth on `B`, has `f - g k` holomorphic on `B ∩ V k` for every `k`. -/
theorem exists_contMDiffOn_mdifferentiableOn_sub_of_chart_eball {ι : Type*} {V : ι → Set X}
    {g : ι → X → W} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {R : ℝ≥0∞}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hV : ∀ k, IsOpen (V k))
    (hg : ∀ k, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, W) ∞ (g k) (V k))
    (hgg : ∀ k l, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, W) (g k - g l) (V k ∩ V l))
    (hR : eball c R ⊆ e.target) (hcov : e.source ∩ e ⁻¹' eball c R ⊆ ⋃ k, V k) :
    ∃ f : X → W, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, W) ∞ f (e.source ∩ e ⁻¹' eball c R) ∧
      ∀ k, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, W) (f - g k) (e.source ∩ e ⁻¹' eball c R ∩ V k) := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ X := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  -- The chart is also a chart of the underlying real smooth surface.
  have heR : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero ∞ one_ne_zero he
  -- The data read in the chart.
  set Ω : ι → Set ℂ := fun k ↦ e.target ∩ e.symm ⁻¹' V k
  have hΩ (k : ι) : IsOpen (Ω k) := e.isOpen_inter_preimage_symm (hV k)
  have hg' (k : ι) : ContDiffOn ℝ ∞ (g k ∘ e.symm) (Ω k) :=
    ((hg k).comp ((contMDiffOn_symm_of_mem_maximalAtlas heR).mono inter_subset_left)
      fun _ hz ↦ hz.2).contDiffOn
  have hgg' (k l : ι) : DifferentiableOn ℂ (g k ∘ e.symm - g l ∘ e.symm) (Ω k ∩ Ω l) := by
    have := ((hgg k l).comp (((contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn
      one_ne_zero).mono inter_subset_left) fun _ hz ↦ hz.2).differentiableOn
    exact this.mono fun z hz ↦ ⟨hz.1.1, hz.1.2, hz.2.2⟩
  have hcov' : eball c R ⊆ ⋃ k, Ω k := fun z hz ↦ by
    have hzt := hR hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 <| hcov
      ⟨e.map_target hzt, by simpa only [mem_preimage, e.right_inv hzt] using hz⟩
    exact mem_iUnion.2 ⟨k, hzt, hk⟩
  obtain ⟨F, hF, hFg⟩ := exists_contDiffOn_differentiableOn_sub_of_eball hΩ hg' hgg' hcov'
  refine ⟨F ∘ e, hF.contMDiffOn.comp ((contMDiffOn_of_mem_maximalAtlas heR).mono
    inter_subset_left) fun _ hy ↦ hy.2, fun k ↦ ?_⟩
  have hmaps : MapsTo e (e.source ∩ e ⁻¹' eball c R ∩ V k) (eball c R ∩ Ω k) :=
    fun y hy ↦ ⟨hy.1.2, e.map_source hy.1.1, by simpa [e.left_inv hy.1.1] using hy.2⟩
  refine ((hFg k).mdifferentiableOn.comp (((contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn
    one_ne_zero).mono fun y (hy : y ∈ e.source ∩ e ⁻¹' eball c R ∩ V k) ↦ hy.1.1) hmaps).congr
    fun y hy ↦ ?_
  simp [e.left_inv hy.1.1]

/-- **Holomorphic cocycles extend to larger chart discs up to a coboundary** (Forster §14.7). Let
`X` be a Hausdorff σ-compact Riemann surface, `U i = (e i).source ∩ e i ⁻¹' eball (c i) (R i)`
the preimage of a disc `eball (c i) (R i)`, `R i ≤ ∞`, lying in the target of a holomorphic chart
`e i`, and `V i ⊆ U i` open sets covering `X`. Every holomorphic Čech `1`-cocycle `ξ` on the
`V i` is `ζ + δ(-η)` there, for a holomorphic `1`-cocycle `ζ` on the `U i` and holomorphic `η i`
on `V i`. Moreover `η i` is bounded on `V i`
when `closure (V i)` is compact and contained in `U i` and all `ξ k i` are bounded on
`V k ∩ V i` by one constant. -/
theorem exists_mdifferentiableOn_cocycle_eq_add_sub_of_chart_eball [T2Space X]
    [SigmaCompactSpace X] {ι : Type*} {e : ι → OpenPartialHomeomorph X ℂ} {c : ι → ℂ}
    {R : ι → ℝ≥0∞} {U V : ι → Set X} (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hU : ∀ i, U i = (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U i) (hVcov : ⋃ i, V i = univ)
    {ξ : ι → ι → X → W} (hξ : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, W) (ξ i j) (V i ∩ V j))
    (hcocycle : ∀ i j k, ∀ y ∈ V i ∩ V j ∩ V k, ξ i j y + ξ j k y = ξ i k y) :
    ∃ ζ : ι → ι → X → W, ∃ η : ι → X → W,
      (∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, W) (ζ i j) (U i ∩ U j)) ∧
      (∀ i j k, ∀ y ∈ U i ∩ U j ∩ U k, ζ i j y + ζ j k y = ζ i k y) ∧
      (∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, W) (η i) (V i)) ∧
      (∀ i j, ∀ y ∈ V i ∩ V j, ζ i j y = ξ i j y + η j y - η i y) ∧
      ∀ i (C : ℝ), (∀ k, ∀ y ∈ V k ∩ V i, ‖ξ k i y‖ ≤ C) → IsCompact (closure (V i)) →
        closure (V i) ⊆ U i → ∃ C', ∀ y ∈ V i, ‖η i y‖ ≤ C' := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ X := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  -- A smooth splitting `ξ i j = g j - g i` of the cocycle.
  have hξs (i j : ι) : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, W) (⊤ : ℕ∞) (ξ i j) (V i ∩ V j) := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((hξ i j).contMDiffOn ((hV i).inter (hV j)) (n := ∞)).restrictScalars ℝ
  obtain ⟨g, hg, hξg, hgC⟩ := exists_contMDiffOn_eq_sub_of_cocycle hV hVcov hξs hcocycle
  have hgg (k l : ι) : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, W) (g k - g l) (V k ∩ V l) :=
    ((hξ l k).mono (inter_comm _ _).le).congr fun y hy ↦ by
      simp [hξg l k y ⟨hy.2, hy.1⟩]
  -- On each disc `U i`, one smooth `f i` with every `f i - g k` holomorphic.
  have hf (i : ι) := exists_contMDiffOn_mdifferentiableOn_sub_of_chart_eball (he i) hV hg hgg
    (hR i) (by simp [hVcov])
  choose f hfs hfg using hf
  simp only [← hU] at hfs hfg
  refine ⟨fun i j ↦ f j - f i, fun i ↦ f i - g i, fun i j y hy ↦ ?_, fun i j k y _ ↦ ?_,
    fun i ↦ (hfg i i).mono fun y hy ↦ ⟨hVU i hy, hy⟩, fun i j y hy ↦ ?_,
    fun i C hC hVc hVU' ↦ ?_⟩
  · -- Near `y ∈ V k`, `f j - f i = (f j - g k) - (f i - g k)`.
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hVcov.ge (mem_univ y))
    have hUo (l : ι) : IsOpen (U l) := hU l ▸ (e l).isOpen_inter_preimage isOpen_eball
    have hs : U i ∩ U j ∩ V k ∈ 𝓝 y := (((hUo i).inter (hUo j)).inter (hV k)).mem_nhds ⟨hy, hk⟩
    have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, W) (f j - g k - (f i - g k)) (U i ∩ U j ∩ V k) :=
      ((hfg j k).mono fun z (hz : z ∈ U i ∩ U j ∩ V k) ↦ ⟨hz.1.2, hz.2⟩).sub
        ((hfg i k).mono fun z (hz : z ∈ U i ∩ U j ∩ V k) ↦ ⟨hz.1.1, hz.2⟩)
    exact ((hd.congr fun z _ ↦ by simp).mdifferentiableAt hs).mdifferentiableWithinAt
  · simp
  · simp [hξg i j y hy]
  · -- `η i = f i - g i`, with `f i` continuous on `U i ⊇ closure (V i)` and `‖g i‖ ≤ C`.
    obtain ⟨C', hC'⟩ := hVc.exists_bound_of_continuousOn ((hfs i).continuousOn.mono hVU')
    exact ⟨C' + C, fun y hy ↦ (norm_sub_le (f i y) (g i y)).trans
      (add_le_add (hC' y (subset_closure hy)) (hgC i C hC y hy))⟩

end TauCeti
