/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Smooth embeddings given by graphs

The graph parametrization of a `Cⁿ` map between boundaryless manifolds is a `Cⁿ` embedding,
with the target model of the original map as a uniform complement. The model spaces may be
infinite dimensional and the original map need not be injective. In charts, the shear
`(u, w) ↦ (u, w - g u)` straightens the graph of `g` to `u ↦ (u, 0)`.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

/-- In model spaces, the graph of a `Cⁿ` map on an open set is an immersion with complement
`F` at every point of that set, straightened by the shear `(u, w) ↦ (u, w - g u)`. -/
private theorem ContDiffOn.isImmersionAtOfComplement_graph {g : E → F} {s : Set E}
    (hg : ContDiffOn 𝕜 n g s) (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    Manifold.IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E × F) n (fun u ↦ (u, g u)) x := by
  have ht : IsOpen (Prod.fst ⁻¹' s : Set (E × F)) := hs.preimage continuous_fst
  have hg' : ContDiffOn 𝕜 n (fun p : E × F ↦ g p.1) (Prod.fst ⁻¹' s) :=
    hg.comp contDiff_fst.contDiffOn fun _ hp ↦ hp
  let ψ : OpenPartialHomeomorph (E × F) (E × F) :=
    { toFun := fun p ↦ (p.1, p.2 - g p.1)
      invFun := fun p ↦ (p.1, p.2 + g p.1)
      source := Prod.fst ⁻¹' s
      target := Prod.fst ⁻¹' s
      map_source' := fun _ hp ↦ hp
      map_target' := fun _ hp ↦ hp
      left_inv' := fun p _ ↦ by simp
      right_inv' := fun p _ ↦ by simp
      open_source := ht
      open_target := ht
      continuousOn_toFun :=
        continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.sub hg'.continuousOn)
      continuousOn_invFun :=
        continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.add hg'.continuousOn) }
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E × F) n (E × F) :=
    ψ.mem_maximalAtlas_of_contMDiffOn
      (contMDiffOn_iff_contDiffOn.mpr
        (contDiff_fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.sub hg')))
      (contMDiffOn_iff_contDiffOn.mpr
        (contDiff_fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.add hg')))
  let φ := (OpenPartialHomeomorph.refl E).restrOpen s hs
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts (ContinuousLinearEquiv.refl 𝕜 (E × F))
    φ ψ (by simpa [φ] using hx) hx
    (φ.mem_maximalAtlas_of_contMDiffOn contMDiffOn_id contMDiffOn_id) hψ
    (fun _ hy ↦ by simpa [φ, ψ] using hy) ?_
  intro u _
  simp [φ, ψ]

/-- The graph of a `Cⁿ` map is a `Cⁿ` embedding, even for noninjective maps. -/
theorem ContMDiff.isSmoothEmbedding_graph [IsManifold I n M] [IsManifold J n N] {f : M → N}
    (hf : ContMDiff I J n f) :
    Manifold.IsSmoothEmbedding I (I.prod J) n (fun x ↦ (x, f x)) := by
  refine ⟨Manifold.IsImmersionOfComplement.isImmersion (F := F) fun x ↦ ?_,
    isEmbedding_graph hf.continuous⟩
  -- Read `f` in the preferred extended charts, on an open set around the chart image of `x`.
  let t := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt J (f x)).source)
  have ht : IsOpen t :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source (f x)))
  have hxt : extChartAt I x x ∈ t := ⟨mem_extChartAt_target x, by simp⟩
  have hft : ContDiffOn 𝕜 n (writtenInExtChartAt I J x f) t := by
    simpa [t] using (contMDiffOn_iff.mp (hf.contMDiffOn (s := Set.univ))).2 x (f x)
  refine Manifold.IsImmersionAtOfComplement.of_writtenInExtChartAt
    (continuous_id.prodMk hf.continuous).continuousAt
    ((hft.isImmersionAtOfComplement_graph ht hxt).congr_of_eventuallyEq ?_)
  -- In the product chart, the graph of `f` is the graph of `f` read in charts.
  filter_upwards [extChartAt_target_mem_nhds x] with u hu
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [extChartAt_prod]
  exact Prod.ext ((extChartAt I x).right_inv hu).symm rfl
