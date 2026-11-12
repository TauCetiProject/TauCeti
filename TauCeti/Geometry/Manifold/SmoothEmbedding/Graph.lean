/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Immersion.Graph

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
