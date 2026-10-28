/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import TauCeti.Analysis.Convex.SimplyConnected
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic

/-!
# Local topology of real manifolds

The convex model range gives the local path-connectedness needed by manifold charts. Extended
charts also provide simply connected neighbourhoods, so real manifolds are
semilocally simply connected.
-/

public section

noncomputable section

open scoped ContDiff Manifold
open Topology

universe u v

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H]

/-- The model space of a model with corners is locally path-connected. -/
theorem locallyPathConnectedSpace (I : ModelWithCorners 𝕜 E H) : LocallyPathConnectedSpace H := by
  let _ : LocallyPathConnectedSpace (Set.range I) := I.convex_range.locallyPathConnectedSpace
  exact I.isClosedEmbedding.isEmbedding.toHomeomorph.symm.locallyPathConnectedSpace

/-- A charted space modelled on `H`, where `I : ModelWithCorners 𝕜 E H`, is semilocally
simply connected. -/
theorem semilocallySimplyConnectedSpace (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :
    TauCeti.SemilocallySimplyConnectedSpace M := by
  apply TauCeti.SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected
  intro x
  let c := extChartAt I x
  have hy : c x ∈ Set.range I := extChartAt_target_subset_range x (mem_extChartAt_target x)
  have htarget : c.target ∈ 𝓝[Set.range I] (c x) := extChartAt_target_mem_nhdsWithin x
  obtain ⟨u, hu, hu_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp htarget
  obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhds_iff.mp hu
  let s : Set E := Metric.ball (c x) r ∩ Set.range I
  have hs_sub : s ⊆ c.target := by
    intro z hz
    exact hu_sub ⟨hr_sub hz.1, hz.2⟩
  have hs_convex : Convex ℝ s := convex_ball _ _ |>.inter I.convex_range
  have hs_nonempty : s.Nonempty := ⟨c x, ⟨Metric.mem_ball_self hr, hy⟩⟩
  have hs_sc : IsSimplyConnected s := hs_convex.isSimplyConnected hs_nonempty
  let ce : PartialHomeomorph M E :=
    PartialHomeomorph.mk c (continuousOn_extChartAt x) (continuousOn_extChartAt_symm x)
  let d : Set M := ce.symm '' s
  have hd_sub : d ⊆ ce.source := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ce.map_target (hs_sub hy)
  have hd_image : ce '' d = s := ce.image_symm_image_of_subset_target hs_sub
  let he : d ≃ₜ s := ce.homeomorphOfImageSubsetSource hd_sub hd_image
  have hd_sc : IsSimplyConnected d := he.toHomotopyEquiv.simplyConnectedSpace_iff.mpr hs_sc
  have hd_nhds : d ∈ 𝓝 x := by
    have hsource : ce.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
    have hpre : c ⁻¹' s ∈ 𝓝 x := by
      apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin
        (I := I) (x := x) (x' := x) (mem_extChartAt_source x)
      simp only [s]
      rw [Set.inter_comm]
      exact inter_mem_nhdsWithin (Set.range I) (Metric.ball_mem_nhds (c x) hr)
    apply Filter.mem_of_superset (Filter.inter_mem hsource hpre)
    rintro z ⟨hzsource, hzc⟩
    dsimp only [d]
    have hce : (ce : M → E) = c := by
      exact PartialHomeomorph.coe_mk c _ _
    have hzc' : ce z ∈ s := by
      rw [hce]
      exact hzc
    exact ⟨ce z, ⟨hzc', ce.left_inv hzsource⟩⟩
  exact ⟨d, hd_nhds, hd_sc⟩

end ModelWithCorners
