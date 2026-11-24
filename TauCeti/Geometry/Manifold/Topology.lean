/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import TauCeti.Analysis.Convex.SimplyConnected
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
import TauCeti.AlgebraicTopology.UniversalCover.Countable

/-!
# Local topology of real manifolds

The convex model range makes charted spaces locally path-connected; nonempty preconnected
charted spaces are therefore path-connected. Extended charts also provide convex-image open
neighbourhood bases (`ModelWithCorners.isBasis_convex_image_extChartAt`) and simply connected
neighbourhoods, so real manifolds are semilocally simply connected. In a second-countable
charted space this implies countability of the fundamental group
(`ModelWithCorners.countable_fundamentalGroup`).
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

/-- A charted space modelled on a model with corners is locally path-connected. -/
theorem locallyPathConnectedSpace_of_chartedSpace (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] : LocallyPathConnectedSpace M := by
  let : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

/-- A nonempty preconnected charted space modelled on a model with corners is path-connected. -/
theorem pathConnectedSpace (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [PreconnectedSpace M] [Nonempty M] :
    PathConnectedSpace M := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : ConnectedSpace M := ⟨inferInstance⟩
  exact PathConnectedSpace.of_locallyPathConnectedSpace

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

/-- The source `(extChartAt I x).source` of the extended chart at `x`, bundled as an open subset of
`M`. -/
abbrev extChartAtOpens (I : ModelWithCorners 𝕜 E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (x : M) : TopologicalSpace.Opens M :=
  ⟨(extChartAt I x).source, isOpen_extChartAt_source x⟩

/-- For any point `x` of a charted space `M` modelled on a model with corners `I`, the open subsets
of `(extChartAt I x).source` whose image under `extChartAt I x` is convex over `ℝ` form a basis for
the topology of `(extChartAt I x).source`. -/
theorem isBasis_convex_image_extChartAt (I : ModelWithCorners 𝕜 E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    TopologicalSpace.Opens.IsBasis
      {V : TopologicalSpace.Opens (I.extChartAtOpens x) |
        Convex ℝ ((fun y : I.extChartAtOpens x ↦ extChartAt I x y.val) '' (V : Set _))} := by
  let φ : I.extChartAtOpens x → E := fun y ↦ extChartAt I x y.val
  have hφ : Continuous φ :=
    (continuousOn_extChartAt (I := I) x).comp_continuous continuous_subtypeVal fun y ↦ y.property
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.2 fun {U y} hy ↦ ?_
  have hUM : IsOpen (Subtype.val '' (U : Set (I.extChartAtOpens x))) :=
    (I.extChartAtOpens x).isOpen.isOpenMap_subtypeVal _ U.isOpen
  have hpre : (extChartAt I x).symm ⁻¹' (Subtype.val '' (U : Set (I.extChartAtOpens x))) ∈
      𝓝 (φ y) :=
    (continuousAt_extChartAt_symm' y.property).preimage_mem_nhds
      (hUM.mem_nhds ⟨y, hy, ((extChartAt I x).left_inv y.property).symm⟩)
  obtain ⟨r, hr_pos, hr⟩ := Metric.mem_nhdsWithin_iff.1
    (Filter.inter_mem (extChartAt_target_mem_nhdsWithin' y.property) (nhdsWithin_le_nhds hpre))
  let V : TopologicalSpace.Opens (I.extChartAtOpens x) :=
    ⟨φ ⁻¹' Metric.ball (φ y) r, Metric.isOpen_ball.preimage hφ⟩
  have hV_im : φ '' (V : Set _) = Metric.ball (φ y) r ∩ Set.range I := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨hz, extChartAt_target_subset_range x ((extChartAt I x).map_source z.property)⟩
    · rintro v hv
      have hv_tgt : v ∈ (extChartAt I x).target := (hr hv).1
      have hφ_symm : φ ⟨(extChartAt I x).symm v, (extChartAt I x).map_target hv_tgt⟩ = v :=
        (extChartAt I x).right_inv hv_tgt
      exact ⟨⟨(extChartAt I x).symm v, (extChartAt I x).map_target hv_tgt⟩,
        Set.mem_preimage.2 (hφ_symm.symm ▸ hv.1), hφ_symm⟩
  refine ⟨V, ?_, Metric.mem_ball_self hr_pos, fun z hz ↦ ?_⟩
  · rw [Set.mem_ofPred_eq]
    dsimp only [φ] at hV_im
    rw [hV_im]
    exact (convex_ball (φ y) r).inter I.convex_range
  · have hz_mem :=
      (hr ⟨hz, extChartAt_target_subset_range x ((extChartAt I x).map_source z.property)⟩).2
    rw [Set.mem_preimage, (extChartAt I x).left_inv z.property] at hz_mem
    obtain ⟨w, hwU, hw⟩ := hz_mem
    exact Subtype.ext hw ▸ hwU

/-- A second-countable manifold has countable fundamental group. -/
theorem countable_fundamentalGroup (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [SecondCountableTopology M] (x₀ : M) :
    Countable (FundamentalGroup M x₀) :=
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  TauCeti.countable_fundamentalGroup x₀

end ModelWithCorners
