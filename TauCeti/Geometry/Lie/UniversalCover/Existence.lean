/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.UniversalCover
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Existence of universal covering Lie groups

A connected finite-dimensional real Lie group has a canonical simply connected covering group: the
universal cover of the identity, equipped with the smooth structure pulled back from the base.
This file packages the existing concrete construction into the existential interface used by
integration and descent arguments.
-/

public section

noncomputable section

open scoped ContDiff Manifold
open Topology

namespace TauCeti.UniversalCover

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G]
  [Group G] [LieGroup I ∞ G]

/-- A connected finite-dimensional real Lie group is covered by its simply connected universal
covering Lie group. The local path-connectedness and semilocal simple-connectedness needed by the
based-path construction are obtained from convex model neighborhoods and extended charts. The
covering homomorphism is the endpoint projection, with its smoothness, covering property, and
Lie-group laws supplied by the canonical construction and its pulled-back instances.
-/
theorem exists_universalCover [ConnectedSpace G] :
    ∃ (Gt : Type w) (_ : TopologicalSpace Gt) (_ : ChartedSpace H Gt)
      (_ : IsManifold I ∞ Gt) (_ : Group Gt) (_ : LieGroup I ∞ Gt) (p : Gt →* G)
      (hsmooth : ContMDiff I I ∞ (p : Gt → G)),
      SimplyConnectedSpace Gt ∧ IsCoveringMap (p : Gt → G) ∧
        Function.Bijective
          (lieMap (⟨p, hsmooth⟩ : ContMDiffMonoidMorphism I I ∞ Gt G)) := by
  let _ : LocallyPathConnectedSpace H := by
    have hconvex : Convex ℝ I.target := by
      rw [I.target_eq]
      exact I.convex_range
    let hI : ∀ x : H, I x ∈ I.target := fun x ↦ by
      rw [I.target_eq]
      exact ⟨x, rfl⟩
    let e : H ≃ₜ I.target :=
      { toFun := fun x ↦ ⟨I x, hI x⟩
        invFun := fun y ↦ I.symm y
        left_inv := fun x ↦ I.left_inv x
        right_inv := fun y ↦ by
          apply Subtype.ext
          have hy : (y : E) ∈ Set.range (I : H → E) := by
            rw [← I.target_eq]
            exact y.property
          exact I.right_inv hy
        continuous_toFun := I.continuous_toFun.codRestrict hI
        continuous_invFun := I.continuous_invFun.comp continuous_subtype_val }
    let _ : LocallyPathConnectedSpace I.target := hconvex.locallyPathConnectedSpace
    exact e.symm.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace H G
  let _ : SemilocallySimplyConnectedSpace G := by
    have hconvex : Convex ℝ I.target := by
      rw [I.target_eq]
      exact I.convex_range
    apply SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected
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
    have hs_sc : IsSimplyConnected s := by
      let _ : ContractibleSpace s := hs_convex.contractibleSpace hs_nonempty
      exact (SimplyConnectedSpace.ofContractible s : SimplyConnectedSpace s)
    let ce : PartialHomeomorph G E :=
      PartialHomeomorph.mk c (continuousOn_extChartAt x) (continuousOn_extChartAt_symm x)
    let d : Set G := ce.symm '' s
    have hd_sub : d ⊆ ce.source := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact ce.map_target (hs_sub hy)
    have hd_image : ce '' d = s := ce.image_symm_image_of_subset_target hs_sub
    let he : d ≃ₜ s := ce.homeomorphOfImageSubsetSource hd_sub hd_image
    have hd_sc : IsSimplyConnected d := by
      let _ : SimplyConnectedSpace s := hs_sc
      let _ : SimplyConnectedSpace d :=
        he.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
      exact (inferInstance : SimplyConnectedSpace d)
    have hd_nhds : d ∈ 𝓝 x := by
      have hsource : ce.source ∈ 𝓝 x :=
        (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
      have hball : Metric.ball (c x) r ∈ 𝓝 (c x) :=
        Metric.mem_nhds_iff.mpr ⟨r, hr, subset_rfl⟩
      have hpre : c ⁻¹' Metric.ball (c x) r ∈ 𝓝 x :=
        (continuousAt_extChartAt x).preimage_mem_nhds hball
      apply Filter.mem_of_superset (Filter.inter_mem hsource hpre)
      rintro z ⟨hzsource, hzb⟩
      change z ∈ ce.symm '' s
      have hzrange : ce z ∈ Set.range I :=
        extChartAt_target_subset_range x (ce.map_source hzsource)
      exact ⟨ce z, ⟨⟨hzb, hzrange⟩, ce.left_inv hzsource⟩⟩
    exact ⟨d, hd_nhds, hd_sc⟩
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : PathConnectedSpace G := PathConnectedSpace.of_locallyPathConnectedSpace
  let Gt := UniversalCover (1 : G)
  let p : Gt →* G := (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G)
  have hp : IsCoveringMap (p : Gt → G) := by
    -- The endpoint projection has distinct monoid-hom and continuous-map coercions;
    -- select the native coercion expected by its covering theorem.
    change IsCoveringMap (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G)
    exact UniversalCover.isCoveringMap_projHom
  have hsmooth : ContMDiff I I ∞ (p : Gt → G) := by
    dsimp [p]
    rw [UniversalCover.coe_projHom]
    exact UniversalCover.contMDiff_proj (x₀ := (1 : G))
  have hlie : Function.Bijective
      (lieMap (ContinuousMonoidHom.toContMDiffMonoidMorphism I I
        (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G))) :=
    UniversalCover.lieMap_projHom_bijective I G
  have hpm : (⟨p, hsmooth⟩ : ContMDiffMonoidMorphism I I ∞ Gt G) =
      ContinuousMonoidHom.toContMDiffMonoidMorphism I I
        (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G) := by
    apply DFunLike.coe_injective
    simp only [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
    funext x
    change p x = (UniversalCover.projHom : Gt → G) x
    rfl
  exact ⟨Gt, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, p, hsmooth,
    UniversalCover.simplyConnectedSpace (1 : G), hp, by rw [hpm]; exact hlie⟩

end TauCeti.UniversalCover
