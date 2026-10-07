/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean

/-!
# Closed normal discs and their boundary spheres

For a compact embedded submanifold of a Euclidean space, a sufficiently small closed normal
disc bundle embeds as a compact neighbourhood of the submanifold. Its boundary is the image
of the corresponding normal sphere bundle. These are the closed neighbourhoods removed in
surgery: the open normal tube has the closed disc image as its closure, and the sphere image
as its frontier.

The disc and sphere bundles here are subsets of `M × V`, with the subspace topology, using
`normalSubspace`. No trivialization or choice of a normal frame is required. The construction
uses `exists_isOpenEmbedding_normalTube`, following J. M. Lee, *Introduction to Smooth
Manifolds*, 2nd ed., Theorem 6.24, and M. W. Hirsch, *Differential Topology*, Chapter 4,
Theorem 6.3.
-/

public section

open Set Function Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {V E H M : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

variable (I) in
/-- The closed normal disc bundle of radius `ε`, with fibres in the ambient inner product
space. -/
def normalDiscBundle (f : M → V) (ε : ℝ) : Set (M × V) :=
  {p | p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ ≤ ε}

variable (I) in
/-- The normal sphere bundle of radius `ε`, with fibres in the ambient inner product space. -/
def normalSphereBundle (f : M → V) (ε : ℝ) : Set (M × V) :=
  {p | p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ = ε}

@[simp] theorem mem_normalDiscBundle {f : M → V} {ε : ℝ} {p : M × V} :
    p ∈ normalDiscBundle I f ε ↔ p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ ≤ ε :=
  Iff.rfl

@[simp] theorem mem_normalSphereBundle {f : M → V} {ε : ℝ} {p : M × V} :
    p ∈ normalSphereBundle I f ε ↔ p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ = ε :=
  Iff.rfl

/-- Removing the open normal tube from the closed normal disc bundle leaves the normal
sphere bundle. -/
@[simp] theorem normalDiscBundle_sdiff_normalTube (f : M → V) (ε : ℝ) :
    normalDiscBundle I f ε \ normalTube I f ε = normalSphereBundle I f ε := by
  ext p
  simp only [Set.mem_sdiff, mem_normalDiscBundle, mem_normalTube, mem_normalSphereBundle]
  grind

/-- Restricting an embedded normal tube to a smaller radius preserves its open embedding. -/
theorem isOpenEmbedding_normalTube_of_le {f : M → V} {ε R : ℝ} (hεR : ε ≤ R)
    (h : IsOpenEmbedding ((normalTube I f R).domRestrict fun p : M × V => f p.1 + p.2)) :
    IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2) := by
  have hsub : normalTube I f ε ⊆ normalTube I f R := fun p hp =>
    mem_normalTube.mpr ⟨(mem_normalTube.mp hp).1, (mem_normalTube.mp hp).2.trans_le hεR⟩
  apply h.comp (IsOpenEmbedding.inclusion hsub ?_)
  convert isOpen_lt ((continuous_norm.comp continuous_snd).comp
    (continuous_subtype_val : Continuous (Subtype.val : normalTube I f R → M × V)))
    (continuous_const : Continuous fun _ : normalTube I f R => ε) using 1
  ext p
  simp only [mem_preimage, mem_normalTube, mem_ofPred_eq, Function.comp_apply]
  exact and_iff_right (mem_normalTube.mp p.2).1

section Regularity

variable [I.Boundaryless] [IsManifold I 1 M] {f : M → V}

/-- The normal vectors of a `C¹` map form a closed subset of `M × V`. No immersion
hypothesis is needed. -/
theorem isClosed_setOf_mem_normalSubspace (hf : ContMDiff I 𝓘(ℝ, V) 1 f) :
    IsClosed {p : M × V | p.2 ∈ normalSubspace I f p.1} := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x, v⟩ hp
  set e := extChartAt I x
  set g : E → V := f ∘ e.symm
  have hgd : ContDiffOn ℝ 1 g e.target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))
  have hgat : ∀ u ∈ e.target, ContDiffAt ℝ 1 g u := fun u hu =>
    hgd.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hu)
  have hnormal : ∀ y ∈ e.source,
      normalSubspace I f y = (fderiv ℝ g (e y)).rangeᗮ := fun y hy =>
    normalSubspace_eq_of_mem_source hy
      ((hgat _ (e.map_source hy)).differentiableAt one_ne_zero)
  have hx : x ∈ e.source := mem_extChartAt_source x
  have hnot : v ∉ (fderiv ℝ g (e x)).rangeᗮ := by
    rw [← hnormal x hx]
    exact hp
  obtain ⟨u, hu⟩ : ∃ u : E, ⟪v, fderiv ℝ g (e x) u⟫_ℝ ≠ 0 := by
    contrapose! hnot
    exact fun _ ⟨u, hu⟩ => hu ▸ inner_eq_zero_symm.mp (hnot u)
  have hec : ContinuousAt e x :=
    (continuousOn_extChartAt x).continuousAt ((isOpen_extChartAt_source x).mem_nhds hx)
  have hA : ContinuousAt (fun p : M × V => fderiv ℝ g (e p.1)) (x, v) :=
    ((hgat _ (e.map_source hx)).fderiv_right (m := 0) (by norm_num)).continuousAt.comp (x := (x, v))
      (hec.comp (x := (x, v)) continuousAt_fst)
  have hc : ContinuousAt (fun p : M × V => ⟪p.2, fderiv ℝ g (e p.1) u⟫_ℝ) (x, v) :=
    continuousAt_snd.inner (hA.clm_apply continuousAt_const)
  have hne := hc.preimage_mem_nhds (isOpen_ne.mem_nhds hu)
  have hsrc : ∀ᶠ p : M × V in 𝓝 (x, v), p.1 ∈ e.source :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_source x).mem_nhds hx)
  filter_upwards [hne, hsrc] with p hpne hpsrc
  intro hpnormal
  simp only [mem_ofPred_eq] at hpnormal
  rw [hnormal p.1 hpsrc] at hpnormal
  exact hpne (Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self _ u) hpnormal)

/-- The closed normal disc bundle of a `C¹` map is closed in `M × V`. -/
theorem isClosed_normalDiscBundle (hf : ContMDiff I 𝓘(ℝ, V) 1 f) (ε : ℝ) :
    IsClosed (normalDiscBundle I f ε) :=
  (isClosed_setOf_mem_normalSubspace hf).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)

/-- The normal sphere bundle of a `C¹` map is closed in `M × V`. -/
theorem isClosed_normalSphereBundle (hf : ContMDiff I 𝓘(ℝ, V) 1 f) (ε : ℝ) :
    IsClosed (normalSphereBundle I f ε) :=
  (isClosed_setOf_mem_normalSubspace hf).inter
    (isClosed_eq (continuous_norm.comp continuous_snd) continuous_const)

/-- The closure of a positive-radius open normal tube is the closed normal disc bundle. -/
theorem closure_normalTube (hf : ContMDiff I 𝓘(ℝ, V) 1 f) {ε : ℝ} (hε : 0 < ε) :
    closure (normalTube I f ε) = normalDiscBundle I f ε := by
  refine subset_antisymm
    (closure_minimal (fun _ hp => ⟨(mem_normalTube.mp hp).1, (mem_normalTube.mp hp).2.le⟩)
      (isClosed_normalDiscBundle hf ε)) ?_
  rintro ⟨x, v⟩ ⟨hv, hnorm⟩
  let w : normalSubspace I f x := ⟨v, hv⟩
  have hw : w ∈ closure (Metric.ball 0 ε) := by
    rw [closure_ball _ hε.ne']
    exact mem_closedBall_zero_iff.mpr hnorm
  have hc : Continuous fun u : normalSubspace I f x => (x, (u : V)) :=
    continuous_const.prodMk continuous_subtype_val
  have hsub : (fun u : normalSubspace I f x => (x, (u : V))) '' Metric.ball 0 ε ⊆
      normalTube I f ε := by
    rintro _ ⟨u, hu, rfl⟩
    exact mem_normalTube.mpr ⟨u.2, mem_ball_zero_iff.mp hu⟩
  exact closure_mono hsub (mem_closure_image (hc.continuousAt (x := w)) hw)

variable [FiniteDimensional ℝ V] [CompactSpace M]

/-- A closed normal disc bundle over a compact manifold is compact. -/
theorem isCompact_normalDiscBundle (hf : ContMDiff I 𝓘(ℝ, V) 1 f) (ε : ℝ) :
    IsCompact (normalDiscBundle I f ε) := by
  apply (isCompact_univ.prod (isCompact_closedBall (0 : V) ε)).of_isClosed_subset
    (isClosed_normalDiscBundle hf ε)
  exact fun p hp => ⟨mem_univ _, mem_closedBall_zero_iff.mpr hp.2⟩

/-- For a compact core, the closure of the image of the open normal tube is the image of
its closed normal disc bundle. This does not require injectivity of the normal map. -/
theorem closure_image_normalTube (hf : ContMDiff I 𝓘(ℝ, V) 1 f) {ε : ℝ} (hε : 0 < ε) :
    closure ((fun p : M × V => f p.1 + p.2) '' normalTube I f ε) =
      (fun p : M × V => f p.1 + p.2) '' normalDiscBundle I f ε := by
  have hc : Continuous fun p : M × V => f p.1 + p.2 :=
    (hf.continuous.comp continuous_fst).add continuous_snd
  refine subset_antisymm (closure_minimal (image_mono ?_)
    ((isCompact_normalDiscBundle hf ε).image hc).isClosed) ?_
  · exact fun p hp => mem_normalDiscBundle.mpr
      ⟨(mem_normalTube.mp hp).1, (mem_normalTube.mp hp).2.le⟩
  · rw [← closure_normalTube hf hε]
    exact image_closure_subset_closure_image hc

/-- A closed normal disc strictly inside an embedded open normal tube is a closed embedding
when the core is compact. -/
theorem isClosedEmbedding_normalDiscBundle (hf : ContMDiff I 𝓘(ℝ, V) 1 f) {ε R : ℝ}
    (hεR : ε < R)
    (h : IsOpenEmbedding ((normalTube I f R).domRestrict fun p : M × V => f p.1 + p.2)) :
    IsClosedEmbedding ((normalDiscBundle I f ε).domRestrict
      fun p : M × V => f p.1 + p.2) := by
  have : CompactSpace (normalDiscBundle I f ε) :=
    isCompact_iff_compactSpace.mp (isCompact_normalDiscBundle hf ε)
  have hc : Continuous fun p : M × V => f p.1 + p.2 :=
    (hf.continuous.comp continuous_fst).add continuous_snd
  refine (hc.comp continuous_subtype_val).isClosedEmbedding ?_
  intro p q hpq
  have hp : p.1 ∈ normalTube I f R := mem_normalTube.mpr
    ⟨(mem_normalDiscBundle.mp p.2).1, (mem_normalDiscBundle.mp p.2).2.trans_lt hεR⟩
  have hq : q.1 ∈ normalTube I f R := mem_normalTube.mpr
    ⟨(mem_normalDiscBundle.mp q.2).1, (mem_normalDiscBundle.mp q.2).2.trans_lt hεR⟩
  exact Subtype.ext (congrArg (fun z : normalTube I f R => z.1)
    (h.injective (a₁ := ⟨p.1, hp⟩) (a₂ := ⟨q.1, hq⟩) hpq))

/-- The frontier of a smaller embedded normal tube is exactly the image of its normal
sphere bundle. -/
theorem frontier_image_normalTube (hf : ContMDiff I 𝓘(ℝ, V) 1 f) {ε R : ℝ}
    (hε : 0 < ε) (hεR : ε < R)
    (h : IsOpenEmbedding ((normalTube I f R).domRestrict fun p : M × V => f p.1 + p.2)) :
    frontier ((fun p : M × V => f p.1 + p.2) '' normalTube I f ε) =
      (fun p : M × V => f p.1 + p.2) '' normalSphereBundle I f ε := by
  let Φ : M × V → V := fun p => f p.1 + p.2
  have hopen : IsOpen (Φ '' normalTube I f ε) := by
    simpa only [range_domRestrict] using
      (isOpenEmbedding_normalTube_of_le hεR.le h).isOpen_range
  have hinj : InjOn Φ (normalDiscBundle I f ε) := by
    intro p hp q hq hpq
    exact congrArg Subtype.val
      ((isClosedEmbedding_normalDiscBundle hf hεR h).injective
        (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) hpq)
  have hsub : normalTube I f ε ⊆ normalDiscBundle I f ε := fun p hp =>
    mem_normalDiscBundle.mpr ⟨(mem_normalTube.mp hp).1, (mem_normalTube.mp hp).2.le⟩
  rw [frontier, closure_image_normalTube hf hε, hopen.interior_eq,
    ← hinj.image_sdiff_subset hsub, normalDiscBundle_sdiff_normalTube]

end Regularity

/-- **Closed disc and sphere form of the tubular neighbourhood theorem.** For a compact
`C²` embedded submanifold of a Euclidean space there is a positive radius for which the
closed normal disc and sphere bundles embed, and the frontier of the open tube is the normal
sphere image. -/
theorem exists_isClosedEmbedding_normalDiscBundle [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompactSpace M]
    {f : M → V} (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hinj : Injective f) :
    ∃ ε > 0, IsOpenEmbedding ((normalTube I f ε).domRestrict
      fun p : M × V => f p.1 + p.2) ∧
      IsClosedEmbedding ((normalDiscBundle I f ε).domRestrict
        fun p : M × V => f p.1 + p.2) ∧
      IsClosedEmbedding ((normalSphereBundle I f ε).domRestrict
        fun p : M × V => f p.1 + p.2) ∧
      frontier ((fun p : M × V => f p.1 + p.2) '' normalTube I f ε) =
        (fun p : M × V => f p.1 + p.2) '' normalSphereBundle I f ε := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  obtain ⟨R, hR, h⟩ := exists_isOpenEmbedding_normalTube hf himm hinj
  have hf1 : ContMDiff I 𝓘(ℝ, V) 1 f := hf.of_le (by norm_num)
  have hd := isClosedEmbedding_normalDiscBundle hf1 (half_lt_self hR) h
  have hsub : normalSphereBundle I f (R / 2) ⊆ normalDiscBundle I f (R / 2) := fun p hp =>
    mem_normalDiscBundle.mpr ⟨(mem_normalSphereBundle.mp hp).1,
      (mem_normalSphereBundle.mp hp).2.le⟩
  exact ⟨R / 2, half_pos hR,
    isOpenEmbedding_normalTube_of_le (half_lt_self hR).le h, hd,
    hd.comp (IsClosedEmbedding.inclusion hsub
      ((isClosed_normalSphereBundle hf1 (R / 2)).preimage continuous_subtype_val)),
    frontier_image_normalTube hf1 (half_pos hR) (half_lt_self hR) h⟩

end TauCeti
