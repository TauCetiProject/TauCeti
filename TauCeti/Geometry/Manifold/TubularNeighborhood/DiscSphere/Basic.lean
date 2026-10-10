/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean

/-!
# Closed normal discs and their boundary spheres

The variable-radius closed normal disc and sphere bundles are closed subsets of `M × V`
for a `C¹` map and a continuous radius. A positive radius gives the closed disc bundle as
the closure of the open normal tube.

These bundles describe the closed neighbourhoods and boundary spheres removed in surgery.
Their closed-image and embedding results, including the compact-core specialization, are
in `DiscSphere.Noncompact`.

The disc and sphere bundles here are subsets of `M × V`, with the subspace topology, using
`normalSubspace`. No trivialization or choice of a normal frame is required. The tubular
neighbourhood construction follows J. M. Lee, *Introduction to Smooth
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
/-- Closed normal discs with radius depending on the base point. -/
def normalDiscBundleOfRadius (f : M → V) (r : M → ℝ) : Set (M × V) :=
  {p | p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ ≤ r p.1}

variable (I) in
/-- Normal spheres with radius depending on the base point. -/
def normalSphereBundleOfRadius (f : M → V) (r : M → ℝ) : Set (M × V) :=
  {p | p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ = r p.1}

@[simp] theorem mem_normalDiscBundleOfRadius {f : M → V} {r : M → ℝ} {p : M × V} :
    p ∈ normalDiscBundleOfRadius I f r ↔
      p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ ≤ r p.1 := Iff.rfl

@[simp] theorem mem_normalSphereBundleOfRadius {f : M → V} {r : M → ℝ} {p : M × V} :
    p ∈ normalSphereBundleOfRadius I f r ↔
      p.2 ∈ normalSubspace I f p.1 ∧ ‖p.2‖ = r p.1 := Iff.rfl

/-- Normal spheres are contained in the closed normal discs of the same radius. -/
theorem normalSphereBundleOfRadius_subset_normalDiscBundleOfRadius {f : M → V} {r : M → ℝ} :
    normalSphereBundleOfRadius I f r ⊆ normalDiscBundleOfRadius I f r := fun _ hp =>
  mem_normalDiscBundleOfRadius.mpr
    ⟨(mem_normalSphereBundleOfRadius.mp hp).1, (mem_normalSphereBundleOfRadius.mp hp).2.le⟩

/-- An open normal tube is contained in the closed normal discs of the same radius. -/
theorem normalTubeOfRadius_subset_normalDiscBundleOfRadius {f : M → V} {r : M → ℝ} :
    normalTubeOfRadius I f r ⊆ normalDiscBundleOfRadius I f r := fun _ hp =>
  mem_normalDiscBundleOfRadius.mpr
    ⟨(mem_normalTubeOfRadius.mp hp).1, (mem_normalTubeOfRadius.mp hp).2.le⟩

/-- Closed normal discs are monotone in their pointwise radius. -/
theorem normalDiscBundleOfRadius_subset_normalDiscBundleOfRadius {f : M → V} {r s : M → ℝ}
    (hrs : ∀ x, r x ≤ s x) :
    normalDiscBundleOfRadius I f r ⊆ normalDiscBundleOfRadius I f s := fun p hp =>
  mem_normalDiscBundleOfRadius.mpr
    ⟨(mem_normalDiscBundleOfRadius.mp hp).1,
      (mem_normalDiscBundleOfRadius.mp hp).2.trans (hrs p.1)⟩

/-- Closed normal discs lie in any open normal tube with a pointwise larger radius. -/
theorem normalDiscBundleOfRadius_subset_normalTubeOfRadius {f : M → V} {r s : M → ℝ}
    (hrs : ∀ x, r x < s x) :
    normalDiscBundleOfRadius I f r ⊆ normalTubeOfRadius I f s := fun p hp =>
  mem_normalTubeOfRadius.mpr
    ⟨(mem_normalDiscBundleOfRadius.mp hp).1,
      (mem_normalDiscBundleOfRadius.mp hp).2.trans_lt (hrs p.1)⟩

/-- The difference between closed normal discs and their open tube consists of the
normal spheres. -/
@[simp] theorem normalDiscBundleOfRadius_sdiff_normalTubeOfRadius (f : M → V) (r : M → ℝ) :
    normalDiscBundleOfRadius I f r \ normalTubeOfRadius I f r =
      normalSphereBundleOfRadius I f r := by
  ext p
  simp only [Set.mem_sdiff, mem_normalDiscBundleOfRadius, mem_normalTubeOfRadius,
    mem_normalSphereBundleOfRadius]
  grind

/-- The difference between constant-radius closed normal discs and their open tube
consists of the normal spheres. -/
@[simp] theorem normalDiscBundleOfRadius_sdiff_normalTube (f : M → V) (ε : ℝ) :
    normalDiscBundleOfRadius I f (fun _ => ε) \ normalTube I f ε =
      normalSphereBundleOfRadius I f (fun _ => ε) := by
  simpa only [normalTubeOfRadius_const] using
    normalDiscBundleOfRadius_sdiff_normalTubeOfRadius (I := I) f (fun _ => ε)

section Regularity

variable [I.Boundaryless] [IsManifold I 1 M] {f : M → V} {r : M → ℝ}

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

/-- Continuous variable-radius closed normal discs are closed in the ambient product. -/
theorem isClosed_normalDiscBundleOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hr : Continuous r) : IsClosed (normalDiscBundleOfRadius I f r) :=
  (isClosed_setOf_mem_normalSubspace hf).inter
    (isClosed_le (continuous_norm.comp continuous_snd) (hr.comp continuous_fst))

/-- Continuous variable-radius normal spheres are closed in the ambient product. -/
theorem isClosed_normalSphereBundleOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hr : Continuous r) : IsClosed (normalSphereBundleOfRadius I f r) :=
  (isClosed_setOf_mem_normalSubspace hf).inter
    (isClosed_eq (continuous_norm.comp continuous_snd) (hr.comp continuous_fst))

/-- The closure of an open normal tube with positive continuous radius is its closed
normal disc bundle. -/
theorem closure_normalTubeOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hr : Continuous r) (hpos : ∀ x, 0 < r x) :
    closure (normalTubeOfRadius I f r) = normalDiscBundleOfRadius I f r := by
  refine subset_antisymm
    (closure_minimal normalTubeOfRadius_subset_normalDiscBundleOfRadius
      (isClosed_normalDiscBundleOfRadius hf hr)) ?_
  rintro ⟨x, v⟩ ⟨hv, hnorm⟩
  let w : normalSubspace I f x := ⟨v, hv⟩
  have hw : w ∈ closure (Metric.ball 0 (r x)) := by
    rw [closure_ball _ (hpos x).ne']
    exact mem_closedBall_zero_iff.mpr hnorm
  have hc : Continuous fun u : normalSubspace I f x => (x, (u : V)) :=
    continuous_const.prodMk continuous_subtype_val
  have hsub : (fun u : normalSubspace I f x => (x, (u : V))) '' Metric.ball 0 (r x) ⊆
      normalTubeOfRadius I f r := by
    rintro _ ⟨u, hu, rfl⟩
    exact mem_normalTubeOfRadius.mpr ⟨u.2, mem_ball_zero_iff.mp hu⟩
  exact closure_mono hsub (mem_closure_image (hc.continuousAt (x := w)) hw)

end Regularity

end TauCeti
