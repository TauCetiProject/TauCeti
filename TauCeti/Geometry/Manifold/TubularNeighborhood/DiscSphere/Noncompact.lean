/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.DiscSphere.Basic
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Noncompact
public import TauCeti.Topology.Algebra.Group.ClosedAddition

/-!
# Closed normal discs over noncompact submanifolds

A closed embedded submanifold of a finite-dimensional Euclidean space admits a positive
continuous radius for which the closed normal discs embed as a closed neighbourhood and
the normal spheres are the frontier of the open tube. The core need not be compact.

For a proper `C¹` map into a proper real inner product space, a continuous uniformly
bounded radius gives closed normal disc images. A smaller positive radius inside an embedded
open tube gives closed disc embeddings and identifies the frontier with the normal sphere
image. For a `C²` Euclidean immersion that is a closed embedding, such a radius exists.
These closed normal neighbourhoods and their boundary spheres provide the neighbourhoods
removed in surgery.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24,
  for the variable-radius normal addition construction.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3,
  for the disc and sphere forms of tubular neighbourhoods.
-/

public section

open Set Function Topology
open scoped Manifold

namespace TauCeti

variable {V E H M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Regularity

variable [I.Boundaryless] [IsManifold I 1 M] {f : M → V} {r : M → ℝ}

variable [ProperSpace V]

/-- For a proper core map and a uniformly bounded continuous radius, the normal disc image
under addition is closed. Injectivity of normal addition is not required. -/
theorem isClosed_image_normalDiscBundleOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hproper : IsProperMap f) (hr : Continuous r) {R : ℝ} (hbound : ∀ x, r x ≤ R) :
    IsClosed ((fun p : M × V => f p.1 + p.2) '' normalDiscBundleOfRadius I f r) := by
  have hs := (hproper.prodMap (isProperMap_id : IsProperMap (id : V → V))).isClosedMap
    _ (isClosed_normalDiscBundleOfRadius hf hr)
  have hsub : Prod.snd '' (Prod.map f id '' normalDiscBundleOfRadius I f r) ⊆
      Metric.closedBall (0 : V) R := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact mem_closedBall_zero_iff.mpr ((mem_normalDiscBundleOfRadius.mp hp).2.trans (hbound p.1))
  simpa only [image_image, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using
    hs.image_add_of_snd_subset (isCompact_closedBall (0 : V) R) hsub

/-- The closure of a bounded variable-radius tube image for a proper core map is exactly
the closed disc image. -/
theorem closure_image_normalTubeOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hproper : IsProperMap f) (hr : Continuous r) (hpos : ∀ x, 0 < r x)
    {R : ℝ} (hbound : ∀ x, r x ≤ R) :
    closure ((fun p : M × V => f p.1 + p.2) '' normalTubeOfRadius I f r) =
      (fun p : M × V => f p.1 + p.2) '' normalDiscBundleOfRadius I f r := by
  refine subset_antisymm (closure_minimal (image_mono
    normalTubeOfRadius_subset_normalDiscBundleOfRadius)
    (isClosed_image_normalDiscBundleOfRadius hf hproper hr hbound)) ?_
  rw [← closure_normalTubeOfRadius hf hr hpos]
  exact image_closure_subset_closure_image
    ((hf.continuous.comp continuous_fst).add continuous_snd)

/-- Closed normal discs strictly inside an embedded tube form a closed embedding if
the core map is proper and the disc radius is continuous and uniformly bounded. -/
theorem isClosedEmbedding_normalDiscBundleOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hproper : IsProperMap f) (hr : Continuous r) {R : ℝ} (hbound : ∀ x, r x ≤ R)
    {s : M → ℝ} (hrs : ∀ x, r x < s x)
    (h : IsEmbedding ((normalTubeOfRadius I f s).domRestrict
      fun p : M × V => f p.1 + p.2)) :
    IsClosedEmbedding ((normalDiscBundleOfRadius I f r).domRestrict
      fun p : M × V => f p.1 + p.2) := by
  have hsub : normalDiscBundleOfRadius I f r ⊆ normalTubeOfRadius I f s :=
    normalDiscBundleOfRadius_subset_normalTubeOfRadius hrs
  refine ⟨h.comp (IsEmbedding.inclusion hsub), ?_⟩
  simpa only [range_domRestrict] using
    isClosed_image_normalDiscBundleOfRadius hf hproper hr hbound

/-- The frontier of an embedded bounded variable-radius tube for a proper core map is
the corresponding normal sphere image. -/
theorem frontier_image_normalTubeOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hproper : IsProperMap f) (hr : Continuous r) (hpos : ∀ x, 0 < r x)
    {R : ℝ} (hbound : ∀ x, r x ≤ R) {s : M → ℝ} (hrs : ∀ x, r x < s x)
    (h : IsOpenEmbedding ((normalTubeOfRadius I f s).domRestrict
      fun p : M × V => f p.1 + p.2)) :
    frontier ((fun p : M × V => f p.1 + p.2) '' normalTubeOfRadius I f r) =
      (fun p : M × V => f p.1 + p.2) '' normalSphereBundleOfRadius I f r := by
  let Φ : M × V → V := fun p => f p.1 + p.2
  have hopen : IsOpen (Φ '' normalTubeOfRadius I f r) := by
    simpa only [range_domRestrict] using
      (isOpenEmbedding_normalTubeOfRadius_of_le hr (fun x => (hrs x).le) h).isOpen_range
  have hinj : InjOn Φ (normalDiscBundleOfRadius I f r) := by
    intro p hp q hq hpq
    exact congrArg Subtype.val
      ((isClosedEmbedding_normalDiscBundleOfRadius hf hproper hr hbound hrs h.isEmbedding).injective
        (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) hpq)
  have htd : normalTubeOfRadius I f r ⊆ normalDiscBundleOfRadius I f r :=
    normalTubeOfRadius_subset_normalDiscBundleOfRadius
  rw [frontier, closure_image_normalTubeOfRadius hf hproper hr hpos hbound,
    hopen.interior_eq, ← hinj.image_sdiff_subset htd,
    normalDiscBundleOfRadius_sdiff_normalTubeOfRadius]

end Regularity

/-- **Noncompact closed disc and sphere tubular theorem.** A closed `C²` Euclidean
embedding admits a positive continuous radius with a closed disc embedding and the
normal sphere image as the frontier of its open tube. -/
theorem exists_isClosedEmbedding_normalDiscBundleOfRadius [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] {f : M → V}
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hclosed : IsClosedEmbedding f) :
    ∃ r : C(M, ℝ), (∀ x, 0 < r x) ∧
      IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict
        fun p : M × V => f p.1 + p.2) ∧
      IsClosedEmbedding ((normalDiscBundleOfRadius I f r).domRestrict
        fun p : M × V => f p.1 + p.2) ∧
      IsClosedEmbedding ((normalSphereBundleOfRadius I f r).domRestrict
        fun p : M × V => f p.1 + p.2) ∧
      frontier ((fun p : M × V => f p.1 + p.2) '' normalTubeOfRadius I f r) =
        (fun p : M × V => f p.1 + p.2) '' normalSphereBundleOfRadius I f r := by
  have : IsManifold I 1 M := .of_le (n := 2) (by norm_num)
  obtain ⟨s, hs, h⟩ :=
    exists_isOpenEmbedding_normalTubeOfRadius hf himm hclosed.isEmbedding.isInducing
  let r : C(M, ℝ) := ⟨fun x => min (s x / 2) 1, by fun_prop⟩
  have hr : ∀ x, 0 < r x := fun x => lt_min (half_pos (hs x)) zero_lt_one
  have hrs : ∀ x, r x < s x := fun x => (min_le_left _ _).trans_lt (half_lt_self (hs x))
  have hbound : ∀ x, r x ≤ 1 := fun x => min_le_right _ _
  have hf1 : ContMDiff I 𝓘(ℝ, V) 1 f := hf.of_le (by norm_num)
  have hd :=
    isClosedEmbedding_normalDiscBundleOfRadius hf1 hclosed.isProperMap r.continuous
      hbound hrs h.isEmbedding
  have hopen :=
    isOpenEmbedding_normalTubeOfRadius_of_le r.continuous (fun x => (hrs x).le) h
  exact ⟨r, hr, hopen, hd,
    hd.comp (IsClosedEmbedding.inclusion normalSphereBundleOfRadius_subset_normalDiscBundleOfRadius
      ((isClosed_normalSphereBundleOfRadius hf1 r.continuous).preimage continuous_subtype_val)),
    frontier_image_normalTubeOfRadius hf1 hclosed.isProperMap r.continuous hr hbound hrs h⟩

end TauCeti
