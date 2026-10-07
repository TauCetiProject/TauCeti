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

Bound the radius uniformly before shrinking inside an injective tube. Closedness of the
core and compactness of the ambient displacement ball then make the disc image closed.
The open tube comes from `exists_isOpenEmbedding_normalTubeOfRadius`.
The bundle closure calculation is fibrewise and needs only positivity and continuity of
the radius, with no uniform positive lower bound.

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

@[simp] theorem normalDiscBundleOfRadius_const (f : M → V) (ε : ℝ) :
    normalDiscBundleOfRadius I f (fun _ => ε) = normalDiscBundle I f ε := by
  ext p
  simp

@[simp] theorem normalSphereBundleOfRadius_const (f : M → V) (ε : ℝ) :
    normalSphereBundleOfRadius I f (fun _ => ε) = normalSphereBundle I f ε := by
  ext p
  simp

/-- The difference between closed normal discs and their open tube consists of the
normal spheres. -/
@[simp] theorem normalDiscBundleOfRadius_sdiff_normalTubeOfRadius (f : M → V) (r : M → ℝ) :
    normalDiscBundleOfRadius I f r \ normalTubeOfRadius I f r =
      normalSphereBundleOfRadius I f r := by
  ext p
  simp only [mem_sdiff, mem_normalDiscBundleOfRadius, mem_normalTubeOfRadius,
    mem_normalSphereBundleOfRadius]
  grind

section Regularity

variable [I.Boundaryless] [IsManifold I 1 M] {f : M → V} {r : M → ℝ}

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
    (closure_minimal (fun p hp => ⟨(mem_normalTubeOfRadius.mp hp).1,
      (mem_normalTubeOfRadius.mp hp).2.le⟩)
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

variable [FiniteDimensional ℝ V]

/-- For a closed core and a uniformly bounded continuous radius, the normal disc image
under addition is closed. Injectivity of normal addition is not required. -/
theorem isClosed_image_normalDiscBundleOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hclosed : IsClosedEmbedding f) (hr : Continuous r) {R : ℝ} (hbound : ∀ x, r x ≤ R) :
    IsClosed ((fun p : M × V => f p.1 + p.2) '' normalDiscBundleOfRadius I f r) := by
  have hs := (hclosed.prodMap (IsClosedEmbedding.id : IsClosedEmbedding (id : V → V))).isClosedMap
    _ (isClosed_normalDiscBundleOfRadius hf hr)
  have hsub : Prod.snd '' (Prod.map f id '' normalDiscBundleOfRadius I f r) ⊆
      Metric.closedBall (0 : V) R := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hp.2.trans (hbound p.1))
  simpa only [image_image, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using
    hs.image_add_of_snd_subset (isCompact_closedBall (0 : V) R) hsub

/-- The closure of a bounded variable-radius tube image over a closed core is exactly
the closed disc image. -/
theorem closure_image_normalTubeOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hclosed : IsClosedEmbedding f) (hr : Continuous r) (hpos : ∀ x, 0 < r x)
    {R : ℝ} (hbound : ∀ x, r x ≤ R) :
    closure ((fun p : M × V => f p.1 + p.2) '' normalTubeOfRadius I f r) =
      (fun p : M × V => f p.1 + p.2) '' normalDiscBundleOfRadius I f r := by
  refine subset_antisymm (closure_minimal (image_mono
    (fun p hp => ⟨(mem_normalTubeOfRadius.mp hp).1,
      (mem_normalTubeOfRadius.mp hp).2.le⟩))
    (isClosed_image_normalDiscBundleOfRadius hf hclosed hr hbound)) ?_
  rw [← closure_normalTubeOfRadius hf hr hpos]
  exact image_closure_subset_closure_image
    ((hf.continuous.comp continuous_fst).add continuous_snd)

/-- Closed normal discs strictly inside an embedded tube form a closed embedding if
the core is closed and the disc radius is continuous and uniformly bounded. -/
theorem isClosedEmbedding_normalDiscBundleOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hclosed : IsClosedEmbedding f) (hr : Continuous r) {R : ℝ} (hbound : ∀ x, r x ≤ R)
    {s : M → ℝ} (hrs : ∀ x, r x < s x)
    (h : IsEmbedding ((normalTubeOfRadius I f s).domRestrict
      fun p : M × V => f p.1 + p.2)) :
    IsClosedEmbedding ((normalDiscBundleOfRadius I f r).domRestrict
      fun p : M × V => f p.1 + p.2) := by
  have hsub : normalDiscBundleOfRadius I f r ⊆ normalTubeOfRadius I f s :=
    fun p hp => mem_normalTubeOfRadius.mpr ⟨hp.1, hp.2.trans_lt (hrs p.1)⟩
  refine ⟨h.comp (IsEmbedding.inclusion hsub), ?_⟩
  simpa only [range_domRestrict] using
    isClosed_image_normalDiscBundleOfRadius hf hclosed hr hbound

/-- The frontier of an embedded bounded variable-radius tube over a closed core is
the corresponding normal sphere image. -/
theorem frontier_image_normalTubeOfRadius (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (hclosed : IsClosedEmbedding f) (hr : Continuous r) (hpos : ∀ x, 0 < r x)
    {R : ℝ} (hbound : ∀ x, r x ≤ R) {s : M → ℝ} (hrs : ∀ x, r x < s x)
    (h : IsOpenEmbedding ((normalTubeOfRadius I f s).domRestrict
      fun p : M × V => f p.1 + p.2)) :
    frontier ((fun p : M × V => f p.1 + p.2) '' normalTubeOfRadius I f r) =
      (fun p : M × V => f p.1 + p.2) '' normalSphereBundleOfRadius I f r := by
  let Φ : M × V → V := fun p => f p.1 + p.2
  have hsub : normalTubeOfRadius I f r ⊆ normalTubeOfRadius I f s :=
    fun p hp => mem_normalTubeOfRadius.mpr
      ⟨(mem_normalTubeOfRadius.mp hp).1, (mem_normalTubeOfRadius.mp hp).2.trans (hrs p.1)⟩
  have hopen : IsOpen (Φ '' normalTubeOfRadius I f r) := by
    have hi : IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict Φ) :=
      h.comp (IsOpenEmbedding.inclusion hsub ?_)
    · simpa only [range_domRestrict] using hi.isOpen_range
    · convert isOpen_lt ((continuous_norm.comp continuous_snd).comp
        (continuous_subtype_val : Continuous (Subtype.val : normalTubeOfRadius I f s → M × V)))
        (hr.comp (continuous_fst.comp continuous_subtype_val)) using 1
      ext p
      simp only [mem_preimage, mem_normalTubeOfRadius, mem_ofPred_eq, Function.comp_apply]
      exact and_iff_right (mem_normalTubeOfRadius.mp p.2).1
  have hinj : InjOn Φ (normalDiscBundleOfRadius I f r) := by
    intro p hp q hq hpq
    exact congrArg Subtype.val
      ((isClosedEmbedding_normalDiscBundleOfRadius hf hclosed hr hbound hrs h.isEmbedding).injective
        (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) hpq)
  have htd : normalTubeOfRadius I f r ⊆ normalDiscBundleOfRadius I f r :=
    fun p hp => ⟨(mem_normalTubeOfRadius.mp hp).1, (mem_normalTubeOfRadius.mp hp).2.le⟩
  rw [frontier, closure_image_normalTubeOfRadius hf hclosed hr hpos hbound,
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
    isClosedEmbedding_normalDiscBundleOfRadius hf1 hclosed r.continuous hbound hrs h.isEmbedding
  have hsub : normalSphereBundleOfRadius I f r ⊆ normalDiscBundleOfRadius I f r :=
    fun p hp => ⟨hp.1, hp.2.le⟩
  have htr : normalTubeOfRadius I f r ⊆ normalTubeOfRadius I f s := fun p hp =>
    mem_normalTubeOfRadius.mpr
      ⟨(mem_normalTubeOfRadius.mp hp).1, (mem_normalTubeOfRadius.mp hp).2.trans (hrs p.1)⟩
  have hopen : IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict
      fun p : M × V => f p.1 + p.2) := by
    apply h.comp (IsOpenEmbedding.inclusion htr ?_)
    convert isOpen_lt ((continuous_norm.comp continuous_snd).comp
      (continuous_subtype_val : Continuous (Subtype.val : normalTubeOfRadius I f s → M × V)))
      (r.continuous.comp (continuous_fst.comp continuous_subtype_val)) using 1
    ext p
    simp only [mem_preimage, mem_normalTubeOfRadius, mem_ofPred_eq, Function.comp_apply]
    exact and_iff_right (mem_normalTubeOfRadius.mp p.2).1
  exact ⟨r, hr, hopen, hd,
    hd.comp (IsClosedEmbedding.inclusion hsub
      ((isClosed_normalSphereBundleOfRadius hf1 r.continuous).preimage continuous_subtype_val)),
    frontier_image_normalTubeOfRadius hf1 hclosed r.continuous hr hbound hrs h⟩

end TauCeti
