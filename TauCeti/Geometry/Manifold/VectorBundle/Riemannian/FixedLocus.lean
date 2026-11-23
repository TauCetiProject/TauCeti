/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Cone
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.SectionTopology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FixedLocus

/-!
# Riemannian metrics with prescribed values on a set

Genericity theorems for Riemannian metrics are often relative: the metric is kept equal to a
given model on a prescribed region and perturbed only elsewhere. In Morse homology, for instance,
the metric is kept Euclidean in Morse coordinates on closed balls around the critical points, or
fixed on closed collars of the boundary of a cobordism, while transversality is achieved by
perturbing it in the regular region. The parameter space of such an argument is the set
`Bundle.ContMDiffRiemannianMetric.fixedOn g₀ S` of the `C^n` metrics equal to a given metric
`g₀` at every point of a set `S`.

As a set of symmetric sections, this is the intersection of the closed affine subspace of the
sections equal to `g₀` on `S` (`ContMDiffSection.fixedOn`) with the cone of positive-definite
sections (`Bundle.ContMDiffRiemannianMetric.image_toSymmetricSection_fixedOn`). It is closed in
the space of metrics for the compact derivative topology
(`Bundle.ContMDiffRiemannianMetric.isClosed_fixedOn`) and stable under convex combinations.
When the prescribed values are models `β i` given near pairwise disjoint closed sets `A i`, such
as Euclidean metrics in Morse charts on disjoint closed balls, the metrics realizing all of them
form `fixedOn g₁ (⋃ i, A i)` for any one of them `g₁`, and such a `g₁` exists by the patching
theorem `TauCeti.exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite`
(`Bundle.ContMDiffRiemannianMetric.exists_fixedOn_iUnion_eq_setOf`).

On a compact base modelled on a locally compact space, for a finite-rank bundle
and finite or smooth regularity `n`, the cone is open in the section space, which is completely
metrizable, so the space of metrics is completely metrizable
(`Bundle.ContMDiffRiemannianMetric.isCompletelyMetrizableSpace_frameTopology`), and so is its
closed subset `fixedOn g₀ S`
(`Bundle.ContMDiffRiemannianMetric.isCompletelyMetrizableSpace_fixedOn`). In particular both are
Baire spaces (`Bundle.ContMDiffRiemannianMetric.baireSpace_frameTopology`,
`Bundle.ContMDiffRiemannianMetric.baireSpace_fixedOn`): a countable intersection of open dense
sets of metrics, each obtained by perturbing away from `S`, is dense.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.fixedOn g₀ S`: the `C^n` metrics equal to `g₀` on `S`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.image_toSymmetricSection_fixedOn`: as symmetric sections,
  these metrics are the positive-definite sections equal to `g₀` on `S`.
* `Bundle.ContMDiffRiemannianMetric.exists_fixedOn_iUnion_eq_setOf`: the metrics equal to
  prescribed models on disjoint closed sets form a nonempty `fixedOn g₁ (⋃ i, A i)`.
* `Bundle.ContMDiffRiemannianMetric.convexCombination_mem_fixedOn`: `fixedOn g₀ S` is stable
  under convex combinations.
* `Bundle.ContMDiffRiemannianMetric.isClosed_fixedOn`: it is closed for the compact derivative
  topology.
* `Bundle.ContMDiffRiemannianMetric.isCompletelyMetrizableSpace_frameTopology`,
  `Bundle.ContMDiffRiemannianMetric.baireSpace_frameTopology`: on a compact base
  modelled on a locally compact space, for finite or smooth regularity `n`, the space of `C^n`
  metrics on a finite-rank bundle is completely metrizable, hence Baire.
* `Bundle.ContMDiffRiemannianMetric.isCompletelyMetrizableSpace_fixedOn`,
  `Bundle.ContMDiffRiemannianMetric.baireSpace_fixedOn`: so is `fixedOn g₀ S`.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §4, for the Baire property of spaces of
  `C^r` maps.
-/

public section

open Bundle Set TopologicalSpace TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-! ### Metrics with prescribed values on a set -/

/-- The `C^n` Riemannian metrics equal to the metric `g₀` at every point of the set `S`. -/
def fixedOn (g₀ : ContMDiffRiemannianMetric IB n F V) (S : Set B) :
    Set (ContMDiffRiemannianMetric IB n F V) :=
  {g | ∀ x ∈ S, g.inner x = g₀.inner x}

@[simp]
theorem mem_fixedOn {g₀ g : ContMDiffRiemannianMetric IB n F V} {S : Set B} :
    g ∈ fixedOn g₀ S ↔ ∀ x ∈ S, g.inner x = g₀.inner x :=
  Iff.rfl

theorem self_mem_fixedOn (g₀ : ContMDiffRiemannianMetric IB n F V) (S : Set B) :
    g₀ ∈ fixedOn g₀ S :=
  fun _ _ ↦ rfl

/-- A metric is equal to `g₀` on `S` exactly when its symmetric section is equal to that of `g₀`
on `S`. -/
theorem toSymmetricSection_mem_fixedOn_iff {g₀ g : ContMDiffRiemannianMetric IB n F V}
    {S : Set B} :
    g.toSymmetricSection ∈ ContMDiffSection.fixedOn g₀.toSymmetricSection S ↔
      g ∈ fixedOn g₀ S := by
  simp only [ContMDiffSection.mem_fixedOn, mem_fixedOn]
  refine forall₂_congr fun x _ ↦ ⟨fun h ↦ ?_, fun h ↦ Subtype.ext ?_⟩
  · simpa using congrArg Subtype.val h
  · simpa using h

theorem fixedOn_eq_preimage (g₀ : ContMDiffRiemannianMetric IB n F V) (S : Set B) :
    fixedOn g₀ S =
      toSymmetricSection ⁻¹' (ContMDiffSection.fixedOn g₀.toSymmetricSection S : Set _) := by
  ext g
  exact toSymmetricSection_mem_fixedOn_iff.symm

@[simp]
theorem fixedOn_empty (g₀ : ContMDiffRiemannianMetric IB n F V) :
    fixedOn g₀ (∅ : Set B) = univ := by
  rw [fixedOn_eq_preimage, ContMDiffSection.fixedOn_empty, AffineSubspace.top_coe, preimage_univ]

theorem fixedOn_antitone (g₀ : ContMDiffRiemannianMetric IB n F V) :
    Antitone (fixedOn g₀ : Set B → Set _) :=
  fun _ _ hST ↦ by
    simp only [fixedOn_eq_preimage]
    exact preimage_mono (SetLike.coe_subset_coe.2 (ContMDiffSection.fixedOn_antitone _ hST))

theorem fixedOn_union (g₀ : ContMDiffRiemannianMetric IB n F V) (S T : Set B) :
    fixedOn g₀ (S ∪ T) = fixedOn g₀ S ∩ fixedOn g₀ T := by
  rw [fixedOn_eq_preimage, ContMDiffSection.fixedOn_union, AffineSubspace.coe_inf, preimage_inter,
    ← fixedOn_eq_preimage, ← fixedOn_eq_preimage]

theorem fixedOn_eq_of_mem {g₀ g₁ : ContMDiffRiemannianMetric IB n F V} {S : Set B}
    (h : g₁ ∈ fixedOn g₀ S) : fixedOn g₁ S = fixedOn g₀ S := by
  rw [fixedOn_eq_preimage, fixedOn_eq_preimage,
    ContMDiffSection.fixedOn_eq_of_mem (toSymmetricSection_mem_fixedOn_iff.2 h)]

/-- **Metrics with prescribed models on closed sets.** Let `A i` be a locally finite family of
pairwise disjoint closed subsets of a σ-compact Hausdorff smooth manifold modelled on a
finite-dimensional space, and `β i` a field of bilinear forms which is `C^n`, symmetric and
positive definite on an open neighbourhood of `A i`. The `C^n` metrics equal to `β i` over `A i`
for every `i` are the metrics equal to one of them on `⋃ i, A i`; in particular there is one. -/
theorem exists_fixedOn_iUnion_eq_setOf {n : ℕ∞} [∀ b, ContinuousConstSMul ℝ (V b)]
    [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] [IsManifold IB ∞ B]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle n F V IB]
    {ι : Type*} {A U : ι → Set B} {β : ι → (b : B) → V b →L[ℝ] V b →L[ℝ] ℝ}
    (hA : ∀ i, IsClosed (A i)) (hAf : LocallyFinite A) (hAd : Pairwise (Function.onFun Disjoint A))
    (hU : ∀ i, IsOpen (U i)) (hAU : ∀ i, A i ⊆ U i)
    (hβ : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (β i b)) (U i))
    (hsymm : ∀ i, ∀ b ∈ U i, ∀ v w, β i b v w = β i b w v)
    (hpos : ∀ i, ∀ b ∈ U i, ∀ v, v ≠ 0 → 0 < β i b v v) :
    ∃ g₁ : ContMDiffRiemannianMetric IB n F V,
      fixedOn g₁ (⋃ i, A i) = {g | ∀ i, ∀ b ∈ A i, g.inner b = β i b} := by
  obtain ⟨g₁, hg₁⟩ := exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite
    hA hAf hAd hU hAU hβ hsymm hpos
  refine ⟨g₁, ?_⟩
  ext g
  simp only [mem_fixedOn, mem_iUnion, mem_ofPred_eq]
  exact ⟨fun h i b hb ↦ (h b ⟨i, hb⟩).trans (hg₁ i b hb),
    fun h b ⟨i, hb⟩ ↦ (h i b hb).trans (hg₁ i b hb).symm⟩

/-- A convex combination of two metrics equal to `g₀` on `S` is equal to `g₀` on `S`. -/
theorem convexCombination_mem_fixedOn [FiniteDimensional ℝ F]
    {g₀ g h : ContMDiffRiemannianMetric IB n F V} {S : Set B}
    (hg : g ∈ fixedOn g₀ S) (hh : h ∈ fixedOn g₀ S) (t : unitInterval) :
    g.convexCombination h t ∈ fixedOn g₀ S :=
  fun x hx ↦ (convexCombination_inner_eq_of_eq g h t ((hg x hx).trans (hh x hx).symm)).trans
    (hg x hx)

/-- As symmetric sections, the metrics equal to `g₀` on `S` are the positive-definite sections
equal to the section of `g₀` on `S`. -/
theorem image_toSymmetricSection_fixedOn [FiniteDimensional ℝ F]
    (g₀ : ContMDiffRiemannianMetric IB n F V) (S : Set B) :
    toSymmetricSection '' fixedOn g₀ S =
      (ContMDiffSection.fixedOn g₀.toSymmetricSection S : Set _) ∩
        positiveDefiniteSymmetricSections IB n F V := by
  rw [fixedOn_eq_preimage, image_preimage_eq_inter_range, range_toSymmetricSection]

/-! ### Topology -/

variable [ContMDiffVectorBundle n F V IB] [IsManifold IB n B]
  {ι : Type*}
  (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
    (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)

/-- The metrics equal to `g₀` on a set form a closed subset of the space of metrics, for the
compact derivative topology of any covering frame system of the symmetric bilinear bundle. -/
theorem isClosed_fixedOn (hcover : ∀ x, ∃ i, x ∈ U i) (g₀ : ContMDiffRiemannianMetric IB n F V)
    (S : Set B) :
    let _ := frameTopology IB n e U hU
    IsClosed (fixedOn g₀ S) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  rw [fixedOn_eq_preimage]
  exact (ContMDiffSection.isClosed_fixedOn e U hU hcover _ S).preimage
    (isEmbedding_toSymmetricSection_frameTopology e U hU).continuous

variable [LocallyCompactSpace EB] [ENat.LEInfty n] [FiniteDimensional ℝ F]
  [CompactSpace B]

/-- On a compact base modelled on a locally compact space, for finite or smooth
regularity `n`, the `C^n` metrics on a finite-rank bundle form a completely metrizable space for
the compact derivative topology of any covering frame system: they are homeomorphic to the
positive-definite cone, an open subset of the completely metrizable section space. -/
theorem isCompletelyMetrizableSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology IB n e U hU
    IsCompletelyMetrizableSpace (ContMDiffRiemannianMetric IB n F V) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  have := ContMDiffSection.isCompletelyMetrizableSpace_frameTopology (I := IB) (n := n)
    e U hU hcover
  have := (isOpen_positiveDefiniteSymmetricSections_frameTopology (IB := IB) (n := n)
    e U hU hcover).isCompletelyMetrizableSpace
  exact (positiveDefiniteSymmetricSectionHomeomorph e U hU).isClosedEmbedding
    |>.IsCompletelyMetrizableSpace

/-- **Metrics form a Baire space.** On a compact base modelled on a locally compact
space, for finite or smooth regularity `n`, the `C^n` metrics on a finite-rank bundle form a Baire
space for the compact derivative topology of any covering frame system. -/
theorem baireSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology IB n e U hU
    BaireSpace (ContMDiffRiemannianMetric IB n F V) := by
  let _ := frameTopology IB n e U hU
  have := isCompletelyMetrizableSpace_frameTopology (IB := IB) (n := n) e U hU hcover
  infer_instance

/-- On a compact base modelled on a locally compact space, for finite or smooth
regularity `n`, the `C^n` metrics on a finite-rank bundle equal to `g₀` on a set form a
completely metrizable space for the compact derivative topology of any covering frame system. -/
theorem isCompletelyMetrizableSpace_fixedOn (hcover : ∀ x, ∃ i, x ∈ U i)
    (g₀ : ContMDiffRiemannianMetric IB n F V) (S : Set B) :
    let _ := frameTopology IB n e U hU
    IsCompletelyMetrizableSpace (fixedOn g₀ S) := by
  let _ := frameTopology IB n e U hU
  have := isCompletelyMetrizableSpace_frameTopology (IB := IB) (n := n) e U hU hcover
  exact (isClosed_fixedOn e U hU hcover g₀ S).isCompletelyMetrizableSpace

/-- **Metrics with prescribed values form a Baire space.** On a compact base
modelled on a locally compact space, for finite or smooth regularity `n`, the `C^n` metrics on a
finite-rank bundle equal to `g₀` on a set form a Baire space for the compact derivative topology
of any covering frame system: a countable intersection of relatively open dense sets of such
metrics is dense. -/
theorem baireSpace_fixedOn (hcover : ∀ x, ∃ i, x ∈ U i)
    (g₀ : ContMDiffRiemannianMetric IB n F V) (S : Set B) :
    let _ := frameTopology IB n e U hU
    BaireSpace (fixedOn g₀ S) := by
  let _ := frameTopology IB n e U hU
  have := isCompletelyMetrizableSpace_fixedOn (IB := IB) (n := n) e U hU hcover g₀ S
  infer_instance

end Bundle.ContMDiffRiemannianMetric
