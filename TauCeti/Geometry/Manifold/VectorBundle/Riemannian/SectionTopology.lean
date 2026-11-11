/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Interpolation
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover

/-!
# The section-space topology on Riemannian metrics

The native finite-rank `C^n` Riemannian metrics carry the subspace topology of the
positive-definite cone in the `C^n` sections of the bundle of symmetric bilinear forms.
`Bundle.ContMDiffRiemannianMetric.frameTopology` supplies this topology explicitly, using
`ContMDiffSection.frameTopology` on the section space. For smooth metrics this controls
all finite derivatives on compact coordinate sets. Covering smooth frames give the same
topology, and the algebraic identification with positive-definite sections is a homeomorphism.

Convex interpolation is jointly continuous in the two metrics and the interval parameter.
This concerns positive definiteness, not positivity of scalar curvature. All results allow
models with corners; neither compactness of the base nor a choice of background metric is
needed. No completeness assertion for the section space, or comparison with the separate
tangent-metric chart C² topology, is made here.

## References

* R. Hamilton, *The inverse function theorem of Nash and Moser*, Part I, Example 1.1.5,
  for the section-space viewpoint on spaces of smooth metrics.
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace TauCeti
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
  [ContMDiffVectorBundle n F V IB] [IsManifold IB n B]
  {ι : Type*}
  (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
    (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)

variable (IB n) in
/-- The subspace topology on native metrics induced by the compact derivative topology on
sections of the symmetric bilinear bundle, in the specified smooth frames. -/
@[instance_reducible]
def frameTopology : TopologicalSpace (ContMDiffRiemannianMetric IB n F V) :=
  .induced toSymmetricSection (ContMDiffSection.frameTopology (I := IB) (n := n) e U hU)

/-- The section representation is an embedding for the section-space topology on metrics. -/
theorem isEmbedding_toSymmetricSection_frameTopology :
    let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    let _ := frameTopology IB n e U hU
    IsEmbedding (toSymmetricSection (IB := IB) (n := n) (F := F) (V := V)) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  exact ⟨.induced _, toSymmetricSection_injective⟩

/-- Continuity of metric families is exactly continuity of their symmetric sections. -/
theorem continuous_frameTopology_iff {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric IB n F V} :
    let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    let _ := frameTopology IB n e U hU
    Continuous g ↔ Continuous (fun p ↦ (g p).toSymmetricSection) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  exact (isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := n)
    e U hU).isInducing.continuous_iff

/-- Convergence of native metrics is exactly convergence of their symmetric sections. -/
theorem tendsto_frameTopology_iff {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric IB n F V} {g₀ : ContMDiffRiemannianMetric IB n F V} :
    let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    let _ := frameTopology IB n e U hU
    Tendsto g l (𝓝 g₀) ↔
      Tendsto (fun p ↦ (g p).toSymmetricSection) l (𝓝 g₀.toSymmetricSection) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  exact (isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := n)
    e U hU).isInducing.tendsto_nhds_iff

variable [FiniteDimensional ℝ F]

/-- Native metrics are homeomorphic to the positive-definite cone of symmetric sections,
with its inherited compact derivative topology. -/
def positiveDefiniteSymmetricSectionHomeomorph :
    let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    let _ := frameTopology IB n e U hU
    ContMDiffRiemannianMetric IB n F V ≃ₜ
      TauCeti.Manifold.positiveDefiniteSymmetricSections IB n F V := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  refine { positiveDefiniteSymmetricSectionEquiv with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact ((isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := n)
      e U hU).continuous.subtype_mk fun g ↦ g.toSymmetricSection_mem).congr
        fun g ↦ Subtype.ext (positiveDefiniteSymmetricSectionEquiv_apply g).symm
  · apply (continuous_frameTopology_iff (IB := IB) (n := n) e U hU).mpr
    simpa using (continuous_subtype_val : Continuous
      (fun σ : TauCeti.Manifold.positiveDefiniteSymmetricSections IB n F V ↦ σ.1))

@[simp]
theorem positiveDefiniteSymmetricSectionHomeomorph_apply
    (g : ContMDiffRiemannianMetric IB n F V) :
    (positiveDefiniteSymmetricSectionHomeomorph e U hU g).1 = g.toSymmetricSection :=
  positiveDefiniteSymmetricSectionEquiv_apply g

@[simp]
theorem positiveDefiniteSymmetricSectionHomeomorph_symm_apply
    (σ : TauCeti.Manifold.positiveDefiniteSymmetricSections IB n F V) :
    let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    let _ := frameTopology IB n e U hU
    (positiveDefiniteSymmetricSectionHomeomorph (IB := IB) (n := n) e U hU).symm σ =
      ofPositiveDefiniteSymmetricSection σ.1 σ.2 := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  exact positiveDefiniteSymmetricSectionEquiv_symm_apply σ

omit [FiniteDimensional ℝ F] in
/-- Covering smooth frames give a Hausdorff topology on the native metric carrier. -/
theorem t2Space_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology IB n e U hU
    T2Space (ContMDiffRiemannianMetric IB n F V) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  let _ := ContMDiffSection.t2Space_frameTopology (I := IB) (n := n) e U hU hcover
  exact (isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := n) e U hU).t2Space

omit [FiniteDimensional ℝ F] in
/-- The section-space topology on native metrics is independent of the covering smooth
frames of the symmetric bilinear bundle. -/
theorem frameTopology_eq_of_covers [LocallyCompactSpace EB]
    (hcover : ∀ x, ∃ i, x ∈ U i)
    {κ : Type*}
    (e' : κ → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens B) (hU' : ∀ j, (U' j : Set B) ⊆ (e' j).baseSet)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    frameTopology IB n e U hU = frameTopology IB n e' U' hU' := by
  unfold frameTopology
  rw [ContMDiffSection.frameTopology_eq_of_covers e U hU hcover e' U' hU' hcover']

/-- Convex interpolation of native metrics is jointly continuous for their section-space
topology, including at the endpoints of the unit interval. -/
theorem continuous_convexCombination_frameTopology :
    let _ := frameTopology IB n e U hU
    Continuous (fun q : (ContMDiffRiemannianMetric IB n F V ×
      ContMDiffRiemannianMetric IB n F V) × unitInterval ↦
        q.1.1.convexCombination q.1.2 q.2) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  let _ := frameTopology IB n e U hU
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := IB) (n := n) e U hU
  let _ := ContMDiffSection.continuousSMul_frameTopology (I := IB) (n := n) e U hU
  have hs := (isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := n) e U hU).continuous
  apply (continuous_frameTopology_iff (IB := IB) (n := n) e U hU).mpr
  simp only [toSymmetricSection_convexCombination]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
    (hs.comp (continuous_fst.comp continuous_fst))).add
      ((continuous_subtype_val.comp continuous_snd).smul
        (hs.comp (continuous_snd.comp continuous_fst)))

end Bundle.ContMDiffRiemannianMetric
