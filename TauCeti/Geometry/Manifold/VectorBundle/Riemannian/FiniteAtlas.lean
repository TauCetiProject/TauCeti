/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartSectionTopology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteAtlas
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Cone
import TauCeti.Topology.VectorBundle.Bilinear

/-!
# Finite-atlas `C^k` topologies and distances on Riemannian metrics

Let `V` be a smooth vector bundle over a manifold `B`, with symmetric bilinear bundle `Sym²(V*)`.
Given a finite chart-frame atlas `(e, U, hU, c, K)` of `Sym²(V*)` with compact coordinate pieces
`K i` in the inherited extended chart targets `(extChartAt IB (c i)).target`, the finite-atlas `C^k`
distance `Bundle.ContMDiffRiemannianMetric.finiteAtlasDist` between two smooth metrics `g₁` and
`g₂` is the finite-atlas `C^k` seminorm of `g₁.toSymmetricSection - g₂.toSymmetricSection`: the
largest coordinate derivative of order at most `k` across the compact pieces `K i`. In particular,
for `k = 2` it measures uniform coordinate derivatives of orders `0`, `1`, and `2` over the finite
atlas.

Derivatives are taken within extended chart targets and interiors are relative to them, so models
with corners — in particular half-space models for compact manifolds with boundary — and boundary
or corner charts are included throughout. None of the finite-atlas metric definitions, topology
comparisons, or uniform margins uses completeness of section spaces on boundaryless manifolds.

When the compact coordinate pieces have relative interiors covering `B`:
* any two such finite chart-frame atlases give Lipschitz-equivalent `C^k` distances
  (`Bundle.ContMDiffRiemannianMetric.exists_finiteAtlasDist_le`) and identical topologies
  (`Bundle.ContMDiffRiemannianMetric.finiteAtlasTopology_eq_of_covers`);
* `Bundle.ContMDiffRiemannianMetric.finiteAtlasTopology` coincides with the finite-order section
  topology `Bundle.ContMDiffRiemannianMetric.frameCkTopology`
  (`Bundle.ContMDiffRiemannianMetric.finiteAtlasTopology_eq_frameCkTopology`), upgrading it to a
  metric space (`Bundle.ContMDiffRiemannianMetric.finiteAtlasMetricSpace`) and yielding uniform
  `δ`-margins around open and compact sets of smooth metrics;
* the `C^∞` section topology `Bundle.ContMDiffRiemannianMetric.frameTopology IB ∞` is the infimum
  of the finite-atlas `C^k` topologies over `k : ℕ`
  (`Bundle.ContMDiffRiemannianMetric.frameTopology_infty_eq_iInf_finiteAtlasTopology`).

On a boundaryless manifold modelled on a locally compact space, this identifies the chart `C^k` and
`C²` topologies `chartCkTopology k` and `chartC2Topology` with the finite-atlas topologies, and
`chartCInftyTopology` with their infimum over `k : ℕ`. When the model fibre `F` is
finite-dimensional and a finite chart-frame atlas covers `B`, the positive-definite cone of `C^n`
symmetric sections admits uniform finite-atlas `C^k` margins
(`TauCeti.Manifold.exists_pos_mem_positiveDefiniteSymmetricSections_of_finiteAtlasSeminorm_lt`), is
open in the finite-atlas `C^k` (in particular `C²`) normed space, and receives `toSymmetricSection`
as an open embedding
(`Bundle.ContMDiffRiemannianMetric.isOpenEmbedding_toSymmetricSection_finiteAtlas`, and
`Bundle.ContMDiffRiemannianMetric.isOpenEmbedding_toSymmetricSection_frameTopology` on a compact
base for any covering frame system).

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.finiteAtlasDist`: the finite-atlas `C^k` distance on smooth
  Riemannian metrics.
* `Bundle.ContMDiffRiemannianMetric.finiteAtlasPseudoMetricSpace` and
  `Bundle.ContMDiffRiemannianMetric.finiteAtlasTopology`: the pseudometric space and topology on
  smooth metrics induced by `finiteAtlasDist`.
* `Bundle.ContMDiffRiemannianMetric.finiteAtlasMetricSpace`: the metric space on smooth metrics for
  a covering finite chart-frame atlas, carrying `frameCkTopology`.

## Main results

* `TauCeti.Manifold.exists_pos_mem_positiveDefiniteSymmetricSections_of_finiteAtlasSeminorm_lt` and
  `TauCeti.Manifold.isOpen_positiveDefiniteSymmetricSections_finiteAtlas`: uniform finite-atlas
  margins and openness of the metric cone (in particular for `C²` and `C^∞` sections).
* `Bundle.ContMDiffRiemannianMetric.isOpenEmbedding_toSymmetricSection_finiteAtlas` and
  `Bundle.ContMDiffRiemannianMetric.isOpenEmbedding_toSymmetricSection_frameTopology`: open
  embedding of native `C^k` and `C^n` metrics into symmetric tensor sections.
* `Bundle.ContMDiffRiemannianMetric.exists_finiteAtlasDist_le` and
  `Bundle.ContMDiffRiemannianMetric.finiteAtlasTopology_eq_of_covers`: Lipschitz equivalence and
  atlas independence of the finite-atlas `C^k` topology on smooth metrics, including boundary
  charts.
* `Bundle.ContMDiffRiemannianMetric.finiteAtlasTopology_eq_frameCkTopology`,
  `Bundle.ContMDiffRiemannianMetric.isOpen_frameCkTopology_iff_finiteAtlasDist`, and
  `IsCompact.exists_pos_forall_mem_of_isOpen_frameCkTopology`: identification with
  `frameCkTopology` and uniform `C^k` margins.
* `Bundle.ContMDiffRiemannianMetric.metrizableSpace_frameCkTopology_of_compactSpace`: metrizability
  of `frameCkTopology` on compact manifolds (with or without boundary).
* `Bundle.ContMDiffRiemannianMetric.chartCkTopology_eq_finiteAtlasTopology`,
  `Bundle.ContMDiffRiemannianMetric.chartC2Topology_eq_finiteAtlasTopology`, and
  `Bundle.ContMDiffRiemannianMetric.chartCInftyTopology_eq_iInf_finiteAtlasTopology`: comparison of
  the boundaryless chart `C^k`, `C²`, and `C^∞` topologies with finite-atlas seminorms.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for finite-atlas `C^k` topologies.
* R. Hamilton, *The inverse function theorem of Nash and Moser*, Bull. Amer. Math. Soc. 7 (1982),
  Part I, Example 1.1.5, for the open metric cone in symmetric tensor sections.
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

/-! ### Openness and finite-atlas margins of the metric cone -/

namespace TauCeti.Manifold

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **Uniform finite-atlas margin in the metric cone.** When the compact pieces `K i` of a finite
chart-frame atlas cover `B` (including boundary and corner charts) and the model fibre `F` is
finite-dimensional, around any positive-definite `C^n` symmetric section `σ₀` there is a radius
`δ > 0` in the finite-atlas `C^k` seminorm (`k ≤ n`, in particular `k = 0` or `k = 2`, and including
`n = ∞`) within which every `C^n` symmetric section remains positive-definite. -/
theorem exists_pos_mem_positiveDefiniteSymmetricSections_of_finiteAtlasSeminorm_lt
    {n : ℕ∞ω} [IsManifold IB n B] [ContMDiffVectorBundle n F V IB]
    {ι : Type*} [Fintype ι]
    (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)
    {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt IB (c i)).target}
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ K i)
    (k : ℕ) (hk : k ≤ n)
    {σ₀ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯}
    (hσ₀ : σ₀ ∈ positiveDefiniteSymmetricSections IB n F V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ,
        fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯,
      ContMDiffSection.finiteAtlasSeminorm e U hU c K k hk (σ - σ₀) < δ →
        σ ∈ positiveDefiniteSymmetricSections IB n F V := by
  have hΩ : IsOpen {p : TotalSpace (symmetricBilinearMaps ℝ F ℝ)
      (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ) |
      ∀ v : V p.1, v ≠ 0 → 0 < (p.2 : V p.1 →L[ℝ] V p.1 →L[ℝ] ℝ) v v} :=
    TauCeti.isOpen_setOf_forall_bilinear_bundle_apply_self_pos.preimage
      TauCeti.continuous_totalSpace_coe_symmetricBilinearMaps
  obtain ⟨δ, hδ, hball⟩ := ContMDiffSection.exists_pos_forall_mem_of_isOpen_totalSpace e U hU hK
    k hk hΩ fun y ↦ (mem_positiveDefiniteSymmetricSections σ₀).mp hσ₀ y
  exact ⟨δ, hδ, fun σ hlt ↦ (mem_positiveDefiniteSymmetricSections σ).mpr (hball σ hlt)⟩

/-- **The metric cone is open in the finite-atlas `C^k` normed space.** When the compact pieces
`K i` of a finite chart-frame atlas have relative interiors covering `B` (including boundary and
corner charts) and `F` is finite-dimensional, the positive-definite `C^k` symmetric sections — in
particular for `k = 2`, the `C²` metric cone — form an open cone in
`ContMDiffSection.finiteAtlasNormedAddCommGroup k e U hU hK`. -/
theorem isOpen_positiveDefiniteSymmetricSections_finiteAtlas
    (k : ℕ) [IsManifold IB k B] [ContMDiffVectorBundle k F V IB]
    {ι : Type*} [Fintype ι]
    (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)
    {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt IB (c i)).target}
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target)) :
    letI := ContMDiffSection.finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
    IsOpen (positiveDefiniteSymmetricSections IB k F V) := by
  let _ := ContMDiffSection.finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
  rw [Metric.isOpen_iff]
  intro σ₀ hσ₀
  obtain ⟨δ, hδ, hball⟩ :=
    exists_pos_mem_positiveDefiniteSymmetricSections_of_finiteAtlasSeminorm_lt e U hU
      (fun y ↦ (hK y).imp fun _ ⟨hyU, hy, hyK⟩ ↦ ⟨hyU, hy, interior_subset hyK⟩) k le_rfl hσ₀
  refine ⟨δ, hδ, fun σ hσ ↦ hball σ ?_⟩
  rwa [Metric.mem_ball, ContMDiffSection.dist_finiteAtlas k e U hU hK] at hσ

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

section OpenCone

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- When a finite chart-frame atlas has compact pieces with relative interiors covering `B`
(including boundary and corner charts) and `F` is finite-dimensional, `toSymmetricSection` is an
open embedding of `C^k` metrics into the finite-atlas `C^k` normed space of symmetric sections (in
particular for `k = 2`). -/
theorem isOpenEmbedding_toSymmetricSection_finiteAtlas
    (k : ℕ) [IsManifold IB k B] [ContMDiffVectorBundle k F V IB]
    {ι : Type*} [Fintype ι]
    (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)
    {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt IB (c i)).target}
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target)) :
    letI := frameTopology IB k e U hU
    letI := ContMDiffSection.finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
    IsOpenEmbedding (toSymmetricSection (IB := IB) (n := k) (F := F) (V := V)) := by
  let _ := frameTopology IB k e U hU
  let _ := ContMDiffSection.finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
  refine ⟨?_, ?_⟩
  · convert isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := k) e U hU
    exact ContMDiffSection.topologicalSpace_finiteAtlasNormedAddCommGroup k e U hU hK
  · rw [range_toSymmetricSection]
    exact isOpen_positiveDefiniteSymmetricSections_finiteAtlas k e U hU hK

/-- On a compact base (possibly with boundary or corners) modelled on a locally compact space,
`toSymmetricSection` is an open embedding of `C^n` metrics with `frameTopology` into `C^n`
symmetric sections with `ContMDiffSection.frameTopology`, for every regularity `n` (in particular
`n = 2` and `n = ∞`). -/
theorem isOpenEmbedding_toSymmetricSection_frameTopology [LocallyCompactSpace EB] [CompactSpace B]
    {n : ℕ∞ω} [IsManifold IB n B] [ContMDiffVectorBundle n F V IB]
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := frameTopology IB n e U hU
    letI := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    IsOpenEmbedding (toSymmetricSection (IB := IB) (n := n) (F := F) (V := V)) := by
  let _ := frameTopology IB n e U hU
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  refine ⟨isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := n) e U hU, ?_⟩
  rw [range_toSymmetricSection]
  exact isOpen_positiveDefiniteSymmetricSections_frameTopology e U hU hcover

end OpenCone

/-! ### Finite-atlas `C^k` distance and topology on smooth metrics -/

section FiniteAtlasDist

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
    (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)
  (c : ∀ i, U i) (K : ∀ i, Compacts (extChartAt IB (c i)).target)

/-- The `C^k` distance on smooth Riemannian metrics associated to a finite chart-frame atlas with
compact coordinate pieces `K i` in the inherited extended chart targets
`(extChartAt IB (c i)).target`, including boundary and corner charts. For `k = 2` it measures
uniform coordinate derivatives of orders `0`, `1`, and `2` over the finite atlas. -/
def finiteAtlasDist (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) : ℝ :=
  ContMDiffSection.finiteAtlasSeminorm e U hU c K k (by simp)
    (g₁.toSymmetricSection - g₂.toSymmetricSection)

/-- Defining formula for `Bundle.ContMDiffRiemannianMetric.finiteAtlasDist`. -/
theorem finiteAtlasDist_def (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    finiteAtlasDist e U hU c K k g₁ g₂ =
      ContMDiffSection.finiteAtlasSeminorm e U hU c K k (by simp)
        (g₁.toSymmetricSection - g₂.toSymmetricSection) :=
  (rfl)

/-- A metric is at finite-atlas distance zero from itself. -/
@[simp]
theorem finiteAtlasDist_self (k : ℕ) (g : ContMDiffRiemannianMetric IB ∞ F V) :
    finiteAtlasDist e U hU c K k g g = 0 := by
  rw [finiteAtlasDist_def, sub_self, map_zero]

/-- The finite-atlas `C^k` distance is symmetric. -/
theorem finiteAtlasDist_comm (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    finiteAtlasDist e U hU c K k g₁ g₂ = finiteAtlasDist e U hU c K k g₂ g₁ := by
  rw [finiteAtlasDist_def, finiteAtlasDist_def, ← neg_sub, map_neg_eq_map]

/-- The finite-atlas `C^k` distance is nonnegative. -/
theorem finiteAtlasDist_nonneg (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    0 ≤ finiteAtlasDist e U hU c K k g₁ g₂ :=
  apply_nonneg _ _

/-- Triangle inequality for the finite-atlas `C^k` distance. -/
theorem finiteAtlasDist_triangle (k : ℕ) (g₁ g₂ g₃ : ContMDiffRiemannianMetric IB ∞ F V) :
    finiteAtlasDist e U hU c K k g₁ g₃ ≤
      finiteAtlasDist e U hU c K k g₁ g₂ + finiteAtlasDist e U hU c K k g₂ g₃ := by
  have hsub : g₁.toSymmetricSection - g₃.toSymmetricSection =
      (g₁.toSymmetricSection - g₂.toSymmetricSection) +
        (g₂.toSymmetricSection - g₃.toSymmetricSection) :=
    (sub_add_sub_cancel _ _ _).symm
  rw [finiteAtlasDist_def, finiteAtlasDist_def, finiteAtlasDist_def, hsub]
  exact map_add_le_add _ _ _

/-- A nonnegative bound on `finiteAtlasDist` is simultaneous uniform control of all coordinate
derivatives of orders `m ≤ k` on every compact piece `K i`. -/
theorem finiteAtlasDist_le_iff (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V)
    {r : ℝ} (hr : 0 ≤ r) :
    finiteAtlasDist e U hU c K k g₁ g₂ ≤ r ↔
      ∀ i, ∀ m ≤ k, ∀ z ∈ K i,
        ‖ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) g₁.toSymmetricSection)
            (c i) m (by simp) z -
          ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) g₂.toSymmetricSection)
            (c i) m (by simp) z‖ ≤ r :=
  ContMDiffSection.finiteAtlasSeminorm_sub_le_iff e U hU c K k (by simp)
    g₂.toSymmetricSection g₁.toSymmetricSection hr

/-- A strict positive bound on `finiteAtlasDist` is simultaneous strict control of all coordinate
derivatives of orders `m ≤ k` on every compact piece `K i`. -/
theorem finiteAtlasDist_lt_iff (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V)
    {r : ℝ} (hr : 0 < r) :
    finiteAtlasDist e U hU c K k g₁ g₂ < r ↔
      ∀ i, ∀ m ≤ k, ∀ z ∈ K i,
        ‖ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) g₁.toSymmetricSection)
            (c i) m (by simp) z -
          ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) g₂.toSymmetricSection)
            (c i) m (by simp) z‖ < r := by
  rw [finiteAtlasDist_def, ← Seminorm.mem_ball]
  exact ContMDiffSection.mem_ball_finiteAtlasSeminorm_iff e U hU c K k (by simp)
    g₂.toSymmetricSection g₁.toSymmetricSection hr

/-- Increasing the derivative order increases the finite-atlas `C^k` distance. -/
theorem finiteAtlasDist_le_of_le {k l : ℕ} (hkl : k ≤ l)
    (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    finiteAtlasDist e U hU c K k g₁ g₂ ≤ finiteAtlasDist e U hU c K l g₁ g₂ :=
  ContMDiffSection.finiteAtlasSeminorm_le_of_le e U hU c K hkl (by simp) _

/-- The pseudometric space on smooth Riemannian metrics defined by `finiteAtlasDist`. -/
@[instance_reducible]
def finiteAtlasPseudoMetricSpace (k : ℕ) :
    PseudoMetricSpace (ContMDiffRiemannianMetric IB ∞ F V) where
  dist := finiteAtlasDist e U hU c K k
  dist_self := finiteAtlasDist_self e U hU c K k
  dist_comm := finiteAtlasDist_comm e U hU c K k
  dist_triangle := finiteAtlasDist_triangle e U hU c K k

variable (IB) in
/-- The `C^k` topology on smooth Riemannian metrics generated by the coordinate derivatives of
order at most `k` over a finite chart-frame atlas, with boundary and corner charts allowed. -/
@[instance_reducible]
def finiteAtlasTopology (k : ℕ) : TopologicalSpace (ContMDiffRiemannianMetric IB ∞ F V) :=
  (finiteAtlasPseudoMetricSpace e U hU c K k).toUniformSpace.toTopologicalSpace

/-- The distance of `finiteAtlasPseudoMetricSpace` is `finiteAtlasDist`. -/
theorem dist_finiteAtlasPseudoMetricSpace (k : ℕ)
    (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    letI := finiteAtlasPseudoMetricSpace e U hU c K k
    dist g₁ g₂ = finiteAtlasDist e U hU c K k g₁ g₂ :=
  (rfl)

/-- The topology underlying `finiteAtlasPseudoMetricSpace` is `finiteAtlasTopology`. -/
@[simp]
theorem topologicalSpace_finiteAtlasPseudoMetricSpace (k : ℕ) :
    (finiteAtlasPseudoMetricSpace e U hU c K k).toUniformSpace.toTopologicalSpace =
      finiteAtlasTopology IB e U hU c K k :=
  (rfl)

/-- Convergence in `finiteAtlasTopology` is convergence to zero of `finiteAtlasDist`. -/
theorem tendsto_finiteAtlasTopology_iff (k : ℕ) {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric IB ∞ F V} {g₀ : ContMDiffRiemannianMetric IB ∞ F V} :
    letI := finiteAtlasTopology IB e U hU c K k
    Tendsto g l (𝓝 g₀) ↔
      Tendsto (fun p ↦ finiteAtlasDist e U hU c K k (g p) g₀) l (𝓝 0) := by
  let _ := finiteAtlasPseudoMetricSpace e U hU c K k
  have h : @Tendsto _ _ g l (@nhds _
      (finiteAtlasPseudoMetricSpace e U hU c K k).toUniformSpace.toTopologicalSpace g₀) ↔
      Tendsto (fun p ↦ finiteAtlasDist e U hU c K k (g p) g₀) l (𝓝 0) := by
    rw [Metric.tendsto_nhds, Metric.tendsto_nhds]
    refine forall₂_congr fun ε _ ↦ eventually_congr (Eventually.of_forall fun p ↦ ?_)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (finiteAtlasDist_nonneg e U hU c K k _ _),
      dist_finiteAtlasPseudoMetricSpace]
  exact h

/-- Open sets in `finiteAtlasTopology` are characterized by positive `finiteAtlasDist` balls. -/
theorem isOpen_finiteAtlasTopology_iff (k : ℕ)
    {S : Set (ContMDiffRiemannianMetric IB ∞ F V)} :
    letI := finiteAtlasTopology IB e U hU c K k
    IsOpen S ↔ ∀ g₀ ∈ S, ∃ δ : ℝ, 0 < δ ∧
      ∀ g, finiteAtlasDist e U hU c K k g g₀ < δ → g ∈ S := by
  let _ := finiteAtlasPseudoMetricSpace e U hU c K k
  have h : @IsOpen _
      (finiteAtlasPseudoMetricSpace e U hU c K k).toUniformSpace.toTopologicalSpace S ↔
      ∀ g₀ ∈ S, ∃ δ : ℝ, 0 < δ ∧ ∀ g, finiteAtlasDist e U hU c K k g g₀ < δ → g ∈ S := by
    simp only [Metric.isOpen_iff, subset_def, Metric.mem_ball]
    rfl
  exact h

/-- Increasing `k` refines the finite-atlas `C^k` topology on smooth metrics. -/
theorem antitone_finiteAtlasTopology : Antitone (finiteAtlasTopology IB e U hU c K) := by
  intro k l hkl
  rw [TopologicalSpace.le_def]
  intro S hS
  rw [isOpen_finiteAtlasTopology_iff] at hS ⊢
  intro g₀ hg₀
  obtain ⟨δ, hδ, hball⟩ := hS g₀ hg₀
  exact ⟨δ, hδ, fun g hg ↦ hball g ((finiteAtlasDist_le_of_le e U hU c K hkl g g₀).trans_lt hg)⟩

variable {c K}

/-- When the compact pieces cover `B`, `finiteAtlasDist` separates smooth metrics. -/
theorem finiteAtlasDist_eq_zero_iff
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ K i)
    (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    finiteAtlasDist e U hU c K k g₁ g₂ = 0 ↔ g₁ = g₂ := by
  rw [finiteAtlasDist_def, ContMDiffSection.finiteAtlasSeminorm_eq_zero_iff e U hU hK k (by simp),
    sub_eq_zero, toSymmetricSection_injective.eq_iff]

/-- **Lipschitz equivalence across finite chart-frame atlases.** If the compact pieces `K i` have
relative interiors covering `B` (boundary and corner charts included), the `C^k` distance of any
other finite chart-frame atlas is bounded by a positive multiple of
`finiteAtlasDist e U hU c K k`. -/
theorem exists_finiteAtlasDist_le
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    {ι' : Type*} [Fintype ι']
    (e' : ι' → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : ι' → Opens B) (hU' : ∀ j, (U' j : Set B) ⊆ (e' j).baseSet)
    (c' : ∀ j, U' j) (K' : ∀ j, Compacts (extChartAt IB (c' j)).target) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V,
      finiteAtlasDist e' U' hU' c' K' k g₁ g₂ ≤ C * finiteAtlasDist e U hU c K k g₁ g₂ := by
  obtain ⟨C, hC, hbound⟩ := ContMDiffSection.exists_finiteAtlasSeminorm_le (n := ∞)
    e U hU hK e' U' hU' c' K' k (by simp)
  exact ⟨C, hC, fun g₁ g₂ ↦ hbound (g₁.toSymmetricSection - g₂.toSymmetricSection)⟩

private theorem finiteAtlasTopology_le_of_cover
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    {ι' : Type*} [Fintype ι']
    (e' : ι' → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : ι' → Opens B) (hU' : ∀ j, (U' j : Set B) ⊆ (e' j).baseSet)
    (c' : ∀ j, U' j) (K' : ∀ j, Compacts (extChartAt IB (c' j)).target) (k : ℕ) :
    finiteAtlasTopology IB e U hU c K k ≤ finiteAtlasTopology IB e' U' hU' c' K' k := by
  obtain ⟨C, hC, hbound⟩ := exists_finiteAtlasDist_le e U hU hK e' U' hU' c' K' k
  rw [TopologicalSpace.le_def]
  intro S hS
  rw [isOpen_finiteAtlasTopology_iff] at hS ⊢
  intro g₀ hg₀
  obtain ⟨δ, hδ, hball⟩ := hS g₀ hg₀
  refine ⟨δ / C, div_pos hδ hC, fun g hg ↦ hball g ?_⟩
  exact (hbound g g₀).trans_lt ((lt_div_iff₀' hC).mp hg)

/-- **Atlas independence of the finite-atlas `C^k` topology on smooth metrics.** Any two finite
chart-frame atlases whose compact coordinate pieces have relative interiors covering `B` define the
same `C^k` topology on smooth metrics, with boundary and corner charts included and without any
local compactness or boundarylessness assumption. -/
theorem finiteAtlasTopology_eq_of_covers
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    {ι' : Type*} [Fintype ι']
    (e' : ι' → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : ι' → Opens B) (hU' : ∀ j, (U' j : Set B) ⊆ (e' j).baseSet)
    {c' : ∀ j, U' j} {K' : ∀ j, Compacts (extChartAt IB (c' j)).target}
    (hK' : ∀ y : B, ∃ j, ∃ hyU : y ∈ U' j,
      ∃ hy : (⟨y, hyU⟩ : U' j) ∈ (extChartAt IB (c' j)).source,
        (⟨extChartAt IB (c' j) ⟨y, hyU⟩, (extChartAt IB (c' j)).map_source hy⟩ :
          (extChartAt IB (c' j)).target) ∈ interior (K' j : Set (extChartAt IB (c' j)).target))
    (k : ℕ) :
    finiteAtlasTopology IB e U hU c K k = finiteAtlasTopology IB e' U' hU' c' K' k :=
  le_antisymm (finiteAtlasTopology_le_of_cover e U hU hK e' U' hU' c' K' k)
    (finiteAtlasTopology_le_of_cover e' U' hU' hK' e U hU c K k)

private theorem finiteAtlasSeminorm_ofLE_sub (c : ∀ i, U i)
    (K : ∀ i, Compacts (extChartAt IB (c i)).target) (k : ℕ)
    (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    ContMDiffSection.finiteAtlasSeminorm (n := k) e U hU c K k le_rfl
        ((g₁.ofLE (m := k) (by simp)).toSymmetricSection -
          (g₂.ofLE (m := k) (by simp)).toSymmetricSection) =
      finiteAtlasDist e U hU c K k g₁ g₂ := by
  have hjet (i : ι) (m : ℕ) (hm : m ≤ k) (z : (extChartAt IB (c i)).target) :
      ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i)
          ((g₁.ofLE (m := k) (by simp)).toSymmetricSection -
            (g₂.ofLE (m := k) (by simp)).toSymmetricSection))
        (c i) m ((Nat.cast_le.mpr hm).trans le_rfl) z =
      ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i)
          (g₁.toSymmetricSection - g₂.toSymmetricSection))
        (c i) m ((Nat.cast_le.mpr hm).trans (by simp)) z := by
    have hc : ⇑((e i).frameCoordinates (hU i)
        ((g₁.ofLE (m := k) (by simp)).toSymmetricSection -
          (g₂.ofLE (m := k) (by simp)).toSymmetricSection)) =
        ⇑((e i).frameCoordinates (hU i) (g₁.toSymmetricSection - g₂.toSymmetricSection)) := by
      funext y
      simp only [map_sub, ContMDiffMap.coe_sub, Pi.sub_apply, Trivialization.frameCoordinates_apply,
        toSymmetricSection_ofLE_apply]
    simp only [ContMDiffMap.chartIteratedFDeriv_self_target_apply, hc]
  apply le_antisymm
  · refine (ContMDiffSection.finiteAtlasSeminorm_le_iff e U hU c K k le_rfl _
      (finiteAtlasDist_nonneg e U hU c K k g₁ g₂)).mpr fun i m hm z hz ↦ ?_
    rw [hjet i m hm z]
    exact (ContMDiffSection.finiteAtlasSeminorm_le_iff e U hU c K k (by simp) _
      (finiteAtlasDist_nonneg e U hU c K k g₁ g₂)).mp le_rfl i m hm z hz
  · refine (ContMDiffSection.finiteAtlasSeminorm_le_iff e U hU c K k (by simp) _
      (apply_nonneg _ _)).mpr fun i m hm z hz ↦ ?_
    rw [← hjet i m hm z]
    exact (ContMDiffSection.finiteAtlasSeminorm_le_iff e U hU c K k le_rfl _
      (apply_nonneg _ _)).mp le_rfl i m hm z hz

/-- **The finite-atlas `C^k` topology coincides with `frameCkTopology`.** Whenever the compact
coordinate pieces have relative interiors covering `B` (boundary and corner charts included),
`finiteAtlasTopology` equals the finite-order section topology `frameCkTopology`. -/
theorem finiteAtlasTopology_eq_frameCkTopology
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    (k : ℕ) :
    finiteAtlasTopology IB e U hU c K k = frameCkTopology IB e U hU k := by
  let φ : ContMDiffRiemannianMetric IB ∞ F V →
      Cₛ^k⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯ :=
    fun g ↦ (g.ofLE (m := k) (by simp)).toSymmetricSection
  let mS := ContMDiffSection.finiteAtlasNormedAddCommGroup (𝕜 := ℝ) k e U hU hK
  have hm : finiteAtlasPseudoMetricSpace e U hU c K k =
      PseudoMetricSpace.induced φ mS.toPseudoMetricSpace := by
    refine PseudoMetricSpace.ext ?_
    ext g₁ g₂
    exact ((ContMDiffSection.dist_finiteAtlas k e U hU hK (φ g₁) (φ g₂)).trans
      (finiteAtlasSeminorm_ofLE_sub e U hU c K k g₁ g₂)).symm
  have hframe : frameTopology IB k e U hU =
      .induced toSymmetricSection (ContMDiffSection.frameTopology (I := IB) (n := k) e U hU) := by
    let _ := ContMDiffSection.frameTopology (I := IB) (n := k) e U hU
    let _ := frameTopology IB k e U hU
    exact (isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := k) e U hU).eq_induced
  calc finiteAtlasTopology IB e U hU c K k
      = (PseudoMetricSpace.induced φ mS.toPseudoMetricSpace).toUniformSpace.toTopologicalSpace :=
        congrArg (fun m ↦ m.toUniformSpace.toTopologicalSpace) hm
    _ = .induced φ mS.toUniformSpace.toTopologicalSpace := rfl
    _ = .induced φ (ContMDiffSection.frameTopology (I := IB) (n := k) e U hU) := by
        rw [ContMDiffSection.topologicalSpace_finiteAtlasNormedAddCommGroup k e U hU hK]
    _ = frameCkTopology IB e U hU k := by
        rw [frameCkTopology_def, hframe, induced_compose]
        rfl

/-- On a locally compact model space (such as Euclidean half-space), any finite chart-frame atlas
with covering relative interiors generates `frameCkTopology` for *any* covering smooth frame
system. -/
theorem finiteAtlasTopology_eq_frameCkTopology_of_cover [LocallyCompactSpace EB]
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    {κ : Type*}
    (e' : κ → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens B) (hU' : ∀ j, (U' j : Set B) ⊆ (e' j).baseSet)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) (k : ℕ) :
    finiteAtlasTopology IB e U hU c K k = frameCkTopology IB e' U' hU' k := by
  have hcover : ∀ x, ∃ i, x ∈ U i := fun x ↦ let ⟨i, hx, _⟩ := hK x; ⟨i, hx⟩
  rw [finiteAtlasTopology_eq_frameCkTopology e U hU hK k,
    frameCkTopology_eq_of_covers e U hU k hcover e' U' hU' hcover']

/-- The metric space structure on smooth Riemannian metrics for a finite chart-frame atlas with
covering relative interiors, carrying `frameCkTopology` as its underlying topology and
`finiteAtlasDist` as its distance. -/
@[instance_reducible]
def finiteAtlasMetricSpace
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    (k : ℕ) : MetricSpace (ContMDiffRiemannianMetric IB ∞ F V) :=
  letI := frameCkTopology IB e U hU k
  MetricSpace.replaceTopology
    { finiteAtlasPseudoMetricSpace e U hU c K k with
      eq_of_dist_eq_zero := (finiteAtlasDist_eq_zero_iff e U hU
        (fun y ↦ (hK y).imp fun _ ⟨hyU, hy, hyK⟩ ↦ ⟨hyU, hy, interior_subset hyK⟩) k _ _).mp }
    (finiteAtlasTopology_eq_frameCkTopology e U hU hK k).symm

/-- The distance in `finiteAtlasMetricSpace` is `finiteAtlasDist`. -/
theorem dist_finiteAtlasMetricSpace
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    (k : ℕ) (g₁ g₂ : ContMDiffRiemannianMetric IB ∞ F V) :
    letI := finiteAtlasMetricSpace e U hU hK k
    dist g₁ g₂ = finiteAtlasDist e U hU c K k g₁ g₂ :=
  (rfl)

/-- The topology underlying `finiteAtlasMetricSpace` is `frameCkTopology`. -/
@[simp]
theorem topologicalSpace_finiteAtlasMetricSpace
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    (k : ℕ) :
    (finiteAtlasMetricSpace e U hU hK k).toUniformSpace.toTopologicalSpace =
      frameCkTopology IB e U hU k :=
  (rfl)

/-- Convergence in `frameCkTopology` is convergence in `finiteAtlasDist`. -/
theorem tendsto_frameCkTopology_iff_finiteAtlasDist
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    (k : ℕ) {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric IB ∞ F V} {g₀ : ContMDiffRiemannianMetric IB ∞ F V} :
    letI := frameCkTopology IB e U hU k
    Tendsto g l (𝓝 g₀) ↔
      Tendsto (fun p ↦ finiteAtlasDist e U hU c K k (g p) g₀) l (𝓝 0) := by
  rw [← finiteAtlasTopology_eq_frameCkTopology e U hU hK k]
  exact tendsto_finiteAtlasTopology_iff e U hU c K k

/-- Openness in `frameCkTopology` is characterized by positive `finiteAtlasDist` margins. -/
theorem isOpen_frameCkTopology_iff_finiteAtlasDist
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    (k : ℕ) {S : Set (ContMDiffRiemannianMetric IB ∞ F V)} :
    letI := frameCkTopology IB e U hU k
    IsOpen S ↔ ∀ g₀ ∈ S, ∃ δ : ℝ, 0 < δ ∧
      ∀ g, finiteAtlasDist e U hU c K k g g₀ < δ → g ∈ S := by
  rw [← finiteAtlasTopology_eq_frameCkTopology e U hU hK k]
  exact isOpen_finiteAtlasTopology_iff e U hU c K k

/-- **Uniform `C^k` margin around a compact set of metrics.** If `L` is compact in
`frameCkTopology` and contained in a `frameCkTopology`-open set `S` of smooth metrics (for instance
on a compact manifold with boundary on the half-space model), there is a uniform `δ > 0` such that
every smooth metric within `finiteAtlasDist ... k < δ` of any metric in `L` belongs to `S`. -/
theorem _root_.IsCompact.exists_pos_forall_mem_of_isOpen_frameCkTopology
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    (k : ℕ) {L S : Set (ContMDiffRiemannianMetric IB ∞ F V)}
    (hL : @IsCompact _ (frameCkTopology IB e U hU k) L)
    (hS : @IsOpen _ (frameCkTopology IB e U hU k) S) (hLS : L ⊆ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g₀ ∈ L, ∀ g, finiteAtlasDist e U hU c K k g g₀ < δ → g ∈ S := by
  let _ := finiteAtlasMetricSpace e U hU hK k
  obtain ⟨δ, hδ, hthick⟩ := hL.exists_thickening_subset_open hS hLS
  refine ⟨δ, hδ, fun g₀ hg₀ g hdist ↦ hthick ?_⟩
  exact Metric.mem_thickening_iff.mpr ⟨g₀, hg₀, hdist⟩

/-- **Metrizability of `frameCkTopology` on a compact manifold.** On a compact manifold modelled on
a locally compact space (including compact manifolds with boundary on the half-space model),
`frameCkTopology` is metrizable for every covering smooth frame system. -/
theorem metrizableSpace_frameCkTopology_of_compactSpace [CompactSpace B] [LocallyCompactSpace EB]
    {κ : Type*}
    (e' : κ → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens B) (hU' : ∀ j, (U' j : Set B) ⊆ (e' j).baseSet)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) (k : ℕ) :
    letI := frameCkTopology IB e' U' hU' k
    MetrizableSpace (ContMDiffRiemannianMetric IB ∞ F V) := by
  let _ := IB.locallyCompactSpace
  obtain ⟨N, r, c₀, K₀, hK₀⟩ := TauCeti.exists_finite_compact_opens_chart_cover (I := IB) U' hcover'
  have heq := finiteAtlasTopology_eq_frameCkTopology_of_cover
    (fun i ↦ e' (r i)) (fun i ↦ U' (r i)) (fun i ↦ hU' (r i)) hK₀ e' U' hU' hcover' k
  let m := finiteAtlasMetricSpace (fun i ↦ e' (r i)) (fun i ↦ U' (r i)) (fun i ↦ hU' (r i)) hK₀ k
  have hm : m.toUniformSpace.toTopologicalSpace = frameCkTopology IB e' U' hU' k :=
    (finiteAtlasTopology_eq_frameCkTopology _ _ _ hK₀ k).symm.trans heq
  let _ := m
  have : MetrizableSpace (ContMDiffRiemannianMetric IB ∞ F V) := inferInstance
  rwa [hm] at this

/-! ### Comparison of the `C^∞` topology with finite-atlas `C^k` distances -/

/-- Convergence of smooth metrics in `frameTopology IB ∞` is convergence in `finiteAtlasDist ... k`
for every finite derivative order `k : ℕ`. -/
theorem tendsto_frameTopology_infty_iff_finiteAtlasDist
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric IB ∞ F V} {g₀ : ContMDiffRiemannianMetric IB ∞ F V} :
    letI := frameTopology IB ∞ e U hU
    Tendsto g l (𝓝 g₀) ↔
      ∀ k : ℕ, Tendsto (fun p ↦ finiteAtlasDist e U hU c K k (g p) g₀) l (𝓝 0) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := ∞) e U hU
  let _ := frameTopology IB ∞ e U hU
  have hp := ContMDiffSection.withSeminorms_finiteAtlasSeminorm_infty e U hU hK
  let _ := hp.isTopologicalAddGroup
  refine (tendsto_frameTopology_iff (IB := IB) (n := ∞) e U hU).trans ?_
  rw [hp.tendsto_nhds]
  refine forall_congr' fun k ↦ ?_
  rw [Metric.tendsto_nhds]
  refine forall₂_congr fun ε _ ↦ eventually_congr (Eventually.of_forall fun p ↦ ?_)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (finiteAtlasDist_nonneg e U hU c K k _ _),
    finiteAtlasDist_def]

/-- Open sets in `frameTopology IB ∞` are characterized by finite-order `finiteAtlasDist` balls. -/
theorem isOpen_frameTopology_infty_iff_finiteAtlasDist
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target))
    {S : Set (ContMDiffRiemannianMetric IB ∞ F V)} :
    letI := frameTopology IB ∞ e U hU
    IsOpen S ↔ ∀ g₀ ∈ S, ∃ (k : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ g, finiteAtlasDist e U hU c K k g g₀ < δ → g ∈ S := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := ∞) e U hU
  let _ := frameTopology IB ∞ e U hU
  let p : ℕ → Seminorm ℝ Cₛ^∞⟮IB; symmetricBilinearMaps ℝ F ℝ,
      fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯ :=
    fun k ↦ ContMDiffSection.finiteAtlasSeminorm (n := ∞) e U hU c K k (by simp)
  have hp : WithSeminorms p := ContMDiffSection.withSeminorms_finiteAtlasSeminorm_infty e U hU hK
  have hemb := isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := ∞) e U hU
  rw [isOpen_iff_mem_nhds]
  refine forall₂_congr fun g₀ _ ↦ ?_
  rw [hemb.isInducing.nhds_eq_comap, Filter.mem_comap]
  constructor
  · rintro ⟨T, hT, hpre⟩
    obtain ⟨s, δ, hδ, hball⟩ := (hp.mem_nhds_iff g₀.toSymmetricSection T).mp hT
    refine ⟨s.sup id, δ, hδ, fun g hg ↦ hpre (hball ?_)⟩
    rw [Seminorm.mem_ball]
    have hsup : s.sup p ≤ p (s.sup id) := Finset.sup_le fun j hj ↦
      ContMDiffSection.finiteAtlasSeminorm_le_of_le e U hU c K
        (Finset.le_sup (f := id) hj) (by simp)
    exact (hsup _).trans_lt hg
  · rintro ⟨k, δ, hδ, hball⟩
    refine ⟨(p k).ball g₀.toSymmetricSection δ, ?_, fun g hg ↦ ?_⟩
    · exact (hp.mem_nhds_iff g₀.toSymmetricSection _).mpr
        ⟨{k}, δ, hδ, by simp only [Finset.sup_singleton, Subset.rfl]⟩
    · rw [Set.mem_preimage, Seminorm.mem_ball] at hg
      exact hball g hg

/-- **The `C^∞` section topology on smooth metrics is the infimum of the finite-atlas `C^k`
topologies.** -/
theorem frameTopology_infty_eq_iInf_finiteAtlasTopology
    (hK : ∀ y : B, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt IB (c i)).source,
        (⟨extChartAt IB (c i) ⟨y, hyU⟩, (extChartAt IB (c i)).map_source hy⟩ :
          (extChartAt IB (c i)).target) ∈ interior (K i : Set (extChartAt IB (c i)).target)) :
    frameTopology IB ∞ e U hU = ⨅ k : ℕ, finiteAtlasTopology IB e U hU c K k := by
  apply le_antisymm
  · exact le_iInf fun k ↦ (frameTopology_le_frameCkTopology e U hU k).trans_eq
      (finiteAtlasTopology_eq_frameCkTopology e U hU hK k).symm
  · rw [TopologicalSpace.le_def]
    intro S hS
    let _ : TopologicalSpace (ContMDiffRiemannianMetric IB ∞ F V) :=
      ⨅ k : ℕ, finiteAtlasTopology IB e U hU c K k
    rw [isOpen_iff_mem_nhds]
    intro g₀ hg₀
    obtain ⟨k, δ, hδ, hball⟩ :=
      (isOpen_frameTopology_infty_iff_finiteAtlasDist e U hU hK).mp hS g₀ hg₀
    have hopen : @IsOpen _ (finiteAtlasTopology IB e U hU c K k)
        {g | finiteAtlasDist e U hU c K k g g₀ < δ} := by
      let _ := finiteAtlasPseudoMetricSpace e U hU c K k
      exact Metric.isOpen_ball
    exact Filter.mem_of_superset
      ((hopen.mono (iInf_le _ k)).mem_nhds (by simp [hδ])) fun g hg ↦ hball g hg

end FiniteAtlasDist

/-! ### Comparison with the boundaryless chart `C^k`, `C²`, and `C^∞` topologies -/

section BoundarylessChartComparison

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
    (π (symmetricBilinearMaps ℝ E ℝ) (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt I (c i)).target}

/-- **The boundaryless chart `C^k` topology agrees with `finiteAtlasTopology`.** On a manifold
without boundary modelled on a locally compact space, `chartCkTopology k` equals the finite-atlas
`C^k` topology of any finite chart-frame atlas of `Sym²(T*M)` whose compact pieces have relative
interiors covering `M`. -/
theorem chartCkTopology_eq_finiteAtlasTopology
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))
    (k : ℕ) :
    chartCkTopology (I := I) (M := M) k = finiteAtlasTopology I e U hU c K k := by
  have hcover : ∀ x, ∃ i, x ∈ U i := fun x ↦ let ⟨i, hx, _⟩ := hK x; ⟨i, hx⟩
  rw [chartCkTopology_eq_frameCkTopology k e U hU hcover,
    finiteAtlasTopology_eq_frameCkTopology e U hU hK k]

/-- **The boundaryless chart `C²` topology agrees with the finite-atlas `C²` topology.** -/
theorem chartC2Topology_eq_finiteAtlasTopology
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target)) :
    chartC2Topology (I := I) (M := M) = finiteAtlasTopology I e U hU c K 2 :=
  chartCkTopology_eq_finiteAtlasTopology e U hU hK 2

/-- **The boundaryless chart `C^∞` topology is the infimum of the finite-atlas `C^k`
topologies.** -/
theorem chartCInftyTopology_eq_iInf_finiteAtlasTopology
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target)) :
    chartCInftyTopology (I := I) (M := M) = ⨅ k : ℕ, finiteAtlasTopology I e U hU c K k := by
  have hcover : ∀ x, ∃ i, x ∈ U i := fun x ↦ let ⟨i, hx, _⟩ := hK x; ⟨i, hx⟩
  rw [chartCInftyTopology_eq_frameTopology e U hU hcover,
    frameTopology_infty_eq_iInf_finiteAtlasTopology e U hU hK]

/-- Convergence of smooth metrics in `chartCInftyTopology` is convergence in `finiteAtlasDist ... k`
for every `k : ℕ`. -/
theorem tendsto_chartCInftyTopology_iff_finiteAtlasDist
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))
    {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    letI := chartCInftyTopology (I := I) (M := M)
    Tendsto g l (𝓝 g₀) ↔
      ∀ k : ℕ, Tendsto (fun p ↦ finiteAtlasDist e U hU c K k (g p) g₀) l (𝓝 0) := by
  have hcover : ∀ x, ∃ i, x ∈ U i := fun x ↦ let ⟨i, hx, _⟩ := hK x; ⟨i, hx⟩
  rw [chartCInftyTopology_eq_frameTopology e U hU hcover]
  exact tendsto_frameTopology_infty_iff_finiteAtlasDist e U hU hK

/-- Open sets in `chartCInftyTopology` are characterized by finite-order `finiteAtlasDist` balls. -/
theorem isOpen_chartCInftyTopology_iff_finiteAtlasDist
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))
    {S : Set (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))} :
    letI := chartCInftyTopology (I := I) (M := M)
    IsOpen S ↔ ∀ g₀ ∈ S, ∃ (k : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ g, finiteAtlasDist e U hU c K k g g₀ < δ → g ∈ S := by
  have hcover : ∀ x, ∃ i, x ∈ U i := fun x ↦ let ⟨i, hx, _⟩ := hK x; ⟨i, hx⟩
  rw [chartCInftyTopology_eq_frameTopology e U hU hcover]
  exact isOpen_frameTopology_infty_iff_finiteAtlasDist e U hU hK

end BoundarylessChartComparison

end Bundle.ContMDiffRiemannianMetric
