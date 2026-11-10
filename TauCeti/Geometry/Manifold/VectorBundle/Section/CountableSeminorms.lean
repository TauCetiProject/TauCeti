/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CountableSeminorms

/-!
# Countable compact frame seminorms

For a countable specified frame system, countable covering chart systems and compact
exhaustions give a countable family of native section seminorms generating exactly
`ContMDiffSection.frameTopology`. If the frames cover, this topology is Hausdorff and
metrizable. The family retains every finite derivative order allowed by the section
regularity, including order zero. Empty domains and empty covering systems are allowed.

The finite-cover coordinate estimate is proved for vector-valued maps in
`ContMDiffMap.Chart.CountableSeminorms`. Here it is pulled back through the existing
frame-coordinate map, using Mathlib's induced and product `WithSeminorms` theorems.
There is no assertion of completeness or comparison with another frame system.

## References

* M. Hirsch, *Differential Topology*, Chapter 2, §1.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {κ : ι → Type*} (c : ∀ i, κ i → U i)
  (A : ∀ i j, CompactExhaustion (extChartAt I (c i j)).target)

/-- The existing compact chart seminorms of the frame coefficients, indexed by a frame,
a selected chart, a compact-exhaustion stage, and an admissible finite derivative order. -/
def frameExhaustionSeminormFamily :
    SeminormFamily 𝕜 Cₛ^n⟮I; F, V⟯ (Σ i, κ i × ℕ × {k : ℕ // k ≤ n}) :=
  SeminormFamily.sigma fun i ↦
    (ContMDiffMap.chartExhaustionSeminormFamily (F := F) (c i) (A i)).comp
      ((e i).frameCoordinates (hU i))

/-- Every entry is one of the existing compact frame seminorms. -/
@[simp]
theorem frameExhaustionSeminormFamily_apply (i : ι) (j : κ i) (l k : ℕ) (hk : k ≤ n)
    (s : Cₛ^n⟮I; F, V⟯) :
    frameExhaustionSeminormFamily e U hU c A ⟨i, j, l, ⟨k, hk⟩⟩ s =
      (e i).chartCkSeminorm (hU i) (c i j) ⟨A i j l, (A i j).isCompact l⟩ k hk s := by
  simp only [frameExhaustionSeminormFamily, SeminormFamily.sigma,
    SeminormFamily.comp_apply, Seminorm.comp_apply,
    ContMDiffMap.chartExhaustionSeminormFamily_apply,
    Bundle.Trivialization.chartCkSeminorm_apply]

/-- The countable frame seminorm family generates exactly the original frame topology.
This does not require that the specified frame domains cover the base. -/
theorem withSeminorms_frameExhaustion
    (hchart : ∀ i (x : U i), ∃ j, x ∈ (extChartAt I (c i j)).source) :
    let _ := frameTopology (I := I) (n := n) e U hU
    WithSeminorms (frameExhaustionSeminormFamily (n := n) e U hU c A) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hp := withSeminorms_pi fun i ↦
    ContMDiffMap.withSeminorms_chartExhaustion (F := F) (n := n) (c i) (hchart i) (A i)
  have h := (isInducing_sectionFrameCoordinates (I := I) (n := n) e U hU).withSeminorms hp
  convert h using 1
  ext j s
  simp only [frameExhaustionSeminormFamily, SeminormFamily.sigma,
    SeminormFamily.comp_apply, Seminorm.comp_apply]
  congr 1
  ext x
  simp only [LinearMap.proj_apply, TauCeti.Manifold.sectionFrameCoordinates_apply,
    Bundle.Trivialization.frameCoordinates_apply]


include A in
/-- The fixed frame topology is first countable when the frame and covering chart indices
are countable. Coverage of the whole base is not required for this certificate. -/
theorem firstCountableTopology_frameExhaustion [Countable ι] [∀ i, Countable (κ i)]
    (hchart : ∀ i (x : U i), ∃ j, x ∈ (extChartAt I (c i j)).source) :
    let _ := frameTopology (I := I) (n := n) e U hU
    FirstCountableTopology Cₛ^n⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (withSeminorms_frameExhaustion e U hU c A hchart).firstCountableTopology

include A in
/-- A countable covering frame system with countable covering chart systems and compact
exhaustions gives a compatible metrizable topology on the same native section space. -/
theorem metrizableSpace_frameExhaustion [Countable ι] [∀ i, Countable (κ i)]
    (hchart : ∀ i (x : U i), ∃ j, x ∈ (extChartAt I (c i j)).source)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    MetrizableSpace Cₛ^n⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hp := withSeminorms_frameExhaustion (n := n) e U hU c A hchart
  let _ := hp.isTopologicalAddGroup
  let _ := hp.firstCountableTopology
  let _ := t2Space_frameTopology (I := I) (n := n) e U hU hcover
  let _ : UniformSpace Cₛ^n⟮I; F, V⟯ := IsTopologicalAddGroup.rightUniformSpace _
  let _ : IsUniformAddGroup Cₛ^n⟮I; F, V⟯ := isUniformAddGroup_of_addCommGroup
  let _ : (uniformity Cₛ^n⟮I; F, V⟯).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.metrizableSpace


/-- On sigma-compact frame domains, select actual countable covering chart centres and
compact exhaustions whose native frame seminorms generate the specified frame topology.
The empty-domain case uses an empty subtype, without choosing a point. -/
theorem exists_countable_frameExhaustion
    [LocallyCompactSpace E] [SecondCountableTopology E]
    [∀ i, SigmaCompactSpace (U i)] :
    ∃ s : ∀ i, Set (U i), (∀ i, (s i).Countable) ∧
      (∀ i (x : U i), ∃ j : s i, x ∈ (extChartAt I (j : U i)).source) ∧
      ∃ A : ∀ i (j : s i), CompactExhaustion (extChartAt I (j : U i)).target,
        let _ := frameTopology (I := I) (n := n) e U hU
        WithSeminorms (frameExhaustionSeminormFamily (n := n) e U hU
          (fun i (j : s i) ↦ (j : U i)) A) := by
  choose s hs hcover using fun i ↦ countable_cover_nhds_of_sigmaCompact
    (fun x : U i ↦ extChartAt_source_mem_nhds (I := I) x)
  have hc : ∀ i (x : U i), ∃ j : s i, x ∈ (extChartAt I (j : U i)).source := by
    intro i x
    have hx : x ∈ ⋃ y ∈ s i, (extChartAt I y).source := by rw [hcover]; trivial
    obtain ⟨y, hy, hx⟩ := mem_iUnion₂.mp hx
    exact ⟨⟨y, hy⟩, hx⟩
  let _ (i : ι) (j : s i) : LocallyCompactSpace (extChartAt I (j : U i)).target := by
    rw [extChartAt_target]
    exact ((chartAt H (j : U i)).open_target.preimage I.continuous_symm).isLocallyClosed.inter
      I.isClosed_range.isLocallyClosed |>.locallyCompactSpace
  let A (i : ι) (j : s i) := CompactExhaustion.choice (extChartAt I (j : U i)).target
  exact ⟨s, hs, hc, A, withSeminorms_frameExhaustion (n := n) e U hU
    (fun i (j : s i) ↦ (j : U i)) A hc⟩

/-- Countable covering frames on sigma-compact domains give metrizability of the same native
frame topology on a manifold with locally compact, second-countable model, including
manifolds with boundary and corners. -/
theorem metrizableSpace_frameTopology_of_sigmaCompactDomains [Countable ι]
    [LocallyCompactSpace E] [SecondCountableTopology E]
    [∀ i, SigmaCompactSpace (U i)] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    MetrizableSpace Cₛ^n⟮I; F, V⟯ := by
  obtain ⟨s, hs, hc, A, -⟩ := exists_countable_frameExhaustion (I := I) (n := n) e U hU
  let _ (i : ι) := (hs i).to_subtype
  exact metrizableSpace_frameExhaustion (n := n) e U hU
    (fun i (j : s i) ↦ (j : U i)) A hc hcover

end ContMDiffSection
