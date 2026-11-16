/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms

/-!
# The compact frame seminorms generate the frame topology

For a frame system `e` with open frame domains `U`, `ContMDiffSection.frameSeminormFamily` is
the family of all compact chart derivative seminorms of the frame coefficients of a section,
indexed by a frame, a chart centre in its domain, an admissible derivative order and a compact
coordinate set. It generates `ContMDiffSection.frameTopology`
(`ContMDiffSection.withSeminorms_frameSeminormFamily`), with no countability or local
compactness assumption, so Mathlib's `WithSeminorms` API applies to the frame topology.
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

/-- All compact chart derivative seminorms of the frame coefficients, indexed by a frame, a chart
centre in its domain, an admissible derivative order, and a compact coordinate set. -/
def frameSeminormFamily :
    SeminormFamily 𝕜 Cₛ^n⟮I; F, V⟯
      (Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target) :=
  SeminormFamily.sigma fun i ↦
    (ContMDiffMap.chartSeminormFamily (I := I) (M := U i) (F := F) (n := n)).comp
      ((e i).frameCoordinates (hU i))

/-- Every entry is one of the existing compact frame derivative seminorms. -/
@[simp]
theorem frameSeminormFamily_apply (i : ι) (x : U i) (m : ℕ) (hm : m ≤ n)
    (K : Compacts (extChartAt I x).target) :
    frameSeminormFamily (I := I) (n := n) e U hU ⟨i, x, ⟨m, hm⟩, K⟩ =
      (e i).chartDerivativeSeminorm (hU i) x K m hm := by
  ext s
  simp only [frameSeminormFamily, SeminormFamily.sigma, SeminormFamily.comp_apply,
    Seminorm.comp_apply, ContMDiffMap.chartSeminormFamily_apply,
    ContMDiffMap.chartDerivativeSeminorm_apply, Trivialization.chartDerivativeSeminorm_apply]

/-- All compact frame derivative seminorms generate exactly the frame topology. Neither
countability of the frames nor local compactness of the model is needed. -/
theorem withSeminorms_frameSeminormFamily :
    let _ := frameTopology (I := I) (n := n) e U hU
    WithSeminorms (frameSeminormFamily (I := I) (n := n) e U hU) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hp := withSeminorms_pi fun i ↦
    ContMDiffMap.withSeminorms_manifoldWeakWhitney (I := I) (M := U i) (F := F) (n := n)
  have h := (isInducing_sectionFrameCoordinates (I := I) (n := n) e U hU).withSeminorms hp
  convert h using 1
  ext j s
  simp only [frameSeminormFamily, SeminormFamily.sigma, SeminormFamily.comp_apply,
    Seminorm.comp_apply]
  congr 1
  ext x
  simp only [LinearMap.proj_apply, TauCeti.Manifold.sectionFrameCoordinates_apply,
    Bundle.Trivialization.frameCoordinates_apply]

end ContMDiffSection
