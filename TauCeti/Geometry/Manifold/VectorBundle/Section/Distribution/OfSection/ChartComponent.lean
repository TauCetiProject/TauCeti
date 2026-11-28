/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartComponent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.OfSection

/-!
# Chart components of the distributional section of a section

Let `u` be a locally integrable section of a smooth vector bundle `W → M` with model fibre `G`
(`TauCeti.LocallyIntegrableSection`), and `TauCeti.BundleDistribution.ofSection I G u` its
distributional section. In a restriction `c` of the preferred chart at `α` and the preferred frame
of the dual-density bundle `W →L |Λ|`, the component of `ofSection I G u` along a covector
`v : G →L[ℝ] ℝ` (`Bundle.Trivialization.chartComponent`) is the regular distribution of
`y ↦ v (u read at y)`, Mathlib's `Distribution.ofFun`, for the Haar measure of the fixed basis of
the model (`TauCeti.chartComponent_ofSection`). This is the form in which local regularity of
`ofSection I G u` (`TauCeti.BundleTest.IsLocallySobolevAt`) is read off from the readings of `u`.
-/

public section

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Distributions

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
  {u : (x : M) → W x} {α : M} (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
  (hct : c.source ⊆ (trivializationAt (G →L[ℝ] ℝ)
    (fun x ↦ W x →L[ℝ] DensityBundle I M x) α).baseSet)

/-- **Chart components of `ofSection`.** In a restriction `c` of the preferred chart at `α` and the
preferred frame of the dual-density bundle, the component along `v` of the distributional section
of a locally integrable section `u` is the regular distribution of `y ↦ v (u read at y)`, for the
Haar measure of the fixed basis of the model. -/
theorem chartComponent_ofSection (hcα : ∀ x ∈ c.source, c x = extChartAt I α x)
    (hu : LocallyIntegrableSection I G u) (v : G →L[ℝ] ℝ) :
    (trivializationAt (G →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] DensityBundle I M x) α).chartComponent
        c hc hct (BundleDistribution.ofSection I G u) v =
      Distribution.ofFun ⟨c.target, c.open_target⟩
        (fun y ↦ (v (FirstJetBundle.localRep I G u α y) : ℂ)) (Module.finBasis ℝ E).addHaar ⊤ := by
  have hloc : LocallyIntegrableOn (fun y ↦ (v (FirstJetBundle.localRep I G u α y) : ℂ)) c.target
      (Module.finBasis ℝ E).addHaar :=
    ((Complex.ofRealCLM.comp v).locallyIntegrableOn_comp
      (hu.locallyIntegrableOn_target c hct hcα))
  ext φ
  rw [Bundle.Trivialization.chartComponent_apply,
    ← Bundle.Trivialization.chartDistributionCLM_apply_apply,
    chartDistributionCLM_ofSection_apply_apply c hc hct hcα hu, Distribution.ofFun_apply hloc,
    ← integral_complex_ofReal]
  simp [Complex.real_smul]

end TauCeti
