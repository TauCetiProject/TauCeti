/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density

/-!
# Lowering the order of Sobolev `(0,1)`-forms has dense range

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`.
For `1 ≤ p < ∞`, the inclusion `W^{k+d,p}(Σ, Λ^{0,1} ⊗ V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)` forgetting `d`
weak derivatives (`TauCeti.zeroOneLowerOrdersL`) has dense range
(`TauCeti.denseRange_zeroOneLowerOrdersL`): the `(0,1)`-projection is onto and commutes with
lowering the order, and lowering the order of one-forms has dense range
(`TauCeti.SobolevSection.denseRange_lowerOrdersL`).
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneDensity : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V) (μ : Measure ℂ)
  [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ)

/-- **Lowering the order of `(0,1)`-forms has dense range.** For `1 ≤ p < ∞`, the `W^{k+d,p}`
`(0,1)`-forms are dense in the `W^{k,p}` `(0,1)`-forms. -/
theorem denseRange_zeroOneLowerOrdersL (hp : p ≠ ⊤) (d : ℕ) :
    DenseRange (zeroOneLowerOrdersL A μ p k d) := by
  have h := (zeroOnePartSobolevL_surjective (A := A) (μ := μ) (p := p) (k := k)).denseRange.comp
    (SobolevSection.denseRange_lowerOrdersL A.tangentHom μ p k hp d)
    (zeroOnePartSobolevL A μ p k).continuous
  refine h.mono ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨_, zeroOneLowerOrdersL_zeroOnePartSobolevL d w⟩

end TauCeti
