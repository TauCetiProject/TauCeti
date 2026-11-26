/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic

/-!
# Rellich compactness for native Sobolev `(0,1)`-forms

On a compact Hausdorff complex curve without boundary, the canonical inclusion
`zeroOneLowerOrdersL A μ p k (d + 1)` from order `k + d + 1` to order `k` is compact for
`1 ≤ p < ∞`. It is the restriction of the canonical Sobolev order inclusion to the closed native
subspaces `zeroOneSobolevSections`; the complex bundle is smooth as a real vector bundle.

## Main results

* `TauCeti.isCompactOperator_zeroOneLowerOrdersL`: compactness for every positive loss of order.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal TauCeti.ComplexManifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

attribute [local instance] instVectorBundleRealZeroOneForm

variable {A : FiniteBundleAtlas ℂ M F V} {μ : Measure ℂ} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {k : ℕ}

variable [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

variable (A μ p k)

/-- The native inclusion of `(0,1)`-forms with any positive loss of order is compact for every
exponent `p`. -/
theorem isCompactOperator_zeroOneLowerOrdersL (d : ℕ) :
    IsCompactOperator (zeroOneLowerOrdersL A μ p k (d + 1)) := by
  rw [coeFn_zeroOneLowerOrdersL_eq_codRestrict]
  exact ((SobolevSection.isCompactOperator_lowerOrdersL A.tangentHom μ p k d).comp_clm
    (zeroOneSobolevSections A μ p (k + (d + 1))).subtypeL).codRestrict
      (fun w ↦ lowerOrdersL_mem_zeroOneSobolevSections (d + 1) w.property)
      isClosed_zeroOneSobolevSections

end TauCeti
