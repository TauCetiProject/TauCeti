/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Distribution.Support

/-!
# Cutoff convolution of distributions with locally integrable kernels

For a locally integrable scalar kernel `K₀ : E → ℝ` with respect to an `SFinite` left-invariant
measure `μ` and a smooth cutoff test function `χ : 𝓓(Ω, ℝ)`, the test-function operator
`TestFunction.cutoffConvolutionCLM χ hK₀ : 𝓓(Ω', ℝ) →L[ℝ] 𝓓(Ω, ℝ)` sends `φ` to
`x ↦ χ x • (K₀ ⋆ φ) x`. Its transpose `Distribution.cutoffConvolutionCLM χ hK₀` is the continuous
linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω', F)` sending a distribution `T` on `Ω` to the distribution
`φ ↦ T (χ • (K₀ ⋆ φ))` on `Ω'`. For a symmetric kernel `K₀` (such as a Newtonian potential kernel)
and a cutoff `χ` equal to `1` near the compact support of `T`, this is the distributional
convolution `K₀ ⋆ (χ T)` on `Ω'`.

## Main declarations

* `Distribution.cutoffConvolutionCLM`: the transpose of `TestFunction.cutoffConvolutionCLM` as a
  continuous linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω', F)`, with `Distribution.cutoffConvolutionCLM_apply`
  and `Distribution.coe_cutoffConvolutionCLM`.
* `Distribution.cutoffConvolutionCLM_zero`, `Distribution.cutoffConvolutionCLM_add`,
  `Distribution.cutoffConvolutionCLM_neg`, `Distribution.cutoffConvolutionCLM_sub`,
  `Distribution.cutoffConvolutionCLM_smul`: linearity in the cutoff `χ`.
* `Distribution.mapCLM_cutoffConvolutionCLM`: cutoff convolution commutes with applying a continuous
  linear map to the values of `T`.
* `Distribution.cutoffConvolutionCLM_congr`: cutoff convolution depends on `χ` only through its
  germ along `dsupport T`.

## References

* [L. Hörmander, *The Analysis of Linear Partial Differential Operators I*][hormander2003],
  §4.1–4.2 (convolution of distributions with compact support).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]
  {Ω Ω' : Opens E} {K₀ : E → ℝ} {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

/-- The transpose of `TestFunction.cutoffConvolutionCLM`: for a smooth cutoff `χ : 𝓓(Ω, ℝ)` and a
locally integrable scalar kernel `K₀`, the continuous linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω', F)`
sending a distribution `T` to `φ ↦ T (χ • (K₀ ⋆ φ))`. -/
def cutoffConvolutionCLM (χ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ) :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω', F) :=
  (TestFunction.cutoffConvolutionCLM (Ω' := Ω') χ hK₀).precompCompactConvergenceCLM F

@[simp]
theorem cutoffConvolutionCLM_apply (χ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ)
    (T : 𝓓'(Ω, F)) (φ : 𝓓(Ω', ℝ)) :
    cutoffConvolutionCLM χ hK₀ T φ = T (TestFunction.cutoffConvolutionCLM χ hK₀ φ) :=
  (rfl)

/-- As a function on test functions, `cutoffConvolutionCLM χ hK₀ T` is `T` composed with
`TestFunction.cutoffConvolutionCLM χ hK₀`. -/
theorem coe_cutoffConvolutionCLM (χ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ) (T : 𝓓'(Ω, F)) :
    ⇑(cutoffConvolutionCLM (Ω' := Ω') χ hK₀ T) = ⇑T ∘ ⇑(TestFunction.cutoffConvolutionCLM χ hK₀) :=
  (rfl)

/-- Cutoff convolution with the zero cutoff vanishes. -/
@[simp]
theorem cutoffConvolutionCLM_zero (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (0 : 𝓓(Ω, ℝ)) hK₀ = 0 := by
  ext T φ
  simp

/-- Cutoff convolution is additive in the cutoff. -/
@[simp]
theorem cutoffConvolutionCLM_add (χ₁ χ₂ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (χ₁ + χ₂) hK₀ =
      cutoffConvolutionCLM χ₁ hK₀ + cutoffConvolutionCLM χ₂ hK₀ := by
  ext T φ
  simp

/-- Cutoff convolution commutes with negation of the cutoff. -/
@[simp]
theorem cutoffConvolutionCLM_neg (χ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (-χ) hK₀ = -cutoffConvolutionCLM χ hK₀ := by
  ext T φ
  simp

/-- Cutoff convolution commutes with subtraction of cutoffs. -/
@[simp]
theorem cutoffConvolutionCLM_sub (χ₁ χ₂ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (χ₁ - χ₂) hK₀ =
      cutoffConvolutionCLM χ₁ hK₀ - cutoffConvolutionCLM χ₂ hK₀ := by
  ext T φ
  simp

/-- Cutoff convolution commutes with scalar multiplication of the cutoff. -/
@[simp]
theorem cutoffConvolutionCLM_smul (c : ℝ) (χ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (c • χ) hK₀ = c • cutoffConvolutionCLM χ hK₀ := by
  ext T φ
  simp

/-- Cutoff convolution commutes with applying a continuous linear map to the values of `T`. -/
theorem mapCLM_cutoffConvolutionCLM {F' : Type*} [AddCommGroup F'] [Module ℝ F']
    [TopologicalSpace F'] [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F']
    (A : F →L[ℝ] F') (χ : 𝓓(Ω, ℝ)) (hK₀ : LocallyIntegrable K₀ μ) (T : 𝓓'(Ω, F)) :
    mapCLM A (cutoffConvolutionCLM (Ω' := Ω') χ hK₀ T) =
      cutoffConvolutionCLM χ hK₀ (mapCLM A T) := by
  ext φ
  simp

/-- Two cutoffs that agree on a neighbourhood of `dsupport T` define the same cutoff convolution. -/
theorem cutoffConvolutionCLM_congr {χ₁ χ₂ : 𝓓(Ω, ℝ)}
    (hK₀ : LocallyIntegrable K₀ μ) {T : 𝓓'(Ω, F)}
    (hχ : (χ₁ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ₂) :
    cutoffConvolutionCLM (Ω' := Ω') χ₁ hK₀ T = cutoffConvolutionCLM χ₂ hK₀ T := by
  ext φ
  simp only [cutoffConvolutionCLM_apply]
  refine Distribution.map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ] with x hx
  simp [hx]

end Distribution
