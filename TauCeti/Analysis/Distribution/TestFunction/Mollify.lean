/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.Analysis.Distribution.TestFunction.Convolution
public import TauCeti.Analysis.Distribution.TestFunction.TranslateAverage.Homotopy

/-!
# Mollification of test forms on the whole space

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let
`ρ` be a smooth bump function centred at `0`, normalized to `ρ̂ = ρ.normed μ` of integral one and
supported in the closed ball of radius `r = ρ.rOut`. Mollification of test forms on `E`,

`(M ω) x = ∫ ρ̂ y ω (x + y) dμ(y) = (ρ̂ ⋆ ω) x`,

is the mean of the translates of `ω` against the probability measure `ρ.normedMeasure μ` with
density `ρ̂`, which is concentrated on `closedBall 0 r`. So it is the continuous linear map
`TestFunction.translationMeanCLM` of that measure on the LF space of test forms
(`TestFunction.mollifyCLM`). It commutes with the exterior derivative, does not increase sup norms,
and converges to the identity as the bump shrinks.

The averaged straight-line homotopy operator `TestFunction.translationHomotopyCLM` of the same
measure relates `M` to the identity, and precomposing currents with `M` mollifies currents, see
`TauCeti.Analysis.Distribution.Flat.Mollify`.

## Main declarations

* `TestFunction.mollifyCLM`: mollification of test functions on `E`, equal to the mean of
  translates `TestFunction.mollifyCLM_eq_translationMeanCLM`, with
  `TestFunction.mollifyCLM_apply_eq_integral` giving it as an average of translates and
  `TestFunction.mollifyCLM_apply` identifying it with the convolution `ρ̂ ⋆ ω`.
* `TestFunction.tsupport_mollifyCLM_subset`: the support of `M φ`.
* `TestFunction.tendsto_mollifyCLM`: `M φ → φ` as the bump shrinks.
* `TestFunction.extDerivCLM_comp_mollifyCLM`: `d ∘ M = M ∘ d`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1 (regularization by convolution).
-/

public section

noncomputable section

open Set Function MeasureTheory Metric TopologicalSpace Filter
open scoped Distributions Topology Convolution Pointwise

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))

/-- **Mollification** of test functions on `E` by the normalized bump `ρ̂ = ρ.normed μ`:
`(M φ) x = ∫ ρ̂ y φ (x + y) dμ(y)`, which is the convolution `ρ̂ ⋆ φ`, see
`TestFunction.mollifyCLM_apply`. It is the mean of the translates of `φ` against the probability
measure `ρ.normedMeasure μ`. Precomposing a current with it mollifies the current. -/
def mollifyCLM : 𝓓((⊤ : Opens E), F) →L[ℝ] 𝓓((⊤ : Opens E), F) :=
  translationMeanCLM (ρ.normedMeasure μ) (ρ.ae_mem_closedBall_normedMeasure μ) (subset_univ _)

/-- Mollification is the mean of translates against the probability measure with density `ρ̂`. -/
theorem mollifyCLM_eq_translationMeanCLM :
    (mollifyCLM μ ρ : 𝓓((⊤ : Opens E), F) →L[ℝ] _) =
      translationMeanCLM (ρ.normedMeasure μ) (ρ.ae_mem_closedBall_normedMeasure μ)
        (subset_univ _) := by
  rw [mollifyCLM]

/-- Mollification at a point, as the average of translates: `(M φ) x = ∫ ρ̂ y φ (x + y) dμ(y)`. -/
theorem mollifyCLM_apply_eq_integral (φ : 𝓓((⊤ : Opens E), F)) (x : E) :
    mollifyCLM μ ρ φ x = ∫ y, ρ.normed μ y • φ (x + y) ∂μ := by
  rw [mollifyCLM, translationMeanCLM_apply, ρ.integral_normedMeasure]

/-- Mollification is convolution with the normalized bump. -/
theorem mollifyCLM_apply (φ : 𝓓((⊤ : Opens E), F)) (x : E) :
    mollifyCLM μ ρ φ x = (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] φ) x := by
  rw [mollifyCLM_apply_eq_integral, convolution_def, ← integral_neg_eq_self]
  simp [ρ.normed_neg, sub_eq_add_neg]

/-- On the whole space, mollification agrees with `TestFunction.mollify`. -/
theorem mollifyCLM_eq_mollify (φ : 𝓓((⊤ : Opens E), F)) :
    mollifyCLM μ ρ φ = mollify φ μ ρ (subset_univ _) := by
  ext x
  rw [mollifyCLM_apply, mollify_apply]

/-- A bound `C` on the values of `φ` bounds its mollification. -/
theorem norm_mollifyCLM_apply_le (φ : 𝓓((⊤ : Opens E), F)) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C)
    (x : E) : ‖mollifyCLM μ ρ φ x‖ ≤ C := by
  rw [mollifyCLM_eq_translationMeanCLM]
  exact (norm_translationMeanCLM_apply_le φ hC x).trans_eq (by simp)

/-- Mollification enlarges supports by at most `r = ρ.rOut`. -/
theorem tsupport_mollifyCLM_subset (φ : 𝓓((⊤ : Opens E), F)) :
    tsupport (mollifyCLM μ ρ φ) ⊆ tsupport φ + closedBall (0 : E) ρ.rOut :=
  tsupport_translationMeanCLM_subset φ

/-- As the bumps shrink, the mollifications of a test function converge to it in the LF
topology. -/
theorem tendsto_mollifyCLM {ι : Type*} {l : Filter ι} [CompleteSpace F]
    {ρ : ι → ContDiffBump (0 : E)} (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0))
    (φ : 𝓓((⊤ : Opens E), F)) : Tendsto (fun i ↦ mollifyCLM μ (ρ i) φ) l (𝓝 φ) := by
  simp only [mollifyCLM_eq_mollify]
  exact tendsto_mollify φ μ hρ fun _ ↦ subset_univ _

/-- **Mollification commutes with the exterior derivative**: `d ∘ M = M ∘ d`. -/
theorem extDerivCLM_comp_mollifyCLM [CompleteSpace F] {m : ℕ} :
    (extDerivCLM ∘L mollifyCLM μ ρ : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] _) =
      mollifyCLM μ ρ ∘L extDerivCLM := by
  ext ω : 1
  exact extDerivCLM_translationMeanCLM ω

end TestFunction
