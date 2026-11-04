/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `Lᵖ` functions as tempered distributions

An `Lᵖ` function `u` defines the tempered distribution `φ ↦ ∫ φ • u`
(`MeasureTheory.Lp.toTemperedDistribution`). This file records facts about that embedding which
are needed to read off a pointwise representative from an identity of tempered distributions.

* An `Lᵖ` function is determined almost everywhere by its pairings with Schwartz functions,
  even when it is compared with a locally integrable function that need not lie in the same
  `Lᵖ` space. Mathlib's `MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot` is the case of
  two functions in one `Lᵖ` space.
* The distributional inverse Fourier transform of an `L¹` function `v` is the bounded continuous
  function `𝓕⁻ v`, given by the absolutely convergent Fourier integral. This is the
  multiplication formula `∫ (𝓕⁻ φ) • v = ∫ φ • 𝓕⁻ v` of
  `VectorFourier.integral_bilin_fourierIntegral_eq_flip`, read through the definition
  `𝓕⁻ T (φ) = T (𝓕⁻ φ)` of the Fourier transform on `𝓢'`.

Together they turn the statement "the Fourier transform of `u ∈ Lᵖ` is an `L¹` function `v`" into
the continuous representative `𝓕⁻ v` of `u` (`MeasureTheory.Lp.ae_eq_fourierInv_of_fourier_eq`);
this is how the Sobolev embedding `H^s(ℝⁿ) ⊆ C₀(ℝⁿ)`, `s > n / 2`, is derived from
`TemperedDistribution.MemSobolev.fourier_memL1`. Multiplying the tempered distribution of an `Lᵖ`
function by a function of temperate growth multiplies the function pointwise
(`MeasureTheory.Lp.smulLeftCLM_toTemperedDistribution_apply`).

## Main declarations

* `MeasureTheory.Lp.ae_eq_of_toTemperedDistribution_apply_eq`: an `Lᵖ` function whose pairings
  with Schwartz functions agree with those of a locally integrable `g` is almost everywhere
  equal to `g`.
* `MeasureTheory.Lp.fourierInv_toTemperedDistribution_apply`: the inverse Fourier transform of
  the tempered distribution of an `L¹` function `v` pairs with `φ` as `∫ φ • 𝓕⁻ v`.
* `MeasureTheory.Lp.ae_eq_fourierInv_of_fourier_eq`: an `Lᵖ` function whose Fourier transform is
  an `L¹` function `v` agrees almost everywhere with `𝓕⁻ v`.
* `MeasureTheory.Lp.smulLeftCLM_toTemperedDistribution_apply`: the product of the tempered
  distribution of an `Lᵖ` function `u` with a function `g` of temperate growth pairs with `φ` as
  `∫ φ • (g • u)`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., §2.3 (functions as tempered distributions
  and the Fourier transform on `𝓢'`).
-/

public section

noncomputable section

namespace MeasureTheory.Lp

open SchwartzMap
open scoped ContDiff FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section NormedSpace

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An `Lᵖ` function is almost everywhere equal to any locally integrable function with the same
pairings against Schwartz functions. The two functions need not lie in the same `Lᵖ` space. -/
theorem ae_eq_of_toTemperedDistribution_apply_eq {μ : Measure E} [μ.HasTemperateGrowth]
    [IsLocallyFiniteMeasure μ] {p : ENNReal} [hp : Fact (1 ≤ p)] (u : Lp F p μ) {g : E → F}
    (hg : LocallyIntegrable g μ)
    (h : ∀ φ : 𝓢(E, ℂ), (u : 𝓢'(E, F)) φ = ∫ x, φ x • g x ∂μ) :
    u =ᵐ[μ] g := by
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp u).locallyIntegrable hp.out) hg
    fun ψ hψ hψc => ?_
  -- A smooth compactly supported real function is a complex Schwartz function.
  have hψ₁ : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hψc.comp_left rfl
  have hψ₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have := h (hψ₁.toSchwartzMap hψ₂)
  simpa [Lp.toTemperedDistribution_apply] using this

omit [FiniteDimensional ℝ E] in
/-- Multiplying the tempered distribution of an `Lᵖ` function `u` by a function `g` of temperate
growth gives the distribution `φ ↦ ∫ φ • (g • u)`. -/
theorem smulLeftCLM_toTemperedDistribution_apply {μ : Measure E} [μ.HasTemperateGrowth]
    {p : ENNReal} [Fact (1 ≤ p)] {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : Lp F p μ)
    (φ : 𝓢(E, ℂ)) :
    TemperedDistribution.smulLeftCLM F g (u : 𝓢'(E, F)) φ = ∫ x, φ x • g x • u x ∂μ := by
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, mul_comm (g _), mul_smul]

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The inverse Fourier transform of an `L¹` function as a tempered distribution.** For
`v ∈ L¹`, the distributional inverse Fourier transform of `v` is the function `𝓕⁻ v` given by the
absolutely convergent Fourier integral: it pairs with a Schwartz function `φ` as `∫ φ • 𝓕⁻ v`. -/
theorem fourierInv_toTemperedDistribution_apply (v : Lp F 1 (volume : Measure E))
    (φ : 𝓢(E, ℂ)) :
    𝓕⁻ (v : 𝓢'(E, F)) φ = ∫ x, φ x • 𝓕⁻ (v : E → F) x := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.fourierInv_coe]
  -- On functions, `𝓕⁻` is defined (`Real.instFourierTransformInv`) as the Fourier integral for
  -- the pairing `-⟪·, ·⟫`, which is its own flip, so this is the multiplication formula for that
  -- pairing.
  have hflip : (-innerₗ E).flip = -innerₗ E :=
    LinearMap.ext₂ fun x y => by simp [real_inner_comm]
  have hL : Continuous fun p : E × E => (-innerₗ E) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar hL
    (φ.integrable (μ := volume)) (L1.integrable_coeFn v)
  rw [hflip] at h
  exact h

/-- **The representative of an `Lᵖ` function with integrable Fourier transform.** If the
distributional Fourier transform of `u ∈ Lᵖ` is an `L¹` function `v`, then `u` agrees almost
everywhere with the continuous function `𝓕⁻ v`. -/
theorem ae_eq_fourierInv_of_fourier_eq {p : ENNReal} [Fact (1 ≤ p)]
    {u : Lp F p (volume : Measure E)} {v : Lp F 1 (volume : Measure E)}
    (h : 𝓕 (u : 𝓢'(E, F)) = v) :
    u =ᵐ[volume] 𝓕⁻ (v : E → F) := by
  have hcont : Continuous (𝓕⁻ (v : E → F)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by simpa only [innerₗ_apply_apply] using continuous_inner)
      (L1.integrable_coeFn v).comp_neg
  have hu : (u : 𝓢'(E, F)) = 𝓕⁻ (v : 𝓢'(E, F)) := by
    rw [← h]
    exact (FourierTransform.fourierInv_fourier_eq _).symm
  refine ae_eq_of_toTemperedDistribution_apply_eq u hcont.locallyIntegrable fun φ => ?_
  rw [hu, fourierInv_toTemperedDistribution_apply]

end InnerProductSpace

end MeasureTheory.Lp
