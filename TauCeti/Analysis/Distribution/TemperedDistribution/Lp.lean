/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Fourier.Continuous

/-!
# `Lᵖ` functions as tempered distributions

An `Lᵖ` function `u` defines the tempered distribution `φ ↦ ∫ φ • u`
(`MeasureTheory.Lp.toTemperedDistribution`). This file records facts about that embedding which
are needed to read off a pointwise representative from an identity of tempered distributions,
and a criterion for an operator into tempered distributions to take values in `Lᵖ`.

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

* A continuous linear map `T : Lᵖ → 𝓢'`, `p < ∞`, that is given on Schwartz functions by an
  operator bounded in the `Lᵖ` norm takes values in `Lᵖ`, with the same bound. Schwartz functions
  are dense in `Lᵖ`, so the bounded operator extends, and the extension agrees with `T` because
  `𝓢'` is Hausdorff. This is how `Lᵖ` bounds for Fourier multipliers and multiplication operators,
  proved on Schwartz functions, pass to all of `Lᵖ` or of a Sobolev space.

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
* `ContinuousLinearMap.exists_apply_eq_toTemperedDistribution_and_norm_le`: an operator
  `Lᵖ → 𝓢'` bounded on Schwartz functions takes values in `Lᵖ`.

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
  have hcont : Continuous (𝓕⁻ (v : E → F)) := (L1.integrable_coeFn v).continuous_fourierInv
  have hu : (u : 𝓢'(E, F)) = 𝓕⁻ (v : 𝓢'(E, F)) := by
    rw [← h]
    exact (FourierTransform.fourierInv_fourier_eq _).symm
  refine ae_eq_of_toTemperedDistribution_apply_eq u hcont.locallyIntegrable fun φ => ?_
  rw [hu, fourierInv_toTemperedDistribution_apply]

end InnerProductSpace

end MeasureTheory.Lp

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-- **Extension from Schwartz functions.** Let `T` be a continuous linear map from `Lᵖ`,
`p < ∞`, to tempered distributions, which on Schwartz functions `φ` is given by an operator
`M` on Schwartz functions with `‖M φ‖_p ≤ C ‖φ‖_p`. Then `T` takes values in `Lᵖ`: every `T f`
is the tempered distribution of some `g ∈ Lᵖ` with `‖g‖_p ≤ C ‖f‖_p`.

The function `g` is the value at `f` of the bounded extension of `φ ↦ M φ` from the dense
Schwartz functions to `Lᵖ`; it agrees with `T f` because both sides are continuous in `f` with
values in the Hausdorff space of tempered distributions. -/
theorem exists_apply_eq_toTemperedDistribution_and_norm_le {μ : Measure E}
    [μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (T : Lp F p μ →L[ℂ] 𝓢'(E, F)) (M : 𝓢(E, F) →L[ℂ] 𝓢(E, F)) {C : ℝ}
    (hT : ∀ φ : 𝓢(E, F), T (φ.toLp p μ) = ((M φ).toLp p μ : 𝓢'(E, F)))
    (hM : ∀ φ : 𝓢(E, F), ‖(M φ).toLp p μ‖ ≤ C * ‖φ.toLp p μ‖) (f : Lp F p μ) :
    ∃ g : Lp F p μ, T f = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  set e : 𝓢(E, F) →ₗ[ℂ] Lp F p μ := (SchwartzMap.toLpCLM ℂ F p μ).toLinearMap
  have he : DenseRange e := SchwartzMap.denseRange_toLpCLM (F := F) (μ := μ) hp
  set S : 𝓢(E, F) →ₗ[ℂ] Lp F p μ := e ∘ₗ M.toLinearMap
  have hSe : ∀ φ, ‖S φ‖ ≤ C * ‖e φ‖ := fun φ ↦ by
    simpa only [S, e, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      SchwartzMap.toLpCLM_apply] using hM φ
  refine ⟨S.extendOfNorm e f, ?_, LinearMap.norm_extendOfNorm_apply_le he _ hSe f⟩
  refine congrFun (he.equalizer (g := T) (h := fun f ↦ (S.extendOfNorm e f : 𝓢'(E, F)))
    T.continuous ((Lp.toTemperedDistributionCLM F μ p).continuous.comp
      (S.extendOfNorm e).continuous) (funext fun φ ↦ ?_)) f
  simp only [Function.comp_apply, LinearMap.extendOfNorm_eq he ⟨_, hSe⟩]
  simpa only [S, e, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    SchwartzMap.toLpCLM_apply] using hT φ

end ContinuousLinearMap
