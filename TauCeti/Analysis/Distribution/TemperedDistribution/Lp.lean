/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

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
* The distributional Fourier transform and inverse Fourier transform of an integrable function
  `v` are the bounded continuous functions `𝓕 v` and `𝓕⁻ v`, given by the absolutely convergent
  Fourier integrals. This is the multiplication formula `∫ (𝓕⁻ φ) • v = ∫ φ • 𝓕⁻ v`, and its
  analogue for `𝓕`, of `VectorFourier.integral_bilin_fourierIntegral_eq_flip`, read through the
  definition `𝓕⁻ T (φ) = T (𝓕⁻ φ)` of the inverse Fourier transform on `𝓢'`.

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
* A Fourier multiplier whose symbol `σ` is a Schwartz function maps every `Lᵖ`, `1 ≤ p ≤ ∞`,
  into itself with norm at most `‖𝓕⁻ σ‖₁`. On Schwartz functions it is convolution with `𝓕⁻ σ`,
  which Young's inequality bounds, and the extension above covers `p < ∞`. Schwartz functions are
  not dense in `L^∞`; there the multiplier of `f` is identified directly with the convolution
  `𝓕⁻ σ ⋆ f` by pairing with Schwartz functions and Fubini's theorem.

## Main declarations

* `MeasureTheory.Lp.ae_eq_of_toTemperedDistribution_apply_eq`: an `Lᵖ` function whose pairings
  with Schwartz functions agree with those of a locally integrable `g` is almost everywhere
  equal to `g`.
* `MeasureTheory.Lp.toTemperedDistribution_compLp_apply`: applying a continuous linear map to the
  values of an `Lᵖ` function applies it to its tempered distribution.
* `SchwartzMap.toTemperedDistributionCLM_postcompCLM_apply`: the same for the values of a
  Schwartz function.
* `MeasureTheory.Lp.fourier_toTemperedDistribution_apply`: the Fourier transform of the tempered
  distribution of an `Lᵖ` function `v` with an integrable representative `f` pairs with `φ` as
  `∫ φ • 𝓕 f`.
* `MeasureTheory.Lp.fourierInv_toTemperedDistribution_apply`: the inverse Fourier transform of
  the tempered distribution of an `L¹` function `v` pairs with `φ` as `∫ φ • 𝓕⁻ v`.
* `MeasureTheory.Lp.ae_eq_fourierInv_of_fourier_eq`: an `Lᵖ` function whose Fourier transform is
  an `L¹` function `v` agrees almost everywhere with `𝓕⁻ v`.
* `MeasureTheory.Lp.smulLeftCLM_toTemperedDistribution_apply`: the product of the tempered
  distribution of an `Lᵖ` function `u` with a function `g` of temperate growth pairs with `φ` as
  `∫ φ • (g • u)`.
* `ContinuousLinearMap.exists_apply_eq_toTemperedDistribution_and_norm_le`: an operator
  `Lᵖ → 𝓢'` bounded on Schwartz functions takes values in `Lᵖ`.
* `TemperedDistribution.fourierMultiplierCLM_toTemperedDistribution_apply_eq_integral_convolution`:
  on `L^∞`, the multiplier with a Schwartz symbol `σ` is convolution with `𝓕⁻ σ`.
* `TemperedDistribution.exists_fourierMultiplierCLM_eq_and_norm_le`: the multiplier with a
  Schwartz symbol `σ` maps `f ∈ Lᵖ` to some `g ∈ Lᵖ` with `‖g‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., §2.3 (functions as tempered distributions
  and the Fourier transform on `𝓢'`).
-/

public section

noncomputable section

/-- A measure of temperate growth is finite on compact sets: `(1 + ‖x‖) ^ (-n)` is integrable and
bounded below by a positive constant on any bounded set. -/
theorem MeasureTheory.Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (μ : Measure E)
    [h : μ.HasTemperateGrowth] : IsFiniteMeasureOnCompacts μ := by
  obtain ⟨n, hn⟩ := h.exists_integrable
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  have hε : 0 < (1 + max R 0) ^ (-(n : ℝ)) := by positivity
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hn.measure_norm_ge_lt_top hε)
  have hx' : ‖x‖ ≤ max R 0 := by simpa using (hR hx).trans (le_max_left R 0)
  rw [Set.mem_ofPred_eq, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)

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
    {p : ENNReal} [hp : Fact (1 ≤ p)] (u : Lp F p μ) {g : E → F}
    (hg : LocallyIntegrable g μ)
    (h : ∀ φ : 𝓢(E, ℂ), (u : 𝓢'(E, F)) φ = ∫ x, φ x • g x ∂μ) :
    u =ᵐ[μ] g := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
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

omit [FiniteDimensional ℝ E] in
/-- Applying a continuous linear map `L` to the values of an `Lᵖ` function `u` applies `L` to the
pairings of its tempered distribution. -/
theorem toTemperedDistribution_compLp_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] {μ : Measure E} [μ.HasTemperateGrowth] {p : ENNReal} [hp : Fact (1 ≤ p)]
    (L : F →L[ℂ] G) (u : Lp F p μ) (φ : 𝓢(E, ℂ)) :
    ((L.compLp u : Lp G p μ) : 𝓢'(E, G)) φ = L ((u : 𝓢'(E, F)) φ) := by
  have : (1 - p⁻¹)⁻¹.HolderConjugate p :=
    (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  have hφu : Integrable (fun x ↦ φ x • u x) μ :=
    memLp_one_iff_integrable.1 ((φ.memLp (1 - p⁻¹)⁻¹ (μ := μ)).smul (Lp.memLp u))
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply, ← L.integral_comp_comm hφu]
  refine integral_congr_ae ((L.coeFn_compLp u).mono fun x hx ↦ ?_)
  simp only [hx, map_smul]

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Fourier transform of an integrable function as a tempered distribution.** If the
`Lᵖ` function `v` agrees almost everywhere with an integrable function `f`, the distributional
Fourier transform of `v` is the function `𝓕 f` given by the absolutely convergent Fourier
integral: it pairs with a Schwartz function `φ` as `∫ φ • 𝓕 f`. -/
theorem fourier_toTemperedDistribution_apply {p : ENNReal} [Fact (1 ≤ p)]
    (v : Lp F p (volume : Measure E)) {f : E → F} (hf : Integrable f) (hvf : v =ᵐ[volume] f)
    (φ : 𝓢(E, ℂ)) :
    𝓕 (v : 𝓢'(E, F)) φ = ∫ x, φ x • 𝓕 f x := by
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    integral_congr_ae (hvf.mono fun x hx => by rw [hx]), SchwartzMap.fourier_coe]
  -- On functions, `𝓕` is the Fourier integral for the pairing `⟪·, ·⟫`, which is its own flip,
  -- so this is the multiplication formula for that pairing.
  have hL : Continuous fun p : E × E => (innerₗ E) p.1 p.2 := by
    simp only [innerₗ_apply_apply]
    fun_prop
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar hL
    (φ.integrable (μ := volume)) hf
  rwa [flip_innerₗ] at h

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

namespace SchwartzMap

open MeasureTheory

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Applying a continuous linear map `L` to the values of a Schwartz function `u` applies `L` to
the pairings of its tempered distribution. -/
theorem toTemperedDistributionCLM_postcompCLM_apply (L : F →L[ℂ] G) (u : 𝓢(E, F))
    (φ : 𝓢(E, ℂ)) :
    ((u.postcompCLM L : 𝓢(E, G)) : 𝓢'(E, G)) φ = L ((u : 𝓢'(E, F)) φ) := by
  have hφu : Integrable (fun x ↦ φ x • u x) := φ.integrable.smul_of_top_left u.memLp_top
  rw [SchwartzMap.coe_apply, SchwartzMap.coe_apply, ← L.integral_comp_comm hφu]
  simp only [postcompCLM_apply, map_smul]

end SchwartzMap

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
    [μ.HasTemperateGrowth] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (T : Lp F p μ →L[ℂ] 𝓢'(E, F)) (M : 𝓢(E, F) →L[ℂ] 𝓢(E, F)) {C : ℝ}
    (hT : ∀ φ : 𝓢(E, F), T (φ.toLp p μ) = ((M φ).toLp p μ : 𝓢'(E, F)))
    (hM : ∀ φ : 𝓢(E, F), ‖(M φ).toLp p μ‖ ≤ C * ‖φ.toLp p μ‖) (f : Lp F p μ) :
    ∃ g : Lp F p μ, T f = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
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

namespace TemperedDistribution

open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The kernel `𝓕⁻ σ` of the multiplier with a Schwartz symbol `σ` is integrable. -/
private theorem integrable_fourierInv_coe (σ : 𝓢(E, ℂ)) : Integrable (𝓕⁻ (σ : E → ℂ)) := by
  simpa [SchwartzMap.fourierInv_coe] using (𝓕⁻ σ : 𝓢(E, ℂ)).integrable (μ := volume)

/-- An `eLpNorm` bound by `‖𝓕⁻ σ‖₁` in `ℝ≥0∞` gives the real bound by `∫ ‖𝓕⁻ σ‖`, as long as the
other factor is finite. -/
private theorem toReal_le_integral_norm_fourierInv_mul (σ : 𝓢(E, ℂ)) {a b : ℝ≥0∞} (hb : b ≠ ∞)
    (h : a ≤ eLpNorm (𝓕⁻ (σ : E → ℂ)) 1 volume * b) :
    a.toReal ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * b.toReal := by
  have hK := integrable_fourierInv_coe σ
  rw [integral_norm_eq_lintegral_enorm hK.1, ← eLpNorm_one_eq_lintegral_enorm hK.1,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top hb) h

/-- The case `p < ∞` of `TemperedDistribution.exists_fourierMultiplierCLM_eq_and_norm_le`: the
bound holds on the dense Schwartz functions, and extends. -/
private theorem exists_fourierMultiplierCLM_eq_and_norm_le_of_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (σ : 𝓢(E, ℂ)) (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E), fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g ∧
      ‖g‖ ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * ‖f‖ := by
  set M : 𝓢(E, F) →L[ℂ] 𝓢(E, F) := SchwartzMap.fourierMultiplierCLM F σ
  have hM : ∀ φ : 𝓢(E, F), ‖(M φ).toLp p‖ ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * ‖φ.toLp p‖ := by
    intro φ
    have h := SchwartzMap.eLpNorm_fourierMultiplierCLM_le σ φ (Fact.out : 1 ≤ p)
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ p _),
      eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ p _)]
    exact toReal_le_integral_norm_fourierInv_mul σ (φ.memLp p volume).eLpNorm_ne_top h
  refine (fourierMultiplierCLM F σ ∘L
    Lp.toTemperedDistributionCLM F volume p).exists_apply_eq_toTemperedDistribution_and_norm_le
      hp M (fun φ ↦ ?_) hM f
  simp only [M, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply,
    Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq σ.hasTemperateGrowth]

/-- **A multiplier with Schwartz symbol is convolution with its kernel on `L^∞`.** For
`f ∈ L^∞` and `K = 𝓕⁻ σ`, the tempered distribution `T_σ f` pairs with a Schwartz function `u` as
the function `K ⋆ f`. -/
theorem fourierMultiplierCLM_toTemperedDistribution_apply_eq_integral_convolution (σ : 𝓢(E, ℂ))
    (f : Lp F ∞ (volume : Measure E)) (u : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F σ (f : 𝓢'(E, F)) u =
      ∫ y, u y • (𝓕⁻ (σ : E → ℂ) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (f : E → F)) y := by
  set K : E → ℂ := 𝓕⁻ (σ : E → ℂ)
  have hKi : Integrable K := integrable_fourierInv_coe σ
  -- The integrand `(x, y) ↦ (K (y - x) * u y) • f x` is integrable on the product: it is an
  -- integrable function of `(x, y)` times the bounded function `f x`.
  have hint : Integrable (Function.uncurry fun x y ↦ (K (y - x) * u y) • (f : E → F) x)
      (volume.prod volume) := by
    have h1 := (u.integrable (μ := volume)).convolution_integrand
      (ContinuousLinearMap.mul ℂ ℂ) hKi.comp_neg
    have h2 : MemLp (fun q : E × E ↦ (f : E → F) q.1) ∞ (volume.prod volume) :=
      (Lp.memLp f).comp_quasiMeasurePreserving_top Measure.quasiMeasurePreserving_fst
    refine (h1.smul_of_top_left h2).congr (Filter.Eventually.of_forall fun ⟨x, y⟩ ↦ ?_)
    simp [neg_sub, mul_comm]
  -- `𝓕 (σ • 𝓕⁻ u) x = ∫ 𝓕 σ (x - y) * u y` and `𝓕 σ (x - y) = K (y - x)`.
  have hL : ∀ x, 𝓕 (SchwartzMap.smulLeftCLM ℂ (σ : E → ℂ) (𝓕⁻ u)) x =
      ∫ y, K (y - x) * u y := by
    intro x
    rw [SchwartzMap.fourier_smulLeftCLM_apply, ← integral_sub_left_eq_self _ volume x]
    simp [K, Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]
  simp only [fourierMultiplierCLM_apply_apply, Lp.toTemperedDistribution_apply, hL]
  calc ∫ x, (∫ y, K (y - x) * u y) • (f : E → F) x
      = ∫ x, ∫ y, (K (y - x) * u y) • (f : E → F) x := by
        simp_rw [integral_smul_const]
    _ = ∫ y, ∫ x, (K (y - x) * u y) • (f : E → F) x := integral_integral_swap hint
    _ = ∫ y, u y • (K ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (f : E → F)) y := by
        simp_rw [MeasureTheory.convolution_eq_swap, ContinuousLinearMap.lsmul_apply,
          ← integral_smul, smul_smul, mul_comm (u _)]

/-- The case `p = ∞` of `TemperedDistribution.exists_fourierMultiplierCLM_eq_and_norm_le`.
Schwartz functions are not dense in `L^∞`, so the multiplier is identified directly with the
convolution `𝓕⁻ σ ⋆ f`, which Young's inequality bounds. -/
private theorem exists_fourierMultiplierCLM_eq_and_norm_le_top (σ : 𝓢(E, ℂ))
    (f : Lp F ∞ (volume : Measure E)) :
    ∃ g : Lp F ∞ (volume : Measure E), fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g ∧
      ‖g‖ ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * ‖f‖ := by
  set K : E → ℂ := 𝓕⁻ (σ : E → ℂ)
  have hKi : Integrable K := integrable_fourierInv_coe σ
  have hf : AEStronglyMeasurable (f : E → F) volume := Lp.aestronglyMeasurable f
  set h : E → F := K ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (f : E → F)
  have hh_le : eLpNorm h ∞ volume ≤ eLpNorm K 1 volume * eLpNorm f ∞ volume := by
    refine (eLpNorm_convolution_le _ hKi.aestronglyMeasurable hf le_top).trans ?_
    grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul]
  have hK1 : eLpNorm K 1 volume ≠ ∞ := (memLp_one_iff_integrable.2 hKi).eLpNorm_ne_top
  have hh : MemLp h ∞ volume :=
    hh_le.trans_lt (ENNReal.mul_lt_top hK1.lt_top (Lp.eLpNorm_lt_top f))
  refine ⟨hh.toLp h, ?_, ?_⟩
  · ext u
    rw [fourierMultiplierCLM_toTemperedDistribution_apply_eq_integral_convolution,
      Lp.toTemperedDistribution_apply]
    exact integral_congr_ae ((MemLp.coeFn_toLp hh).mono fun y hy ↦ congrArg (u y • ·) hy.symm)
  · rw [Lp.norm_toLp, Lp.norm_def]
    exact toReal_le_integral_norm_fourierInv_mul σ (Lp.eLpNorm_ne_top f) hh_le

/-- **`Lᵖ` bound for a multiplier with Schwartz symbol.** For `1 ≤ p ≤ ∞`, the Fourier multiplier
with a Schwartz symbol `σ` maps every `f ∈ Lᵖ` to a function `g ∈ Lᵖ` with
`‖g‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p`. -/
theorem exists_fourierMultiplierCLM_eq_and_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (σ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E), fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g ∧
      ‖g‖ ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact exists_fourierMultiplierCLM_eq_and_norm_le_top σ f
  · exact exists_fourierMultiplierCLM_eq_and_norm_le_of_ne_top hp σ f

end TemperedDistribution
