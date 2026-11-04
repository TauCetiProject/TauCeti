/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Multiplication by Schwartz functions on the Bessel-potential spaces `H^s(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. For a
scalar Schwartz function `φ` and every real `s`, multiplication by `φ` is a bounded operator on
Mathlib's Bessel-potential space `H^s(E, F) = H^{s,2}(E, F)`, with

`‖φ u‖_{H^s} ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖u‖_{H^s}`,

where `⟨ζ⟩ = (1 + ‖ζ‖ ^ 2) ^ (1 / 2)` is the Japanese bracket and `𝓕` is Mathlib's Fourier
transform. This includes the negative orders, where `u` is a genuine tempered distribution and
`φ u` is Mathlib's `TemperedDistribution.smulLeftCLM`.

## The Fourier argument

The `H^s` norm of `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`. For a Schwartz function `u`, the Fourier
transform of `φ u` is the convolution `∫ 𝓕 φ ζ • 𝓕 u (ξ - ζ) dζ`
(`SchwartzMap.fourier_smulLeftCLM_apply`), and **Peetre's inequality**
`⟨ξ⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨ξ - ζ⟩ ^ s ⟨ζ⟩ ^ |s|` (`TauCeti.one_add_norm_add_sq_rpow_le_mul`) gives

`⟨ξ⟩ ^ s ‖𝓕 (φ u) ξ‖ ≤ ∫ k(ζ) g(ξ - ζ) dζ`, with `k = 2 ^ (|s| / 2) ⟨·⟩ ^ |s| ‖𝓕 φ‖ ∈ L¹` and
`g = ⟨·⟩ ^ s ‖𝓕 u‖ ∈ L²`.

Young's inequality `‖k ⋆ g‖₂ ≤ ‖k‖₁ ‖g‖₂`, here Schur's test
`TauCeti.lintegral_rpow_lintegral_mul_le` for the kernel `k (ξ - η)` whose row and column
integrals are both `‖k‖₁`, bounds the `H^s` norm of `φ u`
(`SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le`).

To pass to all of `H^s`, conjugate by the Bessel potentials `J^s` (Mathlib's
`TemperedDistribution.besselPotential`, the Fourier multiplier with symbol `⟨ξ⟩ ^ s`): on `L²` the
operator `w ↦ J^s (φ J^{-s} w)`, with values in tempered distributions, is continuous, and on
Schwartz functions it takes values in `L²` with the bound above. Since Schwartz functions are
dense in `L²`, it takes values in `L²` everywhere, with the same bound
(`ContinuousLinearMap.exists_apply_eq_toTemperedDistribution_and_norm_le`).

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg`: the Bessel
  multipliers of orders `s` and `-s` are inverse on Schwartz functions.
* `TemperedDistribution.besselPotential_toTemperedDistributionCLM_eq`: the Bessel potential of a
  Schwartz function is its Schwartz-space Fourier multiplier.
* `SchwartzMap.eLpNorm_rpow_smul_fourier_smulLeftCLM_le`,
  `SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le`: the `H^s` estimate for Schwartz
  functions.
* `TemperedDistribution.exists_besselPotential_smulLeftCLM_eq_and_norm_le`: the estimate on
  tempered distributions in `H^s`.
* `TemperedDistribution.MemSobolev.smulLeftCLM`: `φ u ∈ H^s` for `u ∈ H^s` and every real `s`.
* `BesselPotentialSpace.smulLeftCLM`: multiplication by `φ` as a bounded operator on `H^s`, with
  `BesselPotentialSpace.norm_smulLeftCLM_le`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (Sobolev spaces on `ℝⁿ`: Peetre's inequality and multiplication by Schwartz functions).
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

section NormedSpace

variable [NormedSpace ℂ F] [CompleteSpace F]

namespace SchwartzMap

/-- Composing the Fourier multipliers with symbols `⟨ξ⟩ ^ s` and `⟨ξ⟩ ^ (-s)` on Schwartz
functions gives the identity. This is the Schwartz-space form of Mathlib's
`TemperedDistribution.besselPotential_besselPotential_apply` at orders `-s` and `s`. -/
theorem fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg (s : ℝ)
    (ψ : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
        (fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) ψ) = ψ := by
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  have : ((fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) *
      fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) = fun _ ↦ 1 := by
    ext x
    rw [Pi.mul_apply, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
    simp [neg_div]
  rw [this, fourierMultiplierCLM_const]
  simp

omit [CompleteSpace F] in
/-- The `L²` norm of `⟨ξ⟩ ^ s 𝓕 f`, written as a lower Lebesgue integral of the real-valued
function `⟨ξ⟩ ^ s ‖𝓕 f ξ‖`. -/
private theorem eLpNorm_rpow_smul_fourier_eq (s : ℝ) (f : E → F) (hf : Continuous f) :
    eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • f ξ) 2 volume =
      (∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖f ξ‖) ^ 2) ^ (1 / 2 : ℝ) := by
  have hw : Continuous fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun x ↦ Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg ‖x‖)).ne')
  have hm : AEStronglyMeasurable (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • f ξ) volume :=
    (hw.smul hf).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, ← ofReal_norm, norm_smul, Complex.norm_real]
  refine congrArg (· ^ (1 / 2 : ℝ)) (lintegral_congr fun ξ ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]

/-- The pointwise Peetre bound behind the `H^s` estimate: for Schwartz functions `φ` and `f`,
`⟨ξ⟩ ^ s ‖𝓕 (φ f) ξ‖` is bounded by the convolution of `2 ^ (|s| / 2) ⟨·⟩ ^ |s| ‖𝓕 φ‖` with
`⟨·⟩ ^ s ‖𝓕 f‖`. -/
private theorem ofReal_rpow_mul_norm_fourier_smulLeftCLM_le (s : ℝ) (φ : 𝓢(E, ℂ))
    (f : 𝓢(E, F)) (ξ : E) :
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ‖) ≤
      ∫⁻ y, ENNReal.ofReal
          (2 ^ (|s| / 2) * ((1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ (ξ - y)‖)) *
        ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ (s / 2) * ‖𝓕 f y‖) := by
  have hconv : 𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ = ∫ y, 𝓕 φ (ξ - y) • 𝓕 f y := by
    rw [fourier_smulLeftCLM_apply,
      ← integral_sub_left_eq_self (fun y ↦ 𝓕 φ (ξ - y) • 𝓕 f y) volume ξ]
    simp only [sub_sub_cancel]
  rw [hconv, ENNReal.ofReal_mul (by positivity), ofReal_norm]
  calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2)) * ‖∫ y, 𝓕 φ (ξ - y) • 𝓕 f y‖ₑ
      ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2)) * ∫⁻ y, ‖𝓕 φ (ξ - y) • 𝓕 f y‖ₑ := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * (‖𝓕 φ (ξ - y)‖ * ‖𝓕 f y‖)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y ↦ ?_
        rw [← ofReal_norm, norm_smul, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
      refine lintegral_mono fun y ↦ ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hP := TauCeti.one_add_norm_add_sq_rpow_le_mul s y (ξ - y)
      rw [add_sub_cancel] at hP
      calc (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (‖𝓕 φ (ξ - y)‖ * ‖𝓕 f y‖)
          ≤ 2 ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) *
              (‖𝓕 φ (ξ - y)‖ * ‖𝓕 f y‖) := by gcongr
        _ = _ := by ring

/-- The `H^s` estimate for multiplication by a Schwartz function, on the Fourier side:
`‖⟨ξ⟩ ^ s 𝓕 (φ f)‖_{L²} ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖⟨ξ⟩ ^ s 𝓕 f‖_{L²}`. It is
the pointwise Peetre bound followed by Schur's test for the convolution kernel. -/
theorem eLpNorm_rpow_smul_fourier_smulLeftCLM_le (s : ℝ) (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) :
    eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ)
        2 volume ≤
      ENNReal.ofReal (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) *
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) 2 volume := by
  set k : E → ℝ≥0∞ :=
    fun ζ ↦ ENNReal.ofReal (2 ^ (|s| / 2) * ((1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖))
  set g : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ (s / 2) * ‖𝓕 f y‖)
  have hk : Measurable k := by fun_prop
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((((measurable_const.add (measurable_norm.pow_const 2)).pow_const (s / 2))).mul
      (𝓕 f).continuous.norm.measurable)
  have hint := ((𝓕 φ).integrable_one_add_norm_sq_rpow_mul_norm (ν := volume) (|s| / 2)).const_mul
    (2 ^ (|s| / 2))
  have hk_int : ∫⁻ ζ, k ζ = ENNReal.ofReal
      (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun ζ ↦ by positivity)]
  -- Schur's test for the kernel `k (x - y)`, whose row and column integrals are `∫⁻ k`.
  have hschur := TauCeti.lintegral_rpow_lintegral_mul_le (μ := volume) (ν := volume)
    (k := fun x y ↦ k (x - y)) (hk.comp (measurable_fst.sub measurable_snd))
    (g := g) hg.aemeasurable (p := 2) one_le_two
    (A := ∫⁻ ζ, k ζ) (B := ∫⁻ ζ, k ζ)
    (.of_forall fun x ↦ (lintegral_sub_left_eq_self k x).le)
    (.of_forall fun y ↦ (lintegral_sub_right_eq_self k y).le)
  simp only [ENNReal.rpow_two] at hschur
  norm_num at hschur
  rw [eLpNorm_rpow_smul_fourier_eq _ _ (𝓕 (smulLeftCLM F (φ : E → ℂ) f)).continuous,
    eLpNorm_rpow_smul_fourier_eq _ _ (𝓕 f).continuous, ← hk_int]
  calc (∫⁻ ξ, ENNReal.ofReal
          ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ‖) ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, (∫⁻ y, k (ξ - y) * g y) ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr with ξ
        exact ofReal_rpow_mul_norm_fourier_smulLeftCLM_le s φ f ξ
    _ ≤ ((∫⁻ ζ, k ζ) ^ 2 * ∫⁻ y, g y ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr
        simpa only [sq, mul_assoc] using hschur
    _ = (∫⁻ ζ, k ζ) * (∫⁻ y, g y ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

end SchwartzMap

namespace TemperedDistribution

/-- The Bessel potential of a Schwartz function is the Schwartz function given by the Fourier
multiplier with the same symbol `⟨ξ⟩ ^ s`. -/
theorem besselPotential_toTemperedDistributionCLM_eq (s : ℝ) (f : 𝓢(E, F)) :
    besselPotential E F s (f : 𝓢'(E, F)) =
      (SchwartzMap.fourierMultiplierCLM F
        (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f : 𝓢'(E, F)) :=
  fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) f

end TemperedDistribution

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℂ F] [CompleteSpace F]

namespace SchwartzMap

/-- **Multiplication by a Schwartz function is bounded on `H^s`**, on Schwartz functions. With
the Bessel-potential weight `⟨ξ⟩ ^ s` of order `s ∈ ℝ`, Mathlib's convention for `H^s`,

`‖J^s (φ f)‖_{L²} ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖J^s f‖_{L²}`,

where `J^s` is the Fourier multiplier with symbol `⟨ξ⟩ ^ s`. -/
theorem norm_toLp_fourierMultiplierCLM_smulLeftCLM_le (s : ℝ) (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) :
    ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
        (smulLeftCLM F (φ : E → ℂ) f)).toLp 2‖ ≤
      (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) *
        ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f).toLp 2‖ := by
  have hw : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hwf : (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) =
      smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 f) := by
    ext ξ
    rw [smulLeftCLM_apply_apply hw]
  rw [norm_toLp_fourierMultiplierCLM_eq hw, norm_toLp_fourierMultiplierCLM_eq hw,
    ← ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 ^ (|s| / 2) *
      ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
    (eLpNorm_rpow_smul_fourier_smulLeftCLM_le s φ f)
  -- The remaining side goal is finiteness of the `L²` norm of a Schwartz function.
  rw [hwf]
  exact ((smulLeftCLM F _ (𝓕 f)).memLp 2 volume).eLpNorm_ne_top

end SchwartzMap

namespace TemperedDistribution

/-- **Multiplication by a Schwartz function is bounded on `H^s`**, for every real `s`. If the
tempered distribution `u` lies in `H^s`, with `J^s u = v ∈ L²`, then `J^s (φ u) = v'` for some
`v' ∈ L²` with `‖v'‖ ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖v‖`. -/
theorem exists_besselPotential_smulLeftCLM_eq_and_norm_le (s : ℝ) (φ : 𝓢(E, ℂ)) {u : 𝓢'(E, F)}
    {v : Lp F 2 (volume : Measure E)} (hv : besselPotential E F s u = v) :
    ∃ v' : Lp F 2 (volume : Measure E),
      besselPotential E F s (smulLeftCLM F (φ : E → ℂ) u) = v' ∧
        ‖v'‖ ≤ (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) * ‖v‖ := by
  set C := 2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖
  set Λ : ℝ → 𝓢(E, F) →L[ℂ] 𝓢(E, F) := fun t ↦
    SchwartzMap.fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ))
  -- The operator `w ↦ J^s (φ J^{-s} w)` on `L²`, with values in tempered distributions, is
  -- given on Schwartz functions by `M`, which is bounded in `L²`.
  set M : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
    Λ s ∘L SchwartzMap.smulLeftCLM F (φ : E → ℂ) ∘L Λ (-s)
  set T : Lp F 2 (volume : Measure E) →L[ℂ] 𝓢'(E, F) :=
    besselPotential E F s ∘L smulLeftCLM F (φ : E → ℂ) ∘L besselPotential E F (-s) ∘L
      Lp.toTemperedDistributionCLM F volume 2
  have hM (ψ : 𝓢(E, F)) : ‖(M ψ).toLp 2 volume‖ ≤ C * ‖ψ.toLp 2 volume‖ := by
    have h := SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le s φ (Λ (-s) ψ)
    simp only [Λ, SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg]
      at h
    simpa only [M, Λ, ContinuousLinearMap.comp_apply] using h
  have hT (ψ : 𝓢(E, F)) : T (ψ.toLp 2 volume) = ((M ψ).toLp 2 volume : 𝓢'(E, F)) := by
    simp only [T, M, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_toLp_eq, besselPotential_toTemperedDistributionCLM_eq,
      smulLeftCLM_toTemperedDistributionCLM_eq φ.hasTemperateGrowth, Λ]
  have hu : u = besselPotential E F (-s) v := by
    rw [← hv, besselPotential_besselPotential_apply]
    simp
  obtain ⟨v', hv', hnorm⟩ := T.exists_apply_eq_toTemperedDistribution_and_norm_le
    ENNReal.ofNat_ne_top M hT hM v
  refine ⟨v', ?_, hnorm⟩
  rw [← hv', hu]
  simp only [T, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]

/-- **Multiplication by a Schwartz function preserves `H^s`**, for every real `s`: if the tempered
distribution `u` lies in `H^s`, so does `φ u`. -/
theorem MemSobolev.smulLeftCLM {s : ℝ} {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u) (φ : 𝓢(E, ℂ)) :
    MemSobolev s 2 (smulLeftCLM F (φ : E → ℂ) u) := by
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv', -⟩ := exists_besselPotential_smulLeftCLM_eq_and_norm_le s φ hv
  exact ⟨v', hv'⟩

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution

variable (s : ℝ) (φ : 𝓢(E, ℂ))

/-- **Multiplication by a Schwartz function** `φ` as a bounded operator on the Bessel-potential
space `H^s(E, F)`, for every real `s`. On the underlying tempered distributions it is Mathlib's
`TemperedDistribution.smulLeftCLM` (`BesselPotentialSpace.toDistr_smulLeftCLM`). -/
def smulLeftCLM : H^{s, 2}(E, F) →L[ℂ] H^{s, 2}(E, F) :=
  LinearMap.mkContinuous
    { toFun u :=
        ⟨TemperedDistribution.smulLeftCLM F (φ : E → ℂ) u.toDistr,
          (exists_besselPotential_smulLeftCLM_eq_and_norm_le s φ u.bessel_toDistr_eq_toLp).choose,
          (exists_besselPotential_smulLeftCLM_eq_and_norm_le s φ
            u.bessel_toDistr_eq_toLp).choose_spec.1⟩
      map_add' u₁ u₂ := ext (by simp)
      map_smul' c u := ext (by simp) }
    (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖)
    fun u ↦ by
      -- The `H^s` norm is the `L²` norm of the `toLp` field, which for `φ u` is the chosen `v'`.
      simp only [← norm_toLp_eq]
      exact (exists_besselPotential_smulLeftCLM_eq_and_norm_le s φ
        u.bessel_toDistr_eq_toLp).choose_spec.2

@[simp]
theorem toDistr_smulLeftCLM (u : H^{s, 2}(E, F)) :
    (smulLeftCLM s φ u).toDistr = TemperedDistribution.smulLeftCLM F (φ : E → ℂ) u.toDistr := by
  rfl

/-- The operator norm of multiplication by `φ` on `H^s` is at most
`2 ^ (|s| / 2) ∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ`. -/
theorem norm_smulLeftCLM_le :
    ‖(smulLeftCLM s φ : H^{s, 2}(E, F) →L[ℂ] H^{s, 2}(E, F))‖ ≤
      2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖ :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ by positivity)) _

/-- The `H^s` norm of `φ u` is at most `2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖u‖`. -/
theorem norm_smulLeftCLM_apply_le (u : H^{s, 2}(E, F)) :
    ‖smulLeftCLM s φ u‖ ≤ (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) * ‖u‖ :=
  (smulLeftCLM s φ).le_of_opNorm_le (norm_smulLeftCLM_le s φ) u

end BesselPotentialSpace

end InnerProductSpace
