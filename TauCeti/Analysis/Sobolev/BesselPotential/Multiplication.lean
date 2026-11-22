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
import TauCeti.MeasureTheory.Group.Integral
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
integrals are both `‖k‖₁` (`SchwartzMap.eLpNorm_rpow_smul_fourier_le_of_eq_integral`), bounds the
`H^s` norm of `φ u` (`SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le`).

To pass to all of `H^s`, conjugate by the Bessel potentials `J^s` (Mathlib's
`TemperedDistribution.besselPotential`, the Fourier multiplier with symbol `⟨ξ⟩ ^ s`): on `L²` the
operator `w ↦ J^s (φ J^{-s} w)`, with values in tempered distributions, is continuous, and on
Schwartz functions it takes values in `L²` with the bound above. Since Schwartz functions are
dense in `L²`, it takes values in `L²` everywhere, with the same bound
(`ContinuousLinearMap.exists_apply_eq_toTemperedDistribution_and_norm_le`). This extension works
for every operator that preserves Schwartz functions
(`TemperedDistribution.exists_besselPotential_apply_eq_and_norm_le_of_norm_toLp_le`).

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg`: the Bessel
  multipliers of orders `s` and `-s` are inverse on Schwartz functions.
* `TemperedDistribution.besselPotential_toTemperedDistributionCLM_eq`: the Bessel potential of a
  Schwartz function is its Schwartz-space Fourier multiplier.
* `SchwartzMap.eLpNorm_rpow_smul_fourier_le_of_eq_integral`: Schur's test on the weighted Fourier
  side, for a Fourier transform given by an integral dominated by a convolution kernel.
* `SchwartzMap.norm_toLp_fourierMultiplierCLM_le_of_eLpNorm_le`: a weighted Fourier-side `L²`
  bound is a bound between Bessel potentials.
* `SchwartzMap.eLpNorm_rpow_smul_fourier_smulLeftCLM_le`,
  `SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le`: the `H^s` estimate for Schwartz
  functions.
* `TemperedDistribution.exists_besselPotential_apply_eq_and_norm_le_of_norm_toLp_le`: an operator
  on tempered distributions that preserves Schwartz functions and is bounded from `H^s` to `H^t`
  on them is bounded from `H^s` to `H^t`.
* `TemperedDistribution.exists_besselPotential_smulLeftCLM_eq_and_norm_le`: the estimate on
  tempered distributions in `H^s`.
* `TemperedDistribution.MemSobolev.smulLeftCLM`: `φ u ∈ H^s` for `u ∈ H^s` and every real `s`, and
  `TemperedDistribution.MemSobolev.smulLeftCLM_mul`: the same for `g φ u` with `g` of temperate
  growth.
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
    rw [Pi.mul_apply, ← Complex.ofReal_mul, mul_comm,
      TauCeti.one_add_norm_sq_rpow_neg_mul_rpow, Complex.ofReal_one]
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
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, ← ofReal_norm, norm_smul, Complex.norm_real]
  refine congrArg (· ^ (1 / 2 : ℝ)) (lintegral_congr fun ξ ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]

omit [CompleteSpace F] in
/-- **Schur's test on the weighted Fourier side.** Let `f` and `g` be Schwartz functions with
`𝓕 g ξ = ∫ I ξ y dy`, where the integrand is dominated by a convolution kernel:
`⟨ξ⟩ ^ t ‖I ξ y‖ ≤ κ (ξ - y) ⟨y⟩ ^ s ‖𝓕 f y‖` for a nonnegative integrable `κ`. Then
`‖⟨ξ⟩ ^ t 𝓕 g‖_{L²} ≤ (∫ κ) ‖⟨ξ⟩ ^ s 𝓕 f‖_{L²}`. -/
theorem eLpNorm_rpow_smul_fourier_le_of_eq_integral {s t : ℝ} {κ : E → ℝ} (hκ : Integrable κ)
    (hκm : Measurable κ) (hκ0 : ∀ ζ, 0 ≤ κ ζ) {f g : 𝓢(E, F)} {I : E → E → F}
    (hI : ∀ ξ, 𝓕 g ξ = ∫ y, I ξ y)
    (hle : ∀ ξ y, (1 + ‖ξ‖ ^ 2) ^ (t / 2) * ‖I ξ y‖ ≤
      κ (ξ - y) * ((1 + ‖y‖ ^ 2) ^ (s / 2) * ‖𝓕 f y‖)) :
    eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (t / 2) : ℝ) : ℂ) • 𝓕 g ξ) 2 volume ≤
      ENNReal.ofReal (∫ ζ, κ ζ) *
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) 2 volume := by
  set k : E → ℝ≥0∞ := fun ζ ↦ ENNReal.ofReal (κ ζ)
  set G : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ (s / 2) * ‖𝓕 f y‖)
  have hk : Measurable k := ENNReal.measurable_ofReal.comp hκm
  have hG : Measurable G := ENNReal.measurable_ofReal.comp
    ((((measurable_const.add (measurable_norm.pow_const 2)).pow_const (s / 2))).mul
      (𝓕 f).continuous.norm.measurable)
  -- The pointwise bound by the convolution of `k` with `G`.
  have hpt (ξ : E) :
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (t / 2) * ‖𝓕 g ξ‖) ≤ ∫⁻ y, k (ξ - y) * G y := by
    rw [hI, ENNReal.ofReal_mul (by positivity), ofReal_norm]
    calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (t / 2)) * ‖∫ y, I ξ y‖ₑ
        ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (t / 2)) * ∫⁻ y, ‖I ξ y‖ₑ := by
          gcongr
          exact eNorm_integral_le_lintegral_eNorm _
      _ = ∫⁻ y, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (t / 2) * ‖I ξ y‖) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y ↦ ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ∫⁻ y, k (ξ - y) * G y := by
          refine lintegral_mono fun y ↦ ?_
          rw [← ENNReal.ofReal_mul (hκ0 _)]
          exact ENNReal.ofReal_le_ofReal (hle ξ y)
  -- Schur's test for the kernel `k (x - y)`, whose row and column integrals are `∫ κ`.
  have hschur := TauCeti.lintegral_rpow_lintegral_mul_le (μ := volume) (ν := volume)
    (k := fun x y ↦ k (x - y)) (hk.comp (measurable_fst.sub measurable_snd)).aemeasurable
    (g := G) hG.aemeasurable (p := 2) one_le_two
    (A := ENNReal.ofReal (∫ ζ, κ ζ)) (B := ENNReal.ofReal (∫ ζ, κ ζ))
    (.of_forall fun x ↦ (TauCeti.lintegral_ofReal_sub_left_eq_ofReal_integral hκ
      (.of_forall hκ0) x).le)
    (.of_forall fun y ↦ (TauCeti.lintegral_ofReal_sub_right_eq_ofReal_integral hκ
      (.of_forall hκ0) y).le)
  simp only [ENNReal.rpow_two] at hschur
  norm_num at hschur
  rw [eLpNorm_rpow_smul_fourier_eq _ _ (𝓕 g).continuous,
    eLpNorm_rpow_smul_fourier_eq _ _ (𝓕 f).continuous]
  calc (∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (t / 2) * ‖𝓕 g ξ‖) ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, (∫⁻ y, k (ξ - y) * G y) ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr with ξ
        exact hpt ξ
    _ ≤ (ENNReal.ofReal (∫ ζ, κ ζ) ^ 2 * ∫⁻ y, G y ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr
        simpa only [sq, mul_assoc] using hschur
    _ = ENNReal.ofReal (∫ ζ, κ ζ) * (∫⁻ y, G y ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

omit [CompleteSpace F] in
/-- The `H^s` estimate for multiplication by a Schwartz function, on the Fourier side:
`‖⟨ξ⟩ ^ s 𝓕 (φ f)‖_{L²} ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖⟨ξ⟩ ^ s 𝓕 f‖_{L²}`. It is
the pointwise Peetre bound followed by Schur's test for the convolution kernel. -/
theorem eLpNorm_rpow_smul_fourier_smulLeftCLM_le (s : ℝ) (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) :
    eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ)
        2 volume ≤
      ENNReal.ofReal (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) *
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) 2 volume := by
  rw [← integral_const_mul]
  refine eLpNorm_rpow_smul_fourier_le_of_eq_integral
    (((𝓕 φ).integrable_one_add_norm_sq_rpow_mul_norm (|s| / 2)).const_mul _) (by fun_prop)
    (fun ζ ↦ by positivity) (fourier_smulLeftCLM_apply_eq_integral_sub φ f) fun ξ y ↦ ?_
  -- Peetre's inequality `⟨ξ⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨y⟩ ^ s ⟨ξ - y⟩ ^ |s|`.
  have hP := TauCeti.one_add_norm_add_sq_rpow_le_mul s y (ξ - y)
  rw [add_sub_cancel] at hP
  rw [norm_smul]
  calc (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (‖𝓕 φ (ξ - y)‖ * ‖𝓕 f y‖)
      ≤ 2 ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) *
          (‖𝓕 φ (ξ - y)‖ * ‖𝓕 f y‖) := by gcongr
    _ = _ := by ring

end SchwartzMap

namespace TemperedDistribution

omit [CompleteSpace F] in
/-- The Bessel potential of a Schwartz function is the Schwartz function given by the Fourier
multiplier with the same symbol `⟨ξ⟩ ^ s`. -/
theorem besselPotential_toTemperedDistributionCLM_eq (s : ℝ) (f : 𝓢(E, F)) :
    besselPotential E F s (f : 𝓢'(E, F)) =
      (SchwartzMap.fourierMultiplierCLM F
        (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f : 𝓢'(E, F)) := by
  by_cases hF : CompleteSpace F
  · exact fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) f
  · have h0 : ∀ g : 𝓢(E, F), (g : 𝓢'(E, F)) = 0 := fun g ↦ by
      ext u
      exact (SchwartzMap.toTemperedDistributionCLM_apply_apply volume g u).trans
        (integral_of_not_completeSpace hF)
    rw [h0, h0, map_zero]

end TemperedDistribution

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℂ F] [CompleteSpace F]

namespace SchwartzMap

/-- A weighted Fourier-side `L²` bound `‖⟨ξ⟩ ^ t 𝓕 g‖_{L²} ≤ C ‖⟨ξ⟩ ^ s 𝓕 f‖_{L²}` between
Schwartz functions is the bound `‖J^t g‖_{L²} ≤ C ‖J^s f‖_{L²}` between their Bessel potentials,
where `J^r` is the Fourier multiplier with symbol `⟨ξ⟩ ^ r`. -/
theorem norm_toLp_fourierMultiplierCLM_le_of_eLpNorm_le {s t C : ℝ} (hC : 0 ≤ C)
    {f g : 𝓢(E, F)}
    (h : eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (t / 2) : ℝ) : ℂ) • 𝓕 g ξ) 2 volume ≤
      ENNReal.ofReal C *
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) 2 volume) :
    ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) g).toLp 2‖ ≤
      C *
        ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f).toLp 2‖ := by
  have hw (r : ℝ) : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hwf : (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) =
      smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 f) := by
    ext ξ
    rw [smulLeftCLM_apply_apply (hw s)]
  rw [norm_toLp_fourierMultiplierCLM_eq (hw t), norm_toLp_fourierMultiplierCLM_eq (hw s),
    ← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) h
  -- The remaining side goal is finiteness of the `L²` norm of a Schwartz function.
  rw [hwf]
  exact ((smulLeftCLM F _ (𝓕 f)).memLp 2 volume).eLpNorm_ne_top

/-- **Multiplication by a Schwartz function is bounded on `H^s`**, on Schwartz functions. With
the Bessel-potential weight `⟨ξ⟩ ^ s` of order `s ∈ ℝ`, Mathlib's convention for `H^s`,

`‖J^s (φ f)‖_{L²} ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖J^s f‖_{L²}`,

where `J^s` is the Fourier multiplier with symbol `⟨ξ⟩ ^ s`. -/
theorem norm_toLp_fourierMultiplierCLM_smulLeftCLM_le (s : ℝ) (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) :
    ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
        (smulLeftCLM F (φ : E → ℂ) f)).toLp 2‖ ≤
      (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) *
        ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f).toLp 2‖ :=
  norm_toLp_fourierMultiplierCLM_le_of_eLpNorm_le (by positivity)
    (eLpNorm_rpow_smul_fourier_smulLeftCLM_le s φ f)

end SchwartzMap

namespace TemperedDistribution

/-- **Extension from Schwartz functions to `H^s`.** Let `A` be a continuous linear operator on
tempered distributions that maps each Schwartz function `f` to the Schwartz function `A₀ f`, and
suppose that `‖J^t (A₀ f)‖_{L²} ≤ C ‖J^s f‖_{L²}` for all Schwartz `f`, where `J^r` is the
Fourier multiplier with symbol `⟨ξ⟩ ^ r`. If the tempered distribution `u` lies in `H^s`, with
`J^s u = v ∈ L²`, then `J^t (A u) = v'` for some `v' ∈ L²` with `‖v'‖ ≤ C ‖v‖`. -/
theorem exists_besselPotential_apply_eq_and_norm_le_of_norm_toLp_le {s t C : ℝ}
    (A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F)) (A₀ : 𝓢(E, F) →L[ℂ] 𝓢(E, F))
    (hA : ∀ f : 𝓢(E, F), A (f : 𝓢'(E, F)) = (A₀ f : 𝓢'(E, F)))
    (hA₀ : ∀ f : 𝓢(E, F),
      ‖(SchwartzMap.fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ))
          (A₀ f)).toLp 2‖ ≤
        C * ‖(SchwartzMap.fourierMultiplierCLM F
          (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f).toLp 2‖)
    {u : 𝓢'(E, F)} {v : Lp F 2 (volume : Measure E)} (hv : besselPotential E F s u = v) :
    ∃ v' : Lp F 2 (volume : Measure E), besselPotential E F t (A u) = v' ∧ ‖v'‖ ≤ C * ‖v‖ := by
  set Λ : ℝ → 𝓢(E, F) →L[ℂ] 𝓢(E, F) := fun r ↦
    SchwartzMap.fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ))
  -- The operator `w ↦ J^t (A (J^{-s} w))` on `L²`, with values in tempered distributions, is
  -- given on Schwartz functions by `M`, which is bounded in `L²`. Since Schwartz functions are
  -- dense in `L²`, it maps all of `L²` into `L²` with the same bound.
  set M : 𝓢(E, F) →L[ℂ] 𝓢(E, F) := Λ t ∘L A₀ ∘L Λ (-s)
  set T : Lp F 2 (volume : Measure E) →L[ℂ] 𝓢'(E, F) :=
    besselPotential E F t ∘L A ∘L besselPotential E F (-s) ∘L
      Lp.toTemperedDistributionCLM F volume 2
  have hM (ψ : 𝓢(E, F)) : ‖(M ψ).toLp 2 volume‖ ≤ C * ‖ψ.toLp 2 volume‖ := by
    have h := hA₀ (Λ (-s) ψ)
    simp only [Λ, SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg]
      at h
    simpa only [M, Λ, ContinuousLinearMap.comp_apply] using h
  have hT (ψ : 𝓢(E, F)) : T (ψ.toLp 2 volume) = ((M ψ).toLp 2 volume : 𝓢'(E, F)) := by
    simp only [T, M, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_toLp_eq, besselPotential_toTemperedDistributionCLM_eq, hA, Λ]
  have hu : u = besselPotential E F (-s) v := by
    rw [← hv, besselPotential_besselPotential_apply]
    simp
  obtain ⟨v', hv', hnorm⟩ := T.exists_apply_eq_toTemperedDistribution_and_norm_le
    ENNReal.ofNat_ne_top M hT hM v
  refine ⟨v', ?_, hnorm⟩
  rw [← hv', hu]
  simp only [T, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]

/-- **Multiplication by a Schwartz function is bounded on `H^s`**, for every real `s`. If the
tempered distribution `u` lies in `H^s`, with `J^s u = v ∈ L²`, then `J^s (φ u) = v'` for some
`v' ∈ L²` with `‖v'‖ ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖v‖`. -/
theorem exists_besselPotential_smulLeftCLM_eq_and_norm_le (s : ℝ) (φ : 𝓢(E, ℂ)) {u : 𝓢'(E, F)}
    {v : Lp F 2 (volume : Measure E)} (hv : besselPotential E F s u = v) :
    ∃ v' : Lp F 2 (volume : Measure E),
      besselPotential E F s (smulLeftCLM F (φ : E → ℂ) u) = v' ∧
        ‖v'‖ ≤ (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) * ‖v‖ :=
  exists_besselPotential_apply_eq_and_norm_le_of_norm_toLp_le _
    (SchwartzMap.smulLeftCLM F (φ : E → ℂ)) (fun _ ↦ smulLeftCLM_toTemperedDistributionCLM_eq _)
    (SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le s φ) hv

/-- **Multiplication by a Schwartz function preserves `H^s`**, for every real `s`: if the tempered
distribution `u` lies in `H^s`, so does `φ u`. -/
theorem MemSobolev.smulLeftCLM {s : ℝ} {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u) (φ : 𝓢(E, ℂ)) :
    MemSobolev s 2 (smulLeftCLM F (φ : E → ℂ) u) := by
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv', -⟩ := exists_besselPotential_smulLeftCLM_eq_and_norm_le s φ hv
  exact ⟨v', hv'⟩

/-- Multiplication by `g φ`, for `g` of temperate growth and `φ` a Schwartz function, preserves
`H^s`, since `g φ` is again a Schwartz function. -/
theorem MemSobolev.smulLeftCLM_mul {s : ℝ} {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (φ : 𝓢(E, ℂ)) :
    MemSobolev s 2 (TemperedDistribution.smulLeftCLM F (g * ⇑φ) u) := by
  have hgφ : g * ⇑φ = ⇑(SchwartzMap.smulLeftCLM ℂ g φ) := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, Pi.mul_apply, smul_eq_mul]
  rw [hgφ]
  exact hu.smulLeftCLM _

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
