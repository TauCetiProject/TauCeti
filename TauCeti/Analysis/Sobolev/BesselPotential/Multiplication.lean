/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

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

Young's inequality `‖k ⋆ g‖₂ ≤ ‖k‖₁ ‖g‖₂` bounds the `H^s` norm of `φ u`
(`SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le`).

To pass to all of `H^s`, conjugate by the Bessel potentials `J^s` (Mathlib's
`TemperedDistribution.besselPotential`, the Fourier multiplier with symbol `⟨ξ⟩ ^ s`): on `L²` the
operator
`w ↦ J^s (φ J^{-s} w)`, with values in tempered distributions, is continuous, and on the dense
subspace of Schwartz functions it takes values in `L²` with the bound above. Its bounded extension
to `L²` (`LinearMap.extendOfNorm`) agrees with it everywhere, since both are continuous into the
Hausdorff space of tempered distributions.

## Main declarations

* `SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le`: the `H^s` estimate for Schwartz
  functions.
* `TemperedDistribution.exists_besselPotential_smulLeftCLM_eq_and_norm_le`: the estimate on
  tempered distributions in `H^s`.
* `TemperedDistribution.MemSobolev.smulLeftCLM`: `φ u ∈ H^s` for `u ∈ H^s` and every real `s`.
* `BesselPotentialSpace.smulLeftCLM`: multiplication by `φ` as a bounded operator on `H^s`, with
  `BesselPotentialSpace.norm_smulLeftCLM_le`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (Sobolev spaces on `ℝⁿ`: Peetre's inequality and multiplication by Schwartz functions).
* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., AMS, 2001, Theorem 4.2 (Young's inequality).
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

section Young

/-- Pointwise Cauchy–Schwarz for a convolution of extended nonnegative functions:
`(∫⁻ y, k y * g (x - y)) ^ 2 ≤ (∫⁻ k) * ∫⁻ y, k y * g (x - y) ^ 2`. -/
private theorem sq_lintegral_mul_sub_le {k g : E → ℝ≥0∞} (hk : Measurable k) (hg : Measurable g)
    (x : E) :
    (∫⁻ y, k y * g (x - y)) ^ 2 ≤ (∫⁻ y, k y) * ∫⁻ y, k y * g (x - y) ^ 2 := by
  have hgx : Measurable fun y ↦ g (x - y) := hg.comp (measurable_const.sub measurable_id)
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    (f := fun y ↦ k y ^ (1 / 2 : ℝ)) (g := fun y ↦ k y ^ (1 / 2 : ℝ) * g (x - y))
    (hk.pow_const (1 / 2 : ℝ)).aemeasurable ((hk.pow_const (1 / 2 : ℝ)).mul hgx).aemeasurable
  simp only [Pi.mul_apply] at hcs
  have h₀ : ∫⁻ y, k y ^ (1 / 2 : ℝ) * (k y ^ (1 / 2 : ℝ) * g (x - y)) =
      ∫⁻ y, k y * g (x - y) := by
    congr 1
    ext y
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h₁ : ∫⁻ y, (k y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = ∫⁻ y, k y := by
    congr 1
    ext y
    rw [← ENNReal.rpow_mul]
    norm_num
  have h₂ : ∫⁻ y, (k y ^ (1 / 2 : ℝ) * g (x - y)) ^ (2 : ℝ) = ∫⁻ y, k y * g (x - y) ^ 2 := by
    congr 1
    ext y
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ENNReal.rpow_two]
    norm_num
  rw [h₀, h₁, h₂] at hcs
  calc (∫⁻ y, k y * g (x - y)) ^ 2
      ≤ ((∫⁻ y, k y) ^ (1 / 2 : ℝ) * (∫⁻ y, k y * g (x - y) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ y, k y) * ∫⁻ y, k y * g (x - y) ^ 2 := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num

/-- Young's inequality `L¹ ⋆ L² ⊆ L²` for extended nonnegative functions:
`∫⁻ x, (∫⁻ y, k y * g (x - y)) ^ 2 ≤ (∫⁻ k) ^ 2 * ∫⁻ g ^ 2`. -/
private theorem lintegral_sq_lintegral_mul_sub_le {k g : E → ℝ≥0∞} (hk : Measurable k)
    (hg : Measurable g) :
    ∫⁻ x, (∫⁻ y, k y * g (x - y)) ^ 2 ≤ (∫⁻ y, k y) ^ 2 * ∫⁻ x, g x ^ 2 := by
  have hm : Measurable (Function.uncurry fun x y : E ↦ k y * g (x - y) ^ 2) :=
    (hk.comp measurable_snd).mul ((hg.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  calc ∫⁻ x, (∫⁻ y, k y * g (x - y)) ^ 2
      ≤ ∫⁻ x, (∫⁻ y, k y) * ∫⁻ y, k y * g (x - y) ^ 2 :=
        lintegral_mono fun x ↦ sq_lintegral_mul_sub_le hk hg x
    _ = (∫⁻ y, k y) * ∫⁻ y, ∫⁻ x, k y * g (x - y) ^ 2 := by
      rw [lintegral_const_mul _ (by exact hm.lintegral_prod_right'),
        lintegral_lintegral_swap (by exact hm.aemeasurable)]
    _ = (∫⁻ y, k y) * ∫⁻ y, k y * ∫⁻ x, g x ^ 2 := by
      congr 1
      refine lintegral_congr fun y ↦ ?_
      rw [lintegral_const_mul _ (by exact (hg.comp (measurable_id.sub_const y)).pow_const 2)]
      congr 1
      exact lintegral_sub_right_eq_self (fun x ↦ g x ^ 2) y
    _ = (∫⁻ y, k y) ^ 2 * ∫⁻ x, g x ^ 2 := by
      rw [lintegral_mul_const _ hk, sq, mul_assoc]

end Young

namespace SchwartzMap

/-- The Peetre weight `ζ ↦ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖` of a Schwartz function is integrable. -/
theorem integrable_one_add_norm_sq_rpow_mul_norm_fourier (r : ℝ) (φ : 𝓢(E, ℂ)) :
    Integrable fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ r * ‖𝓕 φ ζ‖ := by
  have hg := Function.hasTemperateGrowth_one_add_norm_sq_rpow E r
  refine (smulLeftCLM ℂ (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ r) (𝓕 φ)).integrable.norm.congr ?_
  refine .of_forall fun ζ ↦ ?_
  dsimp only
  rw [smulLeftCLM_apply_apply hg, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- The pointwise Peetre bound behind the `H^s` estimate: for Schwartz functions `φ` and `f`,
`⟨ξ⟩ ^ s ‖𝓕 (φ f) ξ‖` is bounded by the convolution of `2 ^ (|s| / 2) ⟨·⟩ ^ |s| ‖𝓕 φ‖` with
`⟨·⟩ ^ s ‖𝓕 f‖`. -/
private theorem enorm_rpow_smul_fourier_smulLeftCLM_le (s : ℝ) (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F))
    (ξ : E) :
    ‖(((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal (2 ^ (|s| / 2) * ((1 + ‖t‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ t‖)) *
        ‖(((1 + ‖ξ - t‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f (ξ - t)‖ₑ := by
  rw [fourier_smulLeftCLM_apply, enorm_smul]
  calc ‖(((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)‖ₑ * ‖∫ t, 𝓕 φ t • 𝓕 f (ξ - t)‖ₑ
      ≤ ‖(((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)‖ₑ * ∫⁻ t, ‖𝓕 φ t • 𝓕 f (ξ - t)‖ₑ := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, ‖(((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)‖ₑ * ‖𝓕 φ t • 𝓕 f (ξ - t)‖ₑ :=
        (lintegral_const_mul' _ _ enorm_ne_top).symm
    _ ≤ _ := by
      refine lintegral_mono fun t ↦ ?_
      have hn (r : ℝ) (hr : 0 ≤ r) (v : F) :
          ‖(r : ℂ) • v‖ₑ = ENNReal.ofReal (r * ‖v‖) := by
        rw [← ofReal_norm, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr]
      rw [hn _ (by positivity), ← ofReal_norm (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ),
        ← ofReal_norm (𝓕 φ t • 𝓕 f (ξ - t)), ← ENNReal.ofReal_mul (norm_nonneg _),
        ← ENNReal.ofReal_mul (by positivity), norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hP := TauCeti.one_add_norm_add_sq_rpow_le_mul s (ξ - t) t
      rw [sub_add_cancel] at hP
      have h₁ : 0 ≤ ‖𝓕 φ t‖ * ‖𝓕 f (ξ - t)‖ := by positivity
      calc (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (‖𝓕 φ t‖ * ‖𝓕 f (ξ - t)‖)
          ≤ 2 ^ (|s| / 2) * (1 + ‖ξ - t‖ ^ 2) ^ (s / 2) * (1 + ‖t‖ ^ 2) ^ (|s| / 2) *
              (‖𝓕 φ t‖ * ‖𝓕 f (ξ - t)‖) := mul_le_mul_of_nonneg_right hP h₁
        _ = _ := by ring

/-- **Multiplication by a Schwartz function is bounded on `H^s`**, on Schwartz functions. With
the Bessel-potential weight `⟨ξ⟩ ^ s` of order `s ∈ ℝ`, Mathlib's convention for `H^s`,

`‖J^s (φ f)‖_{L²} ≤ 2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖J^s f‖_{L²}`,

where `J^s` is the Fourier multiplier with symbol `⟨ξ⟩ ^ s`. -/
theorem norm_toLp_fourierMultiplierCLM_smulLeftCLM_le (s : ℝ) (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) :
    ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
        (smulLeftCLM F (φ : E → ℂ) f)).toLp 2‖ ≤
      (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) *
        ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f).toLp 2‖ := by
  set w : E → ℂ := fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  have hwg (g : 𝓢(E, F)) : (fun ξ ↦ w ξ • 𝓕 g ξ) = smulLeftCLM F w (𝓕 g) := by
    ext ξ
    rw [smulLeftCLM_apply_apply hw]
  -- By Plancherel, the `H^s` norm of a Schwartz function is the `L²` norm of `w • 𝓕 g`.
  have hnorm (g : 𝓢(E, F)) : ‖(fourierMultiplierCLM F w g).toLp 2‖ =
      (eLpNorm (fun ξ ↦ w ξ • 𝓕 g ξ) 2 volume).toReal := by
    rw [← norm_fourier_toL2_eq, fourierMultiplierCLM_apply, fourier_fourierInv_eq, norm_toLp,
      hwg]
  set k : E → ℝ≥0∞ :=
    fun ζ ↦ ENNReal.ofReal (2 ^ (|s| / 2) * ((1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖))
  set g : E → ℝ≥0∞ := fun η ↦ ‖w η • 𝓕 f η‖ₑ
  have hk : Measurable k := by fun_prop
  have hg : Measurable g := by
    have : g = fun η ↦ ‖smulLeftCLM F w (𝓕 f) η‖ₑ := by simp only [g, ← hwg]
    rw [this]
    exact (smulLeftCLM F w (𝓕 f)).continuous.enorm.measurable
  have hint := (integrable_one_add_norm_sq_rpow_mul_norm_fourier (|s| / 2) φ).const_mul
    (2 ^ (|s| / 2))
  have hk_int : ∫⁻ ζ, k ζ = ENNReal.ofReal
      (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun ζ ↦ by positivity)]
  have hL2 (g : 𝓢(E, F)) : eLpNorm (fun ξ ↦ w ξ • 𝓕 g ξ) 2 volume =
      (∫⁻ x, ‖w x • 𝓕 g x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (by rw [hwg]; exact (smulLeftCLM F w (𝓕 g)).continuous.aestronglyMeasurable)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hmain : eLpNorm (fun ξ ↦ w ξ • 𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ) 2 volume ≤
      ENNReal.ofReal (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) *
        eLpNorm (fun ξ ↦ w ξ • 𝓕 f ξ) 2 volume := by
    rw [hL2, hL2, ← hk_int]
    calc (∫⁻ ξ, ‖w ξ • 𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (∫⁻ ξ, (∫⁻ t, k t * g (ξ - t)) ^ 2) ^ (1 / 2 : ℝ) := by
          gcongr with ξ
          exact enorm_rpow_smul_fourier_smulLeftCLM_le s φ f ξ
      _ ≤ ((∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) := by
          gcongr
          exact lintegral_sq_lintegral_mul_sub_le hk hg
      _ = (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
            ← ENNReal.rpow_mul]
          norm_num
  rw [hnorm, hnorm]
  have hfin : eLpNorm (fun ξ ↦ w ξ • 𝓕 f ξ) 2 volume ≠ ⊤ := by
    rw [hwg]
    exact ((smulLeftCLM F w (𝓕 f)).memLp 2 volume).eLpNorm_ne_top
  calc (eLpNorm (fun ξ ↦ w ξ • 𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ) 2 volume).toReal
      ≤ (ENNReal.ofReal (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) *
          eLpNorm (fun ξ ↦ w ξ • 𝓕 f ξ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hmain
    _ = _ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

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
  have hΛ (ψ : 𝓢(E, F)) : Λ s (Λ (-s) ψ) = ψ := by
    simp only [Λ]
    rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
    have : ((fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) *
        fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) = fun _ ↦ 1 := by
      ext x
      rw [Pi.mul_apply, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
      simp [neg_div]
    rw [this, SchwartzMap.fourierMultiplierCLM_const]
    simp
  -- The operator `w ↦ J^s (φ J^{-s} w)` on Schwartz functions, and its bound in `L²`.
  set M : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
    Λ s ∘L SchwartzMap.smulLeftCLM F (φ : E → ℂ) ∘L Λ (-s)
  set e : 𝓢(E, F) →ₗ[ℂ] Lp F 2 (volume : Measure E) :=
    (SchwartzMap.toLpCLM ℂ F 2 volume).toLinearMap
  set f₀ : 𝓢(E, F) →ₗ[ℂ] Lp F 2 (volume : Measure E) :=
    (SchwartzMap.toLpCLM ℂ F 2 volume ∘L M).toLinearMap
  have hbound (ψ : 𝓢(E, F)) : ‖f₀ ψ‖ ≤ C * ‖e ψ‖ := by
    have h := SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le s φ (Λ (-s) ψ)
    -- Fold the multipliers in `h` back into the local abbreviation `Λ`, so that `hΛ` applies.
    change ‖(Λ s _).toLp 2 volume‖ ≤ C * ‖(Λ s (Λ (-s) ψ)).toLp 2 volume‖ at h
    rw [hΛ] at h
    exact h
  have hdense : DenseRange e :=
    SchwartzMap.denseRange_toLpCLM (F := F) (p := 2) (μ := volume) ENNReal.ofNat_ne_top
  set K := f₀.extendOfNorm e
  -- The same operator on `L²`, with values in tempered distributions.
  set T : Lp F 2 (volume : Measure E) →L[ℂ] 𝓢'(E, F) :=
    besselPotential E F s ∘L smulLeftCLM F (φ : E → ℂ) ∘L besselPotential E F (-s) ∘L
      Lp.toTemperedDistributionCLM F volume 2
  have hT (w : Lp F 2 (volume : Measure E)) : T w = (K w : 𝓢'(E, F)) := by
    refine congrFun (hdense.equalizer (g := T) (h := fun w ↦ (K w : 𝓢'(E, F))) T.continuous
      ((Lp.toTemperedDistributionCLM F volume 2).continuous.comp K.continuous) ?_) w
    ext1 ψ
    simp only [Function.comp_apply]
    rw [LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩]
    have hJ (t : ℝ) (χ : 𝓢(E, F)) : besselPotential E F t (χ : 𝓢'(E, F)) = (Λ t χ : 𝓢'(E, F)) :=
      fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) χ
    simp only [T, f₀, e, M, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      SchwartzMap.toLpCLM_apply, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_toLp_eq, hJ,
      smulLeftCLM_toTemperedDistributionCLM_eq φ.hasTemperateGrowth]
  refine ⟨K v, ?_, LinearMap.norm_extendOfNorm_apply_le hdense C hbound v⟩
  have hu : u = besselPotential E F (-s) v := by
    rw [← hv, besselPotential_besselPotential_apply]
    simp
  rw [← hT, hu]
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
      simp only [← norm_toLp_eq]
      exact (exists_besselPotential_smulLeftCLM_eq_and_norm_le s φ
        u.bessel_toDistr_eq_toLp).choose_spec.2

@[simp]
theorem toDistr_smulLeftCLM (u : H^{s, 2}(E, F)) :
    (smulLeftCLM s φ u).toDistr = TemperedDistribution.smulLeftCLM F (φ : E → ℂ) u.toDistr := by
  rfl

/-- The `H^s` norm of `φ u` is at most `2 ^ (|s| / 2) (∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ) ‖u‖`. -/
theorem norm_smulLeftCLM_apply_le (u : H^{s, 2}(E, F)) :
    ‖smulLeftCLM s φ u‖ ≤ (2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) * ‖u‖ := by
  simp only [← norm_toLp_eq]
  exact (exists_besselPotential_smulLeftCLM_eq_and_norm_le s φ
    u.bessel_toDistr_eq_toLp).choose_spec.2

/-- The operator norm of multiplication by `φ` on `H^s` is at most
`2 ^ (|s| / 2) ∫ ⟨ζ⟩ ^ |s| ‖𝓕 φ ζ‖ dζ`. -/
theorem norm_smulLeftCLM_le :
    ‖(smulLeftCLM s φ : H^{s, 2}(E, F) →L[ℂ] H^{s, 2}(E, F))‖ ≤
      2 ^ (|s| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ by positivity))
    (norm_smulLeftCLM_apply_le s φ)

end BesselPotentialSpace
