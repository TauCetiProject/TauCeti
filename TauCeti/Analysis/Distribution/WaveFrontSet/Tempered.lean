/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.Distribution.TestFunction.FourierAtom
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.Sobolev.BesselPotential.Duality

/-!
# Wave front sets of tempered distributions

A tempered distribution `S` on `E` restricts to a distribution on every open set `Ω`
(`TemperedDistribution.toDistribution`), so it has a wave front set. Its localized Fourier
transform with a cutoff `φ` is the value `S (φ e_η)` of `S` on the modulated cutoff
`φ e_η`, `e_η x = 𝐞 (-⟪x, η⟫)` (`TemperedDistribution.localFourier_toDistribution`).

For an element `u` of the Bessel-potential space `H^s` this value decays like `⟨η⟩ ^ (-s)`: the
Fourier transform of `φ e_η` is the translate `𝓕 φ (· + η)`
(`TestFunction.fourier_fourierAtomMulSchwartzMap`), so by Peetre's inequality the
`H^{-s}` norm of `φ e_η` is at most a constant times `⟨η⟩ ^ (-s)`, and `u` pairs `H^s` with
`H^{-s}` (`TestFunction.exists_norm_toDistr_fourierAtomMulSchwartzMap_le`). In particular a
tempered distribution lying in every `H^s` has empty wave front set
(`TemperedDistribution.waveFrontSet_toDistribution_eq_empty`).

## Main results

* `TemperedDistribution.localFourier_toDistribution`: the localized Fourier transform of the
  restriction of `S` is `η ↦ S (φ e_η)`, with `φ e_η` the Schwartz function
  `TestFunction.fourierAtomMulSchwartzMap`.
* `TestFunction.exists_norm_toBesselPotentialSpaceCLM_fourierAtomMulSchwartzMap_le`:
  `‖φ e_η‖_{H^{-s}} ≤ C ⟨η⟩ ^ (-s)`.
* `TestFunction.exists_norm_toDistr_fourierAtomMulSchwartzMap_le`:
  `‖u (φ e_η)‖ ≤ C ‖u‖_{H^s} ⟨η⟩ ^ (-s)`.
* `TemperedDistribution.waveFrontSet_toDistribution_eq_empty`: a tempered distribution in every
  `H^s` has empty wave front set.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Complex MeasureTheory Set TopologicalSpace TestFunction FourierTransform
open scoped Distributions SchwartzMap BesselPotentialSpace RealInnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

namespace TemperedDistribution

/-- **The localized Fourier transform of a restricted tempered distribution.** The localized
Fourier transform of the restriction of `S` to `Ω`, with cutoff `φ`, is `η ↦ S (φ e_η)`. -/
@[simp]
theorem localFourier_toDistribution (S : 𝓢'(E, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (toDistribution Ω S).localFourier φ η = S (φ.fourierAtomMulSchwartzMap η) := by
  rw [Distribution.localFourier_def, Distribution.complexPairing_toDistribution]
  congr 1
  ext x
  simp [bilinLeftCLM_apply]

end TemperedDistribution

namespace TestFunction

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The `H^{-s}` norm of a modulated cutoff.** For a cutoff `φ` and an order `s`, the norm of
`φ e_η` in the Bessel-potential space `H^{-s}` is at most `C ⟨η⟩ ^ (-s)`, by Peetre's inequality,
since the Fourier transform of `φ e_η` is a translate of that of `φ`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_fourierAtomMulSchwartzMap_le (s : ℝ) (φ : 𝓓(Ω, ℂ)) :
    ∃ C, 0 ≤ C ∧ ∀ η : E,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (-s) 2 (φ.fourierAtomMulSchwartzMap η)‖ ≤
        C * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by
  set h : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (|s| / 2) : ℝ) : ℂ) • 𝓕 (toSchwartzMapCLM ℂ φ) ξ
  have hh : MemLp h 2 volume :=
    SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier |s| (toSchwartzMapCLM ℂ φ) 2
  refine ⟨2 ^ (|s| / 2) * (eLpNorm h 2 volume).toReal, by positivity, fun η ↦ ?_⟩
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM]
  set c : ℝ := 2 ^ (|s| / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)
  -- Peetre's inequality `⟨ξ⟩ ^ (-s) ≤ 2 ^ (|s| / 2) ⟨ξ + η⟩ ^ |s| ⟨η⟩ ^ (-s)`.
  have hpt (ξ : E) : ‖(((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) • 𝓕 (φ.fourierAtomMulSchwartzMap η) ξ‖ ≤
      ‖c • h (ξ + η)‖ := by
    have hP := TauCeti.one_add_norm_sq_rpow_le_mul_sub (-s) ξ (-η)
    rw [sub_neg_eq_add, norm_neg, abs_neg] at hP
    simp only [fourier_fourierAtomMulSchwartzMap, h, c, norm_smul, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2) _),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ + η‖ ^ 2) _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (|s| / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2))]
    calc (1 + ‖ξ‖ ^ 2) ^ (-s / 2) * ‖𝓕 (toSchwartzMapCLM ℂ φ) (ξ + η)‖
        ≤ (2 ^ (|s| / 2) * (1 + ‖ξ + η‖ ^ 2) ^ (|s| / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)) *
            ‖𝓕 (toSchwartzMapCLM ℂ φ) (ξ + η)‖ := by
          rw [neg_div] at hP ⊢
          gcongr
      _ = 2 ^ (|s| / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2) *
            ((1 + ‖ξ + η‖ ^ 2) ^ (|s| / 2) * ‖𝓕 (toSchwartzMapCLM ℂ φ) (ξ + η)‖) := by ring
  -- The translate of `h` has the same `L²` norm.
  have hcs : eLpNorm (fun ξ ↦ c • h (ξ + η)) 2 volume = ‖c‖ₑ * eLpNorm h 2 volume := by
    have htr : eLpNorm (fun ξ ↦ h (ξ + η)) 2 volume = eLpNorm h 2 volume :=
      eLpNorm_comp_measurePreserving hh.aestronglyMeasurable (measurePreserving_add_right volume η)
    exact (eLpNorm_const_smul c (fun ξ ↦ h (ξ + η)) 2 volume).trans (by rw [htr])
  calc (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) • 𝓕 (φ.fourierAtomMulSchwartzMap η) ξ)
        2 volume).toReal
      ≤ (eLpNorm (fun ξ ↦ c • h (ξ + η)) 2 volume).toReal := by
        refine ENNReal.toReal_mono ?_ (eLpNorm_mono
          (SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier (-s) (φ.fourierAtomMulSchwartzMap η)
            2).aestronglyMeasurable hpt)
        rw [hcs]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top hh.eLpNorm_lt_top.ne
    _ = 2 ^ (|s| / 2) * (eLpNorm h 2 volume).toReal * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by
        rw [hcs, ENNReal.toReal_mul, toReal_eNorm, Real.norm_of_nonneg (by positivity)]
        ring

/-- **Decay of the localized Fourier transform on `H^s`.** For a cutoff `φ` and an order `s`
there is a constant `C` with `‖u (φ e_η)‖ ≤ C ‖u‖ ⟨η⟩ ^ (-s)` for every `u ∈ H^s` and every
frequency `η`. -/
theorem exists_norm_toDistr_fourierAtomMulSchwartzMap_le (s : ℝ) (φ : 𝓓(Ω, ℂ)) :
    ∃ C, 0 ≤ C ∧ ∀ (u : H^{s}(E, ℂ)) (η : E),
      ‖u.toDistr (φ.fourierAtomMulSchwartzMap η)‖ ≤ C * ‖u‖ * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by
  set B := (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).flip
  obtain ⟨C, hC0, hC⟩ := φ.exists_norm_toBesselPotentialSpaceCLM_fourierAtomMulSchwartzMap_le s
  refine ⟨‖B‖ * C, by positivity, fun u η ↦ ?_⟩
  rw [BesselPotentialSpace.toDistr_apply_eq_besselPotentialPairing 2]
  calc ‖B.besselPotentialPairing s 2 2 u
          (SchwartzMap.toBesselPotentialSpaceCLM (-s) 2 (φ.fourierAtomMulSchwartzMap η))‖
      ≤ ‖B‖ * ‖u‖ *
          ‖SchwartzMap.toBesselPotentialSpaceCLM (-s) 2 (φ.fourierAtomMulSchwartzMap η)‖ :=
        B.norm_besselPotentialPairing_le s u _
    _ ≤ ‖B‖ * ‖u‖ * (C * (1 + ‖η‖ ^ 2) ^ (-s / 2)) := by gcongr; exact hC η
    _ = ‖B‖ * C * ‖u‖ * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by ring

end TestFunction

namespace TemperedDistribution

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Tempered distributions in every `H^s` have empty wave front set.** If `S` lies in the
Bessel-potential space `H^s` for every real `s`, its restriction to any open set is microlocally
smooth everywhere. -/
theorem waveFrontSet_toDistribution_eq_empty {S : 𝓢'(E, ℂ)} (hS : ∀ s : ℝ, MemSobolev s 2 S) :
    (toDistribution Ω S).waveFrontSet = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun ⟨x, ξ⟩ hp ↦
    (Distribution.mem_waveFrontSet_iff.1 hp).2.2 ?_
  obtain ⟨φ, -, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (Ω.isOpen.mem_nhds (Distribution.mem_waveFrontSet_iff.1 hp).1) subset_rfl (1 : ℂ)
  refine Distribution.isMicrolocallySmoothAt_of_forall_decay (φ := φ) (by simp [hφx])
    (fun N ↦ ?_) ξ
  -- Use the decay in `H^{2N}`, since `1 + ‖η‖ ≤ 2 (1 + ‖η‖ ^ 2)`.
  obtain ⟨C, -, hdecay⟩ := exists_norm_toDistr_fourierAtomMulSchwartzMap_le (2 * N) φ
  set u := (hS (2 * N)).toBesselPotentialSpace
  refine ⟨2 ^ N * (C * ‖u‖), fun η ↦ ?_⟩
  have hu : u.toDistr = S := MemSobolev.toBesselPotentialSpace_toDistr _
  have hpow : (1 + ‖η‖ ^ 2) ^ (-(2 * (N : ℝ)) / 2) = ((1 + ‖η‖ ^ 2) ^ N)⁻¹ := by
    rw [neg_div, mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  have hle : (1 + ‖η‖) ^ N ≤ 2 ^ N * (1 + ‖η‖ ^ 2) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg η]) N
  rw [localFourier_toDistribution, ← hu]
  calc (1 + ‖η‖) ^ N * ‖u.toDistr (φ.fourierAtomMulSchwartzMap η)‖
      ≤ (2 ^ N * (1 + ‖η‖ ^ 2) ^ N) * (C * ‖u‖ * ((1 + ‖η‖ ^ 2) ^ N)⁻¹) := by
        rw [← hpow]
        exact mul_le_mul hle (hdecay u η) (norm_nonneg _) (by positivity)
    _ = 2 ^ N * (C * ‖u‖) := by
        field_simp

end TemperedDistribution
