/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Fourier multipliers on tempered distributions

Mathlib's Fourier multiplier `TemperedDistribution.fourierMultiplierCLM F g` on tempered
distributions conjugates multiplication by a temperate-growth symbol `g` with the Fourier
transform. This file records that it is additive in the symbol, the tempered analogue of
`SchwartzMap.fourierMultiplierCLM_add`, and two further facts about it.

The iterated line derivative `∂^{m} = ∂_{m₀} ⋯ ∂_{m_{k-1}}` is the multiplier with the
polynomial symbol `ξ ↦ ∏ᵢ 2πi ⟪ξ, mᵢ⟫`, extending Mathlib's
`TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM` from one derivative to several.

A multiplier only sees the Fourier transform of `u` where it lives: if `𝓕 u` vanishes on a set
`s` (`Distribution.IsVanishingOn`) and the symbol `g` equals `1` off `s`, in the sense that
`1 - g` is supported in `s`, then `g` acts as the identity on `u`. Together with the previous
identity this writes any derivative of a tempered distribution with compactly supported Fourier
transform as a multiplier with a compactly supported smooth, hence Schwartz, symbol; this is how
Bernstein's inequalities are proved.

## Main results

* `TemperedDistribution.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `TemperedDistribution.iteratedLineDerivOp_eq_fourierMultiplierCLM`: `∂^{m}` is the multiplier
  with symbol `ξ ↦ ∏ᵢ 2πi ⟪ξ, mᵢ⟫`.
* `TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`: a multiplier whose symbol
  is `1` wherever `𝓕 u` does not vanish fixes `u`.
-/

public section

namespace TemperedDistribution

open scoped SchwartzMap FourierTransform
open FourierTransform LineDeriv Real

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Fourier multipliers on tempered distributions are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

/-- The iterated line derivative `∂^{m}` of a tempered distribution is the Fourier multiplier with
the polynomial symbol `ξ ↦ ∏ᵢ 2πi ⟪ξ, mᵢ⟫`. -/
theorem iteratedLineDerivOp_eq_fourierMultiplierCLM {k : ℕ} (m : Fin k → E) (u : 𝓢'(E, F)) :
    ∂^{m} u = fourierMultiplierCLM F
      (fun ξ ↦ ∏ i, 2 * π * Complex.I * (inner ℝ ξ (m i) : ℂ)) u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hP : (fun ξ : E ↦ ∏ i, 2 * π * Complex.I * (inner ℝ ξ (Fin.tail m i) : ℂ)
        ).HasTemperateGrowth :=
      Function.HasTemperateGrowth.prod fun i _ ↦ by fun_prop
    have hinner : (fun ξ : E ↦ (inner ℝ ξ (m 0) : ℂ)).HasTemperateGrowth := by fun_prop
    rw [iteratedLineDerivOp_succ_left, ih, lineDeriv_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_fourierMultiplierCLM_apply hP hinner, ← smul_apply,
      ← fourierMultiplierCLM_smul (hP.mul hinner)]
    congr 2
    funext ξ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Fin.prod_univ_succ, Fin.tail]
    ring

/-- **Localization of a Fourier multiplier.** If the Fourier transform of `u` vanishes on a set
`s` and the symbol `g` is `1` off `s`, in the sense that `1 - g` is supported in `s`, then the
multiplier with symbol `g` fixes `u`. -/
theorem fourierMultiplierCLM_eq_self_of_isVanishingOn {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {s : Set E} {u : 𝓢'(E, F)} (hu : Distribution.IsVanishingOn ⇑(𝓕 u : 𝓢'(E, F)) s)
    (hgs : tsupport (1 - g) ⊆ s) :
    fourierMultiplierCLM F g u = u := by
  have h : smulLeftCLM F g (𝓕 u) = 𝓕 u := by
    ext w
    have hw : ⇑(w - SchwartzMap.smulLeftCLM ℂ g w) = fun ξ ↦ (1 - g) ξ • w ξ := by
      funext ξ
      simp [SchwartzMap.smulLeftCLM_apply_apply hg, sub_mul]
    have h0 : 𝓕 u (w - SchwartzMap.smulLeftCLM ℂ g w) = 0 :=
      hu _ (((congrArg tsupport hw).trans_subset (tsupport_smul_subset_left _ _)).trans hgs)
    rw [map_sub, sub_eq_zero] at h0
    rw [smulLeftCLM_apply_apply, h0]
  rw [fourierMultiplierCLM_apply, h, fourierInv_fourier_eq]

end TemperedDistribution
