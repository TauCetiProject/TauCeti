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
`SchwartzMap.fourierMultiplierCLM_add`.

The iterated line derivative `∂^{m} = ∂_{m₀} ⋯ ∂_{m_{k-1}}` is the multiplier with the
polynomial symbol `ξ ↦ ∏ᵢ 2πi ⟪ξ, mᵢ⟫`, extending Mathlib's
`TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM` from one derivative to several.

It also records how multipliers interact with frequency localization. A tempered distribution
`u` is localized in frequency to the complement of a set `s` when its Fourier transform vanishes
on `s` (`Distribution.IsVanishingOn (𝓕 u) s`). A multiplier whose symbol equals one away from a
closed subset of `s` then fixes `u`, and directional derivatives, which are the multipliers with
symbols `2πi ⟪ξ, m⟫`, preserve the localization. This is how band-limited functions are
reproduced by a multiplier with a smooth compactly supported symbol, the starting point of
Bernstein's inequalities.

## Main results

* `TemperedDistribution.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `TemperedDistribution.iteratedLineDerivOp_eq_fourierMultiplierCLM`: `∂^{m}` is the multiplier
  with symbol `ξ ↦ ∏ᵢ 2πi ⟪ξ, mᵢ⟫`.
* `TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`: a multiplier whose symbol
  is one outside the set where `𝓕 u` vanishes fixes `u`.
* `TemperedDistribution.isVanishingOn_fourier_lineDerivOp`,
  `TemperedDistribution.isVanishingOn_fourier_iteratedLineDerivOp`: derivatives preserve the
  vanishing of the Fourier transform.
-/

public section

namespace TemperedDistribution

open Distribution
open scoped SchwartzMap FourierTransform LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Fourier multipliers on tempered distributions are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

open Real in
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
    rw [LineDeriv.iteratedLineDerivOp_succ_left, ih, lineDeriv_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_fourierMultiplierCLM_apply hP hinner, ← smul_apply,
      ← fourierMultiplierCLM_smul (hP.mul hinner)]
    congr 2
    funext ξ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Fin.prod_univ_succ, Fin.tail]
    ring

/-- **Differentiation does not enlarge the spectrum.** If the Fourier transform of `u` vanishes on
`s`, so does that of `∂_m u`. -/
theorem isVanishingOn_fourier_lineDerivOp {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) (m : E) :
    IsVanishingOn (𝓕 (∂_{m} u : 𝓢'(E, F)) : 𝓢'(E, F)) s := by
  intro ψ hψ
  have h := Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM hu
    (g := fun x ↦ ((inner ℝ x m : ℝ) : ℂ)) (by fun_prop) ψ hψ
  rw [fourier_lineDerivOp_eq, smul_apply, h, smul_zero]

/-- **Differentiation does not enlarge the spectrum.** If the Fourier transform of `u` vanishes on
`s`, so does that of every iterated derivative `∂_{m₁} ⋯ ∂_{mₖ} u`. -/
theorem isVanishingOn_fourier_iteratedLineDerivOp {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) {k : ℕ} (m : Fin k → E) :
    IsVanishingOn (𝓕 (∂^{m} u : 𝓢'(E, F)) : 𝓢'(E, F)) s := by
  induction k with
  | zero => simpa [LineDeriv.iteratedLineDerivOp_zero] using hu
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    exact isVanishingOn_fourier_lineDerivOp (ih _) _

/-- **A multiplier equal to one near the spectrum is the identity.** If the Fourier transform of a
tempered distribution `u` vanishes on `s`, and the symbol `g` of temperate growth equals one
outside a closed subset of `s` (that is, `tsupport (g - 1) ⊆ s`), then the Fourier multiplier
with symbol `g` fixes `u`. -/
theorem fourierMultiplierCLM_eq_self_of_isVanishingOn {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hgs : tsupport (g - 1) ⊆ s) : fourierMultiplierCLM F g u = u := by
  have h : smulLeftCLM F g (𝓕 u) = 𝓕 u := by
    ext ψ
    rw [smulLeftCLM_apply_apply, ← sub_eq_zero, ← map_sub]
    refine hu _ (subset_trans ?_ hgs)
    have : ⇑(SchwartzMap.smulLeftCLM ℂ g ψ - ψ) = fun ξ ↦ (g - 1) ξ • ψ ξ := by
      ext ξ
      simp [SchwartzMap.smulLeftCLM_apply_apply hg, sub_mul]
    rw [this]
    exact tsupport_smul_subset_left _ _
  rw [fourierMultiplierCLM_apply, h, FourierTransform.fourierInv_fourier_eq]

end TemperedDistribution
