/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.Support

/-!
# Fourier multipliers on tempered distributions

Mathlib's Fourier multiplier `TemperedDistribution.fourierMultiplierCLM F g` on tempered
distributions conjugates multiplication by a temperate-growth symbol `g` with the Fourier
transform. This file records that it is additive in the symbol, the tempered analogue of
`SchwartzMap.fourierMultiplierCLM_add`, that it absorbs derivatives into the symbol, and how it
interacts with the frequency support of a tempered distribution.

The frequency support is expressed through Mathlib's `Distribution.IsVanishingOn`: the Fourier
transform `𝓕 u` vanishes on `s` when it annihilates every Schwartz function supported in `s`. A
multiplier whose symbol equals `1` near the complement of `s` fixes such a `u`: this reproducing
property is how frequency-localized functions are written as convolutions with a Schwartz kernel,
as in the Bernstein inequalities. Conversely, the Fourier transform of `T_g u` vanishes off the
support of `g`, so a multiplier with a compactly supported symbol produces a frequency-localized
distribution, and derivatives do not enlarge the frequency support.

## Main results

* `TemperedDistribution.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `TemperedDistribution.fourierMultiplierCLM_lineDerivOp`: a multiplier applied to `∂ₘ u` is the
  multiplier with symbol `2πi ⟪ξ, m⟫ g ξ` applied to `u`.
* `TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`: a multiplier equal to `1`
  near the frequency support of `u` fixes `u`.
* `TemperedDistribution.isVanishingOn_fourier_fourierMultiplierCLM`: the Fourier transform of
  `T_g u` vanishes off the support of `g`.
* `TemperedDistribution.isVanishingOn_fourier_lineDerivOp`,
  `TemperedDistribution.isVanishingOn_fourier_iteratedLineDerivOp`: derivatives preserve the
  vanishing of the Fourier transform.
-/

public section

namespace TemperedDistribution

open Filter Set Topology FourierTransform LineDeriv Real
open Distribution (IsVanishingOn)
open scoped SchwartzMap RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Fourier multipliers on tempered distributions are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

/-- A Fourier multiplier applied to a derivative `∂ₘ u` is the multiplier with the symbol
`2πi ⟪ξ, m⟫ g ξ` applied to `u`. -/
theorem fourierMultiplierCLM_lineDerivOp {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢'(E, F))
    (m : E) :
    fourierMultiplierCLM F g (∂_{m} u) =
      fourierMultiplierCLM F ((2 * π * Complex.I) • ((fun ξ ↦ ((⟪ξ, m⟫ : ℝ) : ℂ)) * g)) u := by
  have hm : (fun ξ ↦ ((⟪ξ, m⟫ : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [lineDeriv_eq_fourierMultiplierCLM, map_smul,
    fourierMultiplierCLM_fourierMultiplierCLM_apply hm hg, fourierMultiplierCLM_smul (hm.mul hg),
    smul_apply]

/-- **Reproducing property.** If the Fourier transform of `u` vanishes on `s` and the symbol `g`
equals `1` on a neighbourhood of `sᶜ`, then the Fourier multiplier `T_g` fixes `u`. -/
theorem fourierMultiplierCLM_eq_self_of_isVanishingOn {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {u : 𝓢'(E, F)} {s : Set E} (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s)
    (hgs : ∀ᶠ ξ in 𝓝ˢ sᶜ, g ξ = 1) : fourierMultiplierCLM F g u = u := by
  obtain ⟨U, hU, hsU, hgU⟩ := mem_nhdsSet_iff_exists.1 hgs
  have h : smulLeftCLM F g (𝓕 u) = 𝓕 u := by
    ext v
    rw [smulLeftCLM_apply_apply, ← sub_eq_zero, ← map_sub]
    -- The test function `g • v - v` vanishes on `U`, so its support lies in `Uᶜ ⊆ s`.
    refine hu _ ((closure_minimal (Function.support_subset_iff'.2 fun x hxU ↦ ?_)
      hU.isClosed_compl).trans (compl_subset_comm.1 hsU))
    have hx : g x = 1 := hgU (not_not.1 hxU)
    simp [SchwartzMap.smulLeftCLM_apply_apply hg, hx]
  rw [fourierMultiplierCLM_apply, h, FourierTransform.fourierInv_fourier_eq]

/-- The Fourier transform of `T_g u` vanishes off the support of the symbol `g`. -/
theorem isVanishingOn_fourier_fourierMultiplierCLM {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (fourierMultiplierCLM F g u) : 𝓢'(E, F)) (tsupport g)ᶜ := by
  intro v hv
  rw [fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq, smulLeftCLM_apply_apply]
  convert map_zero (𝓕 u)
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  by_cases hx : x ∈ tsupport g
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hv h hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Differentiation preserves the vanishing of the Fourier transform on a set. -/
theorem isVanishingOn_fourier_lineDerivOp {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) (m : E) :
    IsVanishingOn (𝓕 (∂_{m} u) : 𝓢'(E, F)) s := by
  intro v hv
  rw [fourier_lineDerivOp_eq, smul_apply,
    Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM hu (by fun_prop) v hv, smul_zero]

/-- Iterated differentiation preserves the vanishing of the Fourier transform on a set. -/
theorem isVanishingOn_fourier_iteratedLineDerivOp {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) {n : ℕ} (m : Fin n → E) :
    IsVanishingOn (𝓕 (∂^{m} u) : 𝓢'(E, F)) s := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left]
    exact isVanishingOn_fourier_lineDerivOp (ih _) _

end TemperedDistribution
