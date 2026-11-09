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
`SchwartzMap.fourierMultiplierCLM_add`.

It also records how multipliers interact with the support of the Fourier transform, expressed
with Mathlib's `Distribution.IsVanishingOn`. A multiplier whose symbol equals `1` near the set off
which the Fourier transform of `u` vanishes fixes `u`; this is how a function with compact Fourier
support is reproduced by convolution with a Schwartz kernel. Differentiation, being the multiplier
with symbol `2πi ⟪ξ, v⟫`, does not enlarge the Fourier support.

## Main results

* `TemperedDistribution.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`: a multiplier whose symbol
  is `1` near the Fourier support of `u` fixes `u`.
* `TemperedDistribution.isVanishingOn_fourier_lineDerivOp`,
  `TemperedDistribution.isVanishingOn_fourier_iteratedLineDerivOp`: derivatives do not enlarge
  the Fourier support.
-/

public section

namespace TemperedDistribution

open Distribution Topology
open scoped SchwartzMap FourierTransform LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Fourier multipliers on tempered distributions are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

/-- **Fourier multipliers equal to one near the spectrum.** If the Fourier transform of `u`
vanishes off `s` and the symbol `g` equals `1` on a neighbourhood of `s`, then the Fourier
multiplier with symbol `g` fixes `u`. -/
theorem fourierMultiplierCLM_eq_self_of_isVanishingOn {u : 𝓢'(E, F)} {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {s : Set E} (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) sᶜ)
    (hgs : ∀ᶠ ξ in 𝓝ˢ s, g ξ = 1) :
    fourierMultiplierCLM F g u = u := by
  obtain ⟨U, hUo, hsU, hU⟩ := mem_nhdsSet_iff_exists.1 hgs
  have h : smulLeftCLM F g (𝓕 u) = 𝓕 u := by
    ext ψ
    rw [smulLeftCLM_apply_apply, ← sub_eq_zero, ← map_sub]
    refine hu _ ((closure_minimal ?_ hUo.isClosed_compl).trans (Set.compl_subset_compl.2 hsU))
    intro ξ hξ hξU
    simp [SchwartzMap.smulLeftCLM_apply_apply hg, show g ξ = 1 from hU hξU] at hξ
  rw [fourierMultiplierCLM_apply, h, FourierTransform.fourierInv_fourier_eq]

/-- Differentiating a tempered distribution does not enlarge the support of its Fourier
transform. -/
theorem isVanishingOn_fourier_lineDerivOp {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) (m : E) :
    IsVanishingOn (𝓕 (∂_{m} u) : 𝓢'(E, F)) s := by
  intro ψ hψ
  have hg : (fun ξ ↦ (inner ℝ ξ m : ℂ)).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq, smul_apply,
    Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM hu hg ψ hψ, smul_zero]

/-- Iterated differentiation of a tempered distribution does not enlarge the support of its
Fourier transform. -/
theorem isVanishingOn_fourier_iteratedLineDerivOp {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) {k : ℕ} (m : Fin k → E) :
    IsVanishingOn (𝓕 (∂^{m} u) : 𝓢'(E, F)) s := by
  induction k with
  | zero => rwa [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    exact isVanishingOn_fourier_lineDerivOp (ih _) _

end TemperedDistribution
