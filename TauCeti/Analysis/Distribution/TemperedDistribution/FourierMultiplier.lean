/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Fourier multipliers on tempered distributions

Mathlib's Fourier multiplier `TemperedDistribution.fourierMultiplierCLM F g` on tempered
distributions conjugates multiplication by a temperate-growth symbol `g` with the Fourier
transform. This file records that it is additive in the symbol, the tempered analogue of
`SchwartzMap.fourierMultiplierCLM_add`.

It also records how multipliers interact with frequency localization. A tempered distribution
`u` is localized in frequency to the complement of a set `s` when its Fourier transform vanishes
on `s` (`Distribution.IsVanishingOn (𝓕 u) s`). Every multiplier whose symbol vanishes on `s`
produces such a distribution. A multiplier whose symbol equals one away from a closed subset of
`s` fixes `u`, one whose symbol is supported in `s` annihilates `u`, and directional derivatives,
which are the multipliers with symbols `2πi ⟪ξ, m⟫`, preserve the localization. This is how
band-limited functions are reproduced by a multiplier with a smooth compactly supported symbol,
the starting point of Bernstein's inequalities.

## Main results

* `TemperedDistribution.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `TemperedDistribution.fourierMultiplierCLM_apply_apply_transpose`: the transpose of a multiplier
  is the multiplier on Schwartz functions with the reflected symbol, `(T_g u) f = u (T_{g(-·)} f)`.
* `TemperedDistribution.fourierMultiplierCLM_apply_apply_of_even`: a multiplier with an even
  symbol is the transpose of the multiplier on Schwartz functions, `(T_g u) f = u (T_g f)`.
* `TemperedDistribution.lineDerivOp_fourierMultiplierCLM`,
  `TemperedDistribution.iteratedLineDerivOp_fourierMultiplierCLM`: directional derivatives and
  their iterates commute with Fourier multipliers.
* `TemperedDistribution.fourierMultiplierCLM_fourierInv_delta`: a Fourier multiplier with symbol
  `g` acts on the plane wave `𝓕⁻ δ_ξ` as multiplication by `g(ξ)`.
* `TemperedDistribution.fourierMultiplierCLM_eq_zero_of_not_hasTemperateGrowth`: the multiplier of
  a symbol without temperate growth is the junk value `0`.
* `TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`: a multiplier whose symbol
  is one outside the set where `𝓕 u` vanishes fixes `u`.
* `TemperedDistribution.fourierMultiplierCLM_eq_zero_of_isVanishingOn`: a multiplier whose symbol
  is supported in the set where `𝓕 u` vanishes annihilates `u`.
* `TemperedDistribution.isVanishingOn_fourier_fourierMultiplierCLM`: the Fourier transform of a
  multiplier vanishes wherever its symbol does.
* `TemperedDistribution.isVanishingOn_fourier_lineDerivOp`,
  `TemperedDistribution.isVanishingOn_fourier_iteratedLineDerivOp`,
  `TemperedDistribution.isVanishingOn_fourier_laplacian`: derivatives and the Laplacian preserve
  the vanishing of the Fourier transform.
-/

public section

namespace TemperedDistribution

open Distribution
open scoped SchwartzMap FourierTransform LineDeriv Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Fourier multiplier of a symbol without temperate growth is the junk value `0`, because
`TemperedDistribution.smulLeftCLM` is `0` for such a symbol. -/
@[simp]
theorem fourierMultiplierCLM_eq_zero_of_not_hasTemperateGrowth {g : E → ℂ}
    (hg : ¬ g.HasTemperateGrowth) : fourierMultiplierCLM F g = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMultiplierCLM_apply, smulLeftCLM_eq_zero_of_not_hasTemperateGrowth hg, zero_apply,
    FourierTransform.fourierInv_zero, zero_apply]

/-- **The transpose of a Fourier multiplier.** The Fourier multiplier `T_g` on tempered
distributions is the transpose of the multiplier on Schwartz functions with the reflected symbol:
`(T_g u) f = u (T_{g(-·)} f)`. Multiplying `𝓕⁻ f`, the reflection of `𝓕 f`, by `g` gives the
reflection of `g(-·) • 𝓕 f`, and the Fourier transform of a reflection is the inverse Fourier
transform. Without temperate growth of `g`, neither does `g(-·)` have it, and both sides vanish. -/
theorem fourierMultiplierCLM_apply_apply_transpose (g : E → ℂ) (u : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F g u f = u (SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ g (-ξ)) f) := by
  by_cases hgt : g.HasTemperateGrowth
  · rw [fourierMultiplierCLM_apply_apply, SchwartzMap.fourier_smulLeftCLM_fourierInv_eq hgt]
  have hgt' : ¬ (fun ξ ↦ g (-ξ)).HasTemperateGrowth := fun h ↦ hgt <| by
    simpa [Function.comp_def] using h.comp (by fun_prop : (fun ξ : E ↦ -ξ).HasTemperateGrowth)
  simp [hgt, hgt', SchwartzMap.fourierMultiplierCLM_apply]

/-- **Multipliers with even symbols are symmetric.** If the symbol `g` is even, the Fourier
multiplier `T_g` on tempered distributions is the transpose of the one on Schwartz functions:
`(T_g u) f = u (T_g f)`. -/
theorem fourierMultiplierCLM_apply_apply_of_even {g : E → ℂ} (hg : g.Even) (u : 𝓢'(E, F))
    (f : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F g u f = u (SchwartzMap.fourierMultiplierCLM ℂ g f) := by
  rw [fourierMultiplierCLM_apply_apply_transpose, show (fun ξ ↦ g (-ξ)) = g from funext hg]

/-- Fourier multipliers on tempered distributions are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

/-- A directional derivative, the Fourier multiplier with symbol `2πi ⟪ξ, m⟫`, commutes with every
Fourier multiplier of temperate growth. -/
theorem lineDerivOp_fourierMultiplierCLM {g : E → ℂ} (hg : g.HasTemperateGrowth) (m : E)
    (u : 𝓢'(E, F)) : ∂_{m} (fourierMultiplierCLM F g u) = fourierMultiplierCLM F g (∂_{m} u) := by
  have hinner : (fun ξ : E ↦ ((inner ℝ ξ m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [lineDeriv_eq_fourierMultiplierCLM, lineDeriv_eq_fourierMultiplierCLM, map_smul,
    fourierMultiplierCLM_fourierMultiplierCLM_apply hg hinner,
    fourierMultiplierCLM_fourierMultiplierCLM_apply hinner hg, mul_comm g]

/-- Iterated directional derivatives commute with Fourier multipliers of temperate growth. -/
theorem iteratedLineDerivOp_fourierMultiplierCLM {g : E → ℂ} (hg : g.HasTemperateGrowth) {k : ℕ}
    (m : Fin k → E) (u : 𝓢'(E, F)) :
    ∂^{m} (fourierMultiplierCLM F g u) = fourierMultiplierCLM F g (∂^{m} u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, ih, lineDerivOp_fourierMultiplierCLM hg,
      LineDeriv.iteratedLineDerivOp_succ_left]

omit [NormedAddCommGroup F] [NormedSpace ℂ F] in
/-- **Fourier multipliers act on plane waves by their symbol.** The Fourier multiplier with symbol
`g` of temperate growth multiplies the plane wave `𝓕⁻ δ_ξ` by `g ξ`. -/
theorem fourierMultiplierCLM_fourierInv_delta {g : E → ℂ} (hg : g.HasTemperateGrowth) (ξ : E) :
    fourierMultiplierCLM ℂ g (𝓕⁻ (delta ξ)) = g ξ • 𝓕⁻ (delta ξ) := by
  rw [fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq, smulLeftCLM_delta hg,
    FourierTransform.fourierInv_smul]

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

/-- **The Laplacian does not enlarge the spectrum.** If the Fourier transform of `u` vanishes on
`s`, so does that of `Δ u`. -/
theorem isVanishingOn_fourier_laplacian {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) :
    IsVanishingOn (𝓕 (Δ u : 𝓢'(E, F)) : 𝓢'(E, F)) s := by
  intro ψ hψ
  rw [laplacian_eq_sum (stdOrthonormalBasis ℝ E), fourier_apply, sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← fourier_apply]
  exact isVanishingOn_fourier_lineDerivOp (isVanishingOn_fourier_lineDerivOp hu _) _ ψ hψ

/-- **A multiplier localizes the spectrum to the support of its symbol.** If the symbol `g`
vanishes on `s`, then the Fourier transform of `fourierMultiplierCLM F g u` vanishes on `s`, for
every tempered distribution `u`. -/
theorem isVanishingOn_fourier_fourierMultiplierCLM {g : E → ℂ} {s : Set E}
    (hgs : ∀ ξ ∈ s, g ξ = 0) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (fourierMultiplierCLM F g u) : 𝓢'(E, F)) s := by
  intro ψ hψ
  have h : SchwartzMap.smulLeftCLM ℂ g ψ = 0 := by
    by_cases hg : g.HasTemperateGrowth
    · ext ξ
      rw [SchwartzMap.smulLeftCLM_apply_apply hg, _root_.zero_apply]
      by_cases hξ : ξ ∈ s
      · rw [hgs ξ hξ, zero_smul]
      · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hξ (hψ h), smul_zero]
    · simp [hg]
  rw [fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq, smulLeftCLM_apply_apply,
    h, map_zero]

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

/-- **A multiplier supported off the spectrum annihilates.** If the Fourier transform of a
tempered distribution `u` vanishes on `s` and the symbol `g` is supported in `s`
(`tsupport g ⊆ s`), then the Fourier multiplier with symbol `g` annihilates `u`. -/
theorem fourierMultiplierCLM_eq_zero_of_isVanishingOn {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) {g : E → ℂ} (hgs : tsupport g ⊆ s) :
    fourierMultiplierCLM F g u = 0 := by
  have h : smulLeftCLM F g (𝓕 u) = 0 := by
    ext ψ
    rw [smulLeftCLM_apply_apply, zero_apply]
    exact hu _ ((SchwartzMap.tsupport_smulLeftCLM_subset g ψ).trans
      (Set.inter_subset_right.trans hgs))
  rw [fourierMultiplierCLM_apply, h, FourierTransform.fourierInv_zero]

end TemperedDistribution
