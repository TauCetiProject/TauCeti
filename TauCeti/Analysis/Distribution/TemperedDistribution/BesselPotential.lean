/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.SchwartzSpace.BesselPotential

/-!
# Bessel potentials on Littlewood–Paley blocks

The Bessel potential `J^s = 𝓕⁻ (1 + ‖ξ‖ ^ 2) ^ (s / 2) 𝓕` of order `s` acts on a function whose
Fourier transform lives at frequencies `‖ξ‖ ~ R` essentially as multiplication by `R ^ s`. This file
makes that precise at the level of convolution kernels, which is what gives the localized estimates

`‖J^s Δⱼ u‖_p ≤ C 2^{js} ‖Δⱼ u‖_p`, `1 ≤ p ≤ ∞`,

for the inhomogeneous Littlewood–Paley blocks `Δⱼ` with a constant independent of `j` and `p`. These
estimates compare the Bessel-potential spaces `H^{s,p}` with the Besov spaces `B^s_{p,q}`, whose
norms are weighted sequence norms of the `‖Δⱼ u‖_p`.

* `TemperedDistribution.exists_besselPotential_compL_littlewoodPaleyBlock_eq`: there is `C` such
  that for every `j` the operator `J^s Δⱼ` factors as `T_{σⱼ} Δⱼ`, where `T_{σⱼ}` is the Fourier
  multiplier by a Schwartz symbol `σⱼ` whose kernel satisfies `‖𝓕⁻ σⱼ‖₁ ≤ C 2^{js}`. The symbol
  is `σⱼ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) Ψⱼ` for the enlarged cutoff `Ψⱼ`
  (`ContDiffBump.enlargedLittlewoodPaley`), which equals `1` on the support of the piece `ψⱼ`.
  The kernel bound is `TauCeti.exists_integral_norm_fourierInv_one_add_norm_sq_rpow_mul_le`
  applied at the scale `R = 2^j`: let `χ` be a smooth cutoff supported where
  `1 + ‖ξ‖ ^ 2 ≍ R ^ 2`, with `‖D^k χ‖ ≤ B_k R ^ (-k)`; then the kernel of the symbol
  `(1 + ‖ξ‖ ^ 2) ^ (s / 2) χ ξ` has `L¹` norm at most `C R ^ s`, with `C` independent of `R` and
  `χ`.

A Fourier multiplier with Schwartz symbol `σ` is the convolution with `𝓕⁻ σ`, so Young's
inequality bounds it on every `Lᵖ` by `‖𝓕⁻ σ‖₁`. Applying that bound to `Δⱼ u` turns the
factorization into the localized estimates above; the `Lᵖ` bound itself is not proved here.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Lemma 6.2.1.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.2.
-/

public section

open scoped FourierTransform SchwartzMap LineDeriv ContDiff
open FourierTransform MeasureTheory Metric Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

namespace TemperedDistribution

variable [NormedSpace ℂ F] (φ : ContDiffBump (0 : E))

/-- **Bessel potentials on Littlewood–Paley blocks.** There is a constant `C` such that for every
`j` the Bessel potential `J^s` of order `s`, applied after the Littlewood–Paley block `Δⱼ`, is the
Fourier multiplier by a Schwartz symbol `σⱼ` applied after `Δⱼ`, where the kernel of `σⱼ` satisfies

`∫ ‖𝓕⁻ σⱼ x‖ dx ≤ C 2^{js}`.

The symbol `σⱼ` is the Bessel weight `(1 + ‖ξ‖ ^ 2) ^ (s / 2)` cut off to the frequencies of `Δⱼ`
by the enlarged cutoff `Ψⱼ`, and the factorization `J^s Δⱼ = T_{σⱼ} Δⱼ` holds because
`Ψⱼ ψⱼ = ψⱼ`. -/
theorem exists_besselPotential_compL_littlewoodPaleyBlock_eq (s : ℝ) :
    ∃ C, ∀ j : ℕ, ∃ σ : 𝓢(E, ℂ),
      besselPotential E F s ∘L littlewoodPaleyBlock F φ j =
          fourierMultiplierCLM F σ ∘L littlewoodPaleyBlock F φ j ∧
        ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖ ≤ C * (2 ^ j) ^ s := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero
  choose B hB0 hB using fun k : ℕ ↦ φ.exists_norm_iteratedFDeriv_enlargedLittlewoodPaley_le L k
  obtain ⟨a, b, ha, hab⟩ := φ.exists_one_add_norm_sq_le_of_mem_tsupport_enlargedLittlewoodPaley L
  obtain ⟨C, hC⟩ := TauCeti.exists_integral_norm_fourierInv_one_add_norm_sq_rpow_mul_le (E := E)
    s (b := b) ha (N := finrank ℝ E + 1) (by omega) B
  refine ⟨C, fun j ↦ ?_⟩
  -- The symbol `σⱼ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) Ψⱼ ξ`.
  set χ : E → ℝ := φ.enlargedLittlewoodPaley L j
  have hχ : ContDiff ℝ ∞ χ := φ.contDiff_enlargedLittlewoodPaley L j
  have hσs : ContDiff ℝ ∞ (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun ξ ↦ by positivity).mul hχ)
  set σ : 𝓢(E, ℂ) := ((φ.hasCompactSupport_enlargedLittlewoodPaley L j).mul_left.comp_left
    Complex.ofReal_zero : HasCompactSupport _).toSchwartzMap hσs
  have hσ : ⇑σ = fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ : ℝ) : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  refine ⟨σ, ?_, ?_⟩
  · -- Both sides are Fourier multipliers; their symbols agree since `Ψⱼ ψⱼ = ψⱼ`.
    rw [besselPotential, littlewoodPaleyBlock_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_compL_fourierMultiplierCLM
        (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) (by fun_prop),
      fourierMultiplierCLM_compL_fourierMultiplierCLM
        (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) σ.hasTemperateGrowth]
    congr 1
    funext ξ
    have h := φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL j ξ
    have h' : φ.inhomogeneousLittlewoodPaley j ξ * (1 + ‖ξ‖ ^ 2) ^ (s / 2) =
        φ.inhomogeneousLittlewoodPaley j ξ * ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ) := by
      linear_combination (-(1 + ‖ξ‖ ^ 2) ^ (s / 2)) * h
    simp only [Pi.mul_apply, hσ]
    exact_mod_cast h'
  · rw [hσ]
    exact hC (2 ^ j) χ (by positivity) hχ (hab j) fun k _ ξ ↦ hB k j ξ

end TemperedDistribution
