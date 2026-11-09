/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.SchwartzSpace.BesselPotential
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution

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
factorization into the localized estimates above, which give the two block comparisons:

* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_two_rpow_mul_norm_le`: if
  `J^s u = g ∈ Lᵖ`, then every block `Δⱼ u` is an `Lᵖ` function with
  `2^{js} ‖Δⱼ u‖_p ≤ C ‖g‖_p`, since `Δⱼ u = J^{-s} Δⱼ g`.
* `TemperedDistribution.exists_besselPotential_eq_and_norm_le_tsum`: if the blocks `Δⱼ u` are
  `Lᵖ` functions with `Σⱼ 2^{js} ‖Δⱼ u‖_p < ∞`, then `J^s u` is an `Lᵖ` function of norm at most
  `C Σⱼ 2^{js} ‖Δⱼ u‖_p`, since the series `Σⱼ J^s Δⱼ u` converges absolutely in `Lᵖ` and sums to
  `J^s u` in `𝓢'`.

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

section Lp

open Filter Topology
open scoped ENNReal

variable [CompleteSpace F]

/-- **`H^{s,p} ⊆ B^s_{p,∞}`, quantitatively.** There is `C`, depending only on `φ` and `s`, such
that for every `1 ≤ p ≤ ∞`, if the Bessel potential `J^s u` is an `Lᵖ` function `g`, then every
block `Δⱼ u` is an `Lᵖ` function `h` with `2^{js} ‖h‖_p ≤ C ‖g‖_p`. -/
theorem exists_littlewoodPaleyBlock_eq_and_two_rpow_mul_norm_le (s : ℝ) :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) {u : 𝓢'(E, F)}
      (g : Lp F p (volume : Measure E)), besselPotential E F s u = g →
      ∃ h : Lp F p (volume : Measure E), littlewoodPaleyBlock F φ j u = h ∧
        (2 : ℝ) ^ (j * s) * ‖h‖ ≤ C * ‖g‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₁, hC₁⟩ := exists_besselPotential_compL_littlewoodPaleyBlock_eq (F := F) φ (-s)
  refine ⟨C₁ * C₀, fun {p} _ j u g hg ↦ ?_⟩
  obtain ⟨σ, hσ, hσn⟩ := hC₁ j
  obtain ⟨g', hg', hg'n⟩ := hC₀ j g
  obtain ⟨h, hh, hhn⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ g'
  refine ⟨h, ?_, ?_⟩
  · -- `Δⱼ u = Δⱼ J^{-s} g = J^{-s} Δⱼ g = T_σ Δⱼ g`.
    have hu : u = besselPotential E F (-s) g := by
      rw [← hg, besselPotential_besselPotential_apply, add_neg_cancel, besselPotential_zero,
        ContinuousLinearMap.id_apply]
    rw [hu, littlewoodPaleyBlock_besselPotential_comm, ← ContinuousLinearMap.comp_apply, hσ,
      ContinuousLinearMap.comp_apply, hg', hh]
  · have hK : (2 : ℝ) ^ (j * s) * ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖ ≤ C₁ := by
      calc (2 : ℝ) ^ (j * s) * ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖
          ≤ (2 : ℝ) ^ (j * s) * (C₁ * ((2 : ℝ) ^ j) ^ (-s)) := by gcongr
        _ = C₁ := by
          rw [← Real.rpow_natCast_mul zero_le_two, mul_left_comm, ← Real.rpow_add zero_lt_two,
            mul_neg, add_neg_cancel,
            Real.rpow_zero, mul_one]
    have hg'0 : 0 ≤ C₀ * ‖g‖ := (norm_nonneg _).trans hg'n
    calc (2 : ℝ) ^ (j * s) * ‖h‖
        ≤ (2 : ℝ) ^ (j * s) * ((∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * (C₀ * ‖g‖)) := by
          gcongr
          exact hhn.trans (mul_le_mul_of_nonneg_left hg'n (integral_nonneg fun _ ↦ norm_nonneg _))
      _ = ((2 : ℝ) ^ (j * s) * ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * (C₀ * ‖g‖) := by ring
      _ ≤ C₁ * (C₀ * ‖g‖) := by gcongr
      _ = C₁ * C₀ * ‖g‖ := by ring

/-- **`B^s_{p,1} ⊆ H^{s,p}`, quantitatively.** There is `C`, depending only on `φ` and `s`, such
that for every `1 ≤ p ≤ ∞`, if the blocks `Δⱼ u` are `Lᵖ` functions `gⱼ` with
`Σⱼ 2^{js} ‖gⱼ‖_p < ∞`, then the Bessel potential `J^s u` is an `Lᵖ` function `h` with
`‖h‖_p ≤ C Σⱼ 2^{js} ‖gⱼ‖_p`. -/
theorem exists_besselPotential_eq_and_norm_le_tsum (s : ℝ) :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)}
      (g : ℕ → Lp F p (volume : Measure E)), (∀ j, littlewoodPaleyBlock F φ j u = g j) →
      Summable (fun j : ℕ ↦ (2 : ℝ) ^ (j * s) * ‖g j‖) →
      ∃ h : Lp F p (volume : Measure E), besselPotential E F s u = h ∧
        ‖h‖ ≤ C * ∑' j : ℕ, (2 : ℝ) ^ (j * s) * ‖g j‖ := by
  obtain ⟨C, hC⟩ := exists_besselPotential_compL_littlewoodPaleyBlock_eq (F := F) φ s
  refine ⟨C, fun {p} _ u g hg hsum ↦ ?_⟩
  choose σ hσ hσn using hC
  -- The pieces `J^s Δⱼ u = T_{σⱼ} gⱼ` are `Lᵖ` functions with `‖J^s Δⱼ u‖_p ≤ C 2^{js} ‖gⱼ‖_p`.
  choose k hk hkn using fun j ↦ exists_fourierMultiplierCLM_eq_and_norm_le (σ j) (g j)
  have hkJ (j : ℕ) : besselPotential E F s (littlewoodPaleyBlock F φ j u) = k j := by
    rw [← ContinuousLinearMap.comp_apply, hσ, ContinuousLinearMap.comp_apply, hg, hk]
  have hkn' (j : ℕ) : ‖k j‖ ≤ C * ((2 : ℝ) ^ (j * s) * ‖g j‖) := by
    calc ‖k j‖ ≤ (∫ x, ‖𝓕⁻ (σ j : E → ℂ) x‖) * ‖g j‖ := hkn j
      _ ≤ C * ((2 : ℝ) ^ j) ^ s * ‖g j‖ := by gcongr; exact hσn j
      _ = C * ((2 : ℝ) ^ (j * s) * ‖g j‖) := by rw [← Real.rpow_natCast_mul zero_le_two, mul_assoc]
  -- The series `Σⱼ J^s Δⱼ u` converges absolutely in `Lᵖ`.
  have hksum : Summable fun j ↦ ‖k j‖ :=
    (hsum.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hkn'
  have hH := hksum.of_norm.hasSum
  refine ⟨∑' j, k j, ?_, ?_⟩
  · -- In `𝓢'` the same series sums to `J^s u`, since `u = Σⱼ Δⱼ u` there.
    have h₁ : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, (k j : 𝓢'(E, F))) atTop
        (𝓝 ((∑' j, k j : Lp F p (volume : Measure E)) : 𝓢'(E, F))) := by
      have := ((Lp.toTemperedDistributionCLM F volume p).hasSum hH).tendsto_sum_nat
      simpa only [Lp.toTemperedDistributionCLM_apply] using this
    have h₂ : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, (k j : 𝓢'(E, F))) atTop
        (𝓝 (besselPotential E F s u)) := by
      simp_rw [← hkJ, ← map_sum]
      exact ((besselPotential E F s).continuous.tendsto u).comp
        (tendsto_sum_littlewoodPaleyBlock φ u)
    exact tendsto_nhds_unique h₂ h₁
  · calc ‖∑' j, k j‖ ≤ ∑' j : ℕ, ‖k j‖ := norm_tsum_le_tsum_norm hksum
      _ ≤ ∑' j : ℕ, C * ((2 : ℝ) ^ (j * s) * ‖g j‖) :=
        hksum.tsum_le_tsum hkn' (hsum.mul_left C)
      _ = C * ∑' j : ℕ, (2 : ℝ) ^ (j * s) * ‖g j‖ := tsum_mul_left

end Lp

end TemperedDistribution
