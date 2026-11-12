/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.SchwartzSpace.BesselPotential
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Bessel potentials on Littlewood–Paley blocks

The Bessel potential `J^s = 𝓕⁻ (1 + ‖ξ‖ ^ 2) ^ (s / 2) 𝓕` of order `s` acts on a function whose
Fourier transform lives at frequencies `‖ξ‖ ~ R` essentially as multiplication by `R ^ s`. This file
makes that precise at the level of convolution kernels, and deduces the localized estimates

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

* `TemperedDistribution.exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le`: the
  localized estimates themselves. A Fourier multiplier with Schwartz symbol `σ` is the convolution
  with `𝓕⁻ σ`, so Young's inequality bounds it on every `Lᵖ` by `‖𝓕⁻ σ‖₁`; applied to `Δⱼ u`, the
  factorization gives `‖J^s Δⱼ u‖_p ≤ C 2^{js} ‖Δⱼ u‖_p` whenever `Δⱼ u` is an `Lᵖ` function.

* `TemperedDistribution.exists_besselPotential_eq_and_norm_le_of_isVanishingOn`: the same estimate
  `‖J^s v‖_p ≤ C 2^{js} ‖v‖_p` for any `v ∈ Lᵖ` whose Fourier transform lives in a dyadic annulus
  `2^j a ≤ ‖ξ‖ ≤ 2^j b` (in the ball of radius `b` when `j = 0`). Such a `v` is the sum of
  boundedly many of its blocks, of index near `j`, so this follows from the block estimate.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Lemma 6.2.1.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.2.
-/

public section

open scoped FourierTransform SchwartzMap LineDeriv ContDiff ENNReal
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
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  choose B _ hB using fun k : ℕ ↦ φ.exists_norm_iteratedFDeriv_enlargedLittlewoodPaley_le L k
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

/-- **Bessel potentials of Littlewood–Paley blocks in `Lᵖ`.** There is a constant `C ≥ 0`,
depending only on `s` and `φ`, such that for every `1 ≤ p ≤ ∞` and every `j`: if the block
`Δⱼ u` of a tempered distribution `u` is an `Lᵖ` function `f`, then `J^s Δⱼ u` is an `Lᵖ`
function `g` with

`‖g‖_p ≤ C 2^{js} ‖f‖_p`. -/
theorem exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le [CompleteSpace F] (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (u : 𝓢'(E, F))
      (f : Lp F p (volume : Measure E)), littlewoodPaleyBlock F φ j u = f →
      ∃ g : Lp F p (volume : Measure E),
        besselPotential E F s (littlewoodPaleyBlock F φ j u) = g ∧
          ‖g‖ ≤ C * 2 ^ (s * j) * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_besselPotential_compL_littlewoodPaleyBlock_eq (F := F) φ s
  refine ⟨max C 0, le_max_right _ _, fun {p} _ j u f hf ↦ ?_⟩
  obtain ⟨σ, hσ, hσC⟩ := hC j
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ f
  refine ⟨g, ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_apply, hσ, ContinuousLinearMap.comp_apply, hf, hg]
  · have h2 : ((2 : ℝ) ^ j) ^ s = 2 ^ (s * j) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm]
    calc ‖g‖ ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * ‖f‖ := hgf
      _ ≤ max C 0 * 2 ^ (s * j) * ‖f‖ := by
        rw [← h2]
        gcongr
        exact hσC.trans (by gcongr; exact le_max_left _ _)

open Distribution in
/-- **Bessel potentials on a dyadic annulus.** For `t : ℝ`, `a > 0` and every `b` there is a
constant `C ≥ 0`, depending only on `t`, `a` and `b`, with the following property. Let
`1 ≤ p ≤ ∞` and let `v ∈ Lᵖ` have Fourier transform vanishing outside the closed ball of radius
`2^j b` and, when `j > 0`, on the open ball of radius `2^j a`. Then `J^t v` is an `Lᵖ` function
`g` with

`‖g‖_p ≤ C 2^{jt} ‖v‖_p`. -/
theorem exists_besselPotential_eq_and_norm_le_of_isVanishingOn [CompleteSpace F] (t : ℝ) {a : ℝ}
    (ha : 0 < a) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (v : Lp F p (volume : Measure E)),
      IsVanishingOn (𝓕 (v : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ j * b))ᶜ →
        (0 < j → IsVanishingOn (𝓕 (v : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 (2 ^ j * a))) →
          ∃ g : Lp F p (volume : Measure E),
            besselPotential E F t v = g ∧ ‖g‖ ≤ C * 2 ^ (t * j) * ‖v‖ := by
  -- Cut `v` into the blocks of any fixed bump function.
  let φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_annulus (F := F) φ ha b
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₁, hC₁, hJ⟩ := exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ t
  set K : ℝ := C₁ * 2 ^ (|t| * L) * max C₀ 0
  refine ⟨2 * L * K, by positivity, fun {p} _ j v hb ha' ↦ ?_⟩
  -- Only the blocks `Δₖ v` with `j - L ≤ k < j + L` survive, so `v` is their sum.
  have hv : ∑ k ∈ Finset.Ico (j - L) (j + L), littlewoodPaleyBlock F φ k (v : 𝓢'(E, F)) = v :=
    sum_littlewoodPaleyBlock_eq_self φ _ fun k hk ↦ hL j k _ hb ha' <| by
      rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
      omega
  choose f hf hfC using fun k ↦ hC₀ (p := p) k v
  choose g hg hgC using fun k ↦ hJ (p := p) k (v : 𝓢'(E, F)) (f k) (hf k)
  refine ⟨∑ k ∈ Finset.Ico (j - L) (j + L), g k, ?_, ?_⟩
  · rw [← hv, map_sum, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun k _ ↦ hg k
  -- Each surviving block costs `2^{kt} ≤ 2^{|t| L} 2^{jt}`, and there are at most `2 L` of them.
  have hgk (k : ℕ) (hk : k ∈ Finset.Ico (j - L) (j + L)) :
      ‖g k‖ ≤ K * 2 ^ (t * j) * ‖v‖ := by
    calc ‖g k‖ ≤ C₁ * 2 ^ (t * k) * ‖f k‖ := hgC k
      _ ≤ C₁ * (2 ^ (|t| * L) * 2 ^ (t * j)) * (max C₀ 0 * ‖v‖) := by
        gcongr
        · exact Real.rpow_mul_natCast_le_of_mem_Ico one_le_two t hk
        · exact (hfC k).trans (by gcongr; exact le_max_left C₀ 0)
      _ = K * 2 ^ (t * j) * ‖v‖ := by ring
  calc ‖∑ k ∈ Finset.Ico (j - L) (j + L), g k‖
      ≤ ∑ k ∈ Finset.Ico (j - L) (j + L), K * 2 ^ (t * j) * ‖v‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hgk)
    _ = (Finset.Ico (j - L) (j + L)).card * (K * 2 ^ (t * j) * ‖v‖) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * L * (K * 2 ^ (t * j) * ‖v‖) := by
        gcongr
        rw [Nat.card_Ico]
        exact_mod_cast (by omega)
    _ = 2 * L * K * 2 ^ (t * j) * ‖v‖ := by ring

end TemperedDistribution
