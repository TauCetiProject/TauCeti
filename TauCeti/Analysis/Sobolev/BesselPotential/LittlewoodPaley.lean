/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.L2Multiplier
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The `L²` Littlewood–Paley characterization of `H^s`

Let `E` be a finite-dimensional real inner product space, `F` a complex Hilbert space and `Δⱼ` the
inhomogeneous Littlewood–Paley blocks built from a bump function `φ`
(`TemperedDistribution.littlewoodPaleyBlock`). This file proves that the Besov space
`B^s_{2,2}` is the Bessel-potential space `H^s = H^{s,2}` of Mathlib, with equivalent norms:
a tempered distribution `u` lies in `H^s` exactly when its blocks `Δⱼ u` are `L²` functions with

`∑ⱼ 2^{2js} ‖Δⱼ u‖₂² < ∞`,

and this sum is comparable to `‖u‖_{H^s}²` with constants depending only on `s` and `φ`.

## The argument

Write `J^s` for the Bessel potential, the Fourier multiplier with symbol `⟨ξ⟩^s`,
`⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}`, and `f = J^s u ∈ L²` for `u ∈ H^s`. Then `Δₖ u` is the `L²` Fourier
multiplier with the bounded symbol `ψₖ ⟨ξ⟩^{-s}` applied to `f`, so by Plancherel's theorem

`∑ₖ 2^{2ks} ‖Δₖ u‖₂² = ∫ W(ξ) ‖𝓕 f (ξ)‖² dξ`, `W(ξ) = ∑ₖ 2^{2ks} ⟨ξ⟩^{-2s} ψₖ(ξ)²`.

On the support of `ψₖ` the weight `⟨ξ⟩` is comparable to `2^k`, and the sum of squares of the
partition is bounded above and below (`ContDiffBump.exists_sum_sq_inhomogeneousLittlewoodPaley_le`
and `ContDiffBump.exists_one_le_mul_sum_sq_inhomogeneousLittlewoodPaley`), so `W` is bounded above
and below by positive constants. This gives `H^s ⊆ B^s_{2,2}` with both norm inequalities on
`H^s`.

Conversely, for `u ∈ B^s_{2,2}` each block is an `L²` function with compact Fourier support, hence
lies in `H^s`, and so do the partial sums `uₙ = ∑_{j < n} Δⱼ u`. The blocks of `uₙ - uₘ` are
images of the blocks of `u` under a Fourier multiplier bounded by `2`, and vanish far below `m`,
so the lower norm inequality makes `(uₙ)` a Cauchy sequence in `H^s`. Its limit is `u`, the limit of
the partial sums in `𝓢'(E, F)` (`TemperedDistribution.tendsto_sum_littlewoodPaleyBlock`).

## Main declarations

* `TemperedDistribution.memBesov_two_two_iff_memSobolev`: `u ∈ B^s_{2,2}` if and only if
  `u ∈ H^s`.
* `BesselPotentialSpace.besovSpaceEquiv`: the isomorphism of normed spaces
  `H^s(E, F) ≃L[ℂ] B^s_{2,2}`, which keeps the underlying tempered distribution
  (`BesselPotentialSpace.toDistr_besovSpaceEquiv`,
  `BesselPotentialSpace.toDistr_besovSpaceEquiv_symm`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E)) {s : ℝ}

/-- The symbol `ψₖ(ξ) (1 + ‖ξ‖²)^{-s/2}` of `Δₖ J^{-s}`. -/
private def blockSymbol (s : ℝ) (k : ℕ) (ξ : E) : ℂ :=
  ((φ.inhomogeneousLittlewoodPaley k ξ * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)

omit [MeasurableSpace E] [BorelSpace E] in
private lemma hasTemperateGrowth_blockSymbol (s : ℝ) (k : ℕ) :
    (blockSymbol φ s k).HasTemperateGrowth := by
  have := φ.hasTemperateGrowth_inhomogeneousLittlewoodPaley k
  unfold blockSymbol
  fun_prop

private lemma memLp_blockSymbol (s : ℝ) (k : ℕ) : MemLp (blockSymbol φ s k) ∞ volume := by
  have hc : Continuous (blockSymbol φ s k) :=
    (hasTemperateGrowth_blockSymbol φ s k).1.continuous
  have hcs : HasCompactSupport (blockSymbol φ s k) :=
    (φ.hasCompactSupport_inhomogeneousLittlewoodPaley k).mul_right.comp_left Complex.ofReal_zero
  exact hc.memLp_top_of_hasCompactSupport hcs volume

/-- If `J^s u = f ∈ L²`, then the block `Δₖ u` is the `L²` Fourier multiplier with symbol
`ψₖ ⟨ξ⟩^{-s}` applied to `f`. -/
private lemma littlewoodPaleyBlock_eq_of_besselPotential_eq {u : 𝓢'(E, F)}
    {f : Lp F 2 (volume : Measure E)} (hu : besselPotential E F s u = f) (k : ℕ) :
    littlewoodPaleyBlock F φ k u =
      (Lp.fourierMultiplierCLM F ((memLp_blockSymbol φ s k).toLp _) f : 𝓢'(E, F)) := by
  have hu' : besselPotential E F (-s) (f : 𝓢'(E, F)) = u :=
    (besselPotential_neg_apply_eq_iff s _ _).2 hu
  rw [← Lp.fourierMultiplierCLM_toTemperedDistribution_eq f (hasTemperateGrowth_blockSymbol φ s k),
    ← hu', besselPotential, littlewoodPaleyBlock_apply,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop)
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k)]
  congr 2
  funext ξ
  simp [blockSymbol, mul_comm]

/-- Plancherel's theorem for the block multipliers. -/
private lemma enorm_fourierMultiplierCLM_blockSymbol_sq (s : ℝ) (k : ℕ)
    (f : Lp F 2 (volume : Measure E)) :
    ‖Lp.fourierMultiplierCLM F ((memLp_blockSymbol φ s k).toLp _) f‖ₑ ^ 2 =
      ∫⁻ ξ, ‖blockSymbol φ s k ξ‖ₑ ^ 2 * ‖𝓕 f ξ‖ₑ ^ 2 := by
  have h : ‖Lp.fourierMultiplierCLM F ((memLp_blockSymbol φ s k).toLp _) f‖ =
      ‖((memLp_blockSymbol φ s k).toLp _ • 𝓕 f : Lp F 2 (volume : Measure E))‖ := by
    rw [← Lp.norm_fourier_eq, Lp.fourier_fourierMultiplierCLM]
  rw [← ofReal_norm, h, ofReal_norm, L2.enorm_sq_eq_lintegral]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_lpSMul (r := 2) ((memLp_blockSymbol φ s k).toLp _) (𝓕 f),
    (memLp_blockSymbol φ s k).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.smul_apply', h₂, enorm_smul, mul_pow]

omit [MeasurableSpace E] [BorelSpace E] in
/-- On the support of `ψₖ`, the weight `2^{2ks} ⟨ξ⟩^{-2s}` is bounded above and below
independently of `k`. -/
private lemma exists_weight_bounds (s : ℝ) : ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ (k : ℕ) (ξ : E),
    a * φ.inhomogeneousLittlewoodPaley k ξ ^ 2 ≤ (2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2 ∧
      (2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2 ≤ b * φ.inhomogeneousLittlewoodPaley k ξ ^ 2 := by
  obtain ⟨c₁, hc₁, h₁⟩ :=
    φ.exists_one_add_norm_sq_rpow_le_of_mem_tsupport_inhomogeneousLittlewoodPaley (-(2 * s))
  obtain ⟨c₂, -, h₂⟩ :=
    φ.exists_one_add_norm_sq_rpow_le_of_mem_tsupport_inhomogeneousLittlewoodPaley (2 * s)
  refine ⟨(max c₂ 1)⁻¹, c₁, by positivity, hc₁, fun k ξ ↦ ?_⟩
  by_cases hψ : φ.inhomogeneousLittlewoodPaley k ξ = 0
  · simp [blockSymbol, hψ]
  have hξ := subset_tsupport _ hψ
  have hX : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hy : (0 : ℝ) < 2 ^ k := by positivity
  -- The weighted value is `y^{2s} X^{-s} ψₖ(ξ)²` with `X = 1 + ‖ξ‖²` and `y = 2^k`.
  have hkey : (2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2 =
      ((2 : ℝ) ^ k) ^ (2 * s) * (1 + ‖ξ‖ ^ 2) ^ (-s) * φ.inhomogeneousLittlewoodPaley k ξ ^ 2 := by
    rw [blockSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hX _), mul_comm s, Real.rpow_natCast_mul zero_le_two,
      mul_pow, mul_pow, ← Real.rpow_mul_natCast hy.le, ← Real.rpow_mul_natCast hX.le, sq_abs]
    push_cast
    ring_nf
  have hy2 : 0 < ((2 : ℝ) ^ k) ^ (2 * s) := Real.rpow_pos_of_pos hy _
  rw [hkey]
  constructor
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h₂' := h₂ k ξ hξ
    rw [show 2 * s / 2 = s by ring] at h₂'
    rw [Real.rpow_neg hX.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hX _),
      inv_mul_le_iff₀ (by positivity)]
    exact h₂'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy2.le)
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h₁' := h₁ k ξ hξ
    rw [show -(2 * s) / 2 = -s by ring] at h₁'
    calc ((2 : ℝ) ^ k) ^ (2 * s) * (1 + ‖ξ‖ ^ 2) ^ (-s)
        ≤ ((2 : ℝ) ^ k) ^ (2 * s) * (c₁ * ((2 : ℝ) ^ k) ^ (-(2 * s))) :=
          mul_le_mul_of_nonneg_left h₁' hy2.le
      _ = c₁ := by
        rw [mul_left_comm, ← Real.rpow_add hy, add_neg_cancel, Real.rpow_zero, mul_one]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The total weight `W(ξ) = ∑ₖ 2^{2ks} ⟨ξ⟩^{-2s} ψₖ(ξ)²` is bounded above and below by positive
constants. -/
private lemma exists_tsum_weight_bounds (s : ℝ) : ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ ξ : E,
    ENNReal.ofReal a ≤ ∑' k : ℕ, ENNReal.ofReal ((2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2) ∧
      ∑' k : ℕ, ENNReal.ofReal ((2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2) ≤ ENNReal.ofReal b := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_weight_bounds φ s
  obtain ⟨L, hL⟩ := φ.exists_sum_sq_inhomogeneousLittlewoodPaley_le
  obtain ⟨L', hL'⟩ := φ.exists_one_le_mul_sum_sq_inhomogeneousLittlewoodPaley
  have hL'0 : (0 : ℝ) < L' := by
    obtain ⟨N, hN⟩ := hL' 0
    refine lt_of_le_of_ne (Nat.cast_nonneg _) fun h ↦ ?_
    rw [← h, zero_mul] at hN
    exact absurd hN (by norm_num)
  refine ⟨a / L', b * L, by positivity, by positivity, fun ξ ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨N, hN⟩ := hL' ξ
    calc ENNReal.ofReal (a / L')
        ≤ ENNReal.ofReal (a * ∑ k ∈ Finset.range N, φ.inhomogeneousLittlewoodPaley k ξ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_left ?_ ha.le
          rw [inv_le_iff_one_le_mul₀' hL'0]
          exact hN
      _ = ∑ k ∈ Finset.range N,
            ENNReal.ofReal (a * φ.inhomogeneousLittlewoodPaley k ξ ^ 2) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ ↦ by positivity]
      _ ≤ ∑ k ∈ Finset.range N,
            ENNReal.ofReal ((2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2) :=
          Finset.sum_le_sum fun k _ ↦ ENNReal.ofReal_le_ofReal (hab k ξ).1
      _ ≤ _ := sum_le_tsum _
  · refine ENNReal.tsum_le_of_sum_range_le fun N ↦ ?_
    calc ∑ k ∈ Finset.range N, ENNReal.ofReal ((2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2)
        ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal (b * φ.inhomogeneousLittlewoodPaley k ξ ^ 2) :=
          Finset.sum_le_sum fun k _ ↦ ENNReal.ofReal_le_ofReal (hab k ξ).2
      _ = ENNReal.ofReal (b * ∑ k ∈ Finset.range N, φ.inhomogeneousLittlewoodPaley k ξ ^ 2) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ ↦ by positivity]
      _ ≤ ENNReal.ofReal (b * L) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hL _ ξ) hb)

/-- **The `L²` Littlewood–Paley inequalities**, in `ℝ≥0∞`: if `J^s u = f ∈ L²`, then the blocks
`Δₖ u` are `L²` functions `gₖ` with `a ‖f‖² ≤ ∑ₖ (2^{ks} ‖gₖ‖)² ≤ b ‖f‖²`. -/
private lemma exists_enorm_bounds (s : ℝ) : ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ {u : 𝓢'(E, F)}
    {f : Lp F 2 (volume : Measure E)}, besselPotential E F s u = f →
      ∃ g : ℕ → Lp F 2 (volume : Measure E), (∀ k, littlewoodPaleyBlock F φ k u = g k) ∧
        ENNReal.ofReal a * ‖f‖ₑ ^ 2 ≤ ∑' k : ℕ, ENNReal.ofReal ((2 ^ (s * k) * ‖g k‖) ^ 2) ∧
        ∑' k : ℕ, ENNReal.ofReal ((2 ^ (s * k) * ‖g k‖) ^ 2) ≤ ENNReal.ofReal b * ‖f‖ₑ ^ 2 := by
  obtain ⟨a, b, ha, hb, hW⟩ := exists_tsum_weight_bounds φ s
  refine ⟨a, b, ha, hb, fun {u f} hu ↦ ⟨fun k ↦ Lp.fourierMultiplierCLM F
    ((memLp_blockSymbol φ s k).toLp _) f, littlewoodPaleyBlock_eq_of_besselPotential_eq φ hu, ?_⟩⟩
  have hterm : ∀ k : ℕ, ENNReal.ofReal ((2 ^ (s * k) *
      ‖Lp.fourierMultiplierCLM F ((memLp_blockSymbol φ s k).toLp _) f‖) ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal ((2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2) * ‖𝓕 f ξ‖ₑ ^ 2 := by
    intro k
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, enorm_fourierMultiplierCLM_blockSymbol_sq,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ξ ↦ ?_
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, mul_assoc]
  have hmeas : ∀ k : ℕ, AEMeasurable (fun ξ ↦
      ENNReal.ofReal ((2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2) * ‖𝓕 f ξ‖ₑ ^ 2) volume :=
    fun k ↦ (((continuous_const.mul (hasTemperateGrowth_blockSymbol φ s k).1.continuous.norm).pow
      2).measurable.ennreal_ofReal.aemeasurable).mul
      ((Lp.aestronglyMeasurable (𝓕 f)).enorm.pow_const 2)
  have hsum : ∑' k : ℕ, ENNReal.ofReal ((2 ^ (s * k) *
      ‖Lp.fourierMultiplierCLM F ((memLp_blockSymbol φ s k).toLp _) f‖) ^ 2) =
      ∫⁻ ξ, (∑' k : ℕ, ENNReal.ofReal ((2 ^ (s * k) * ‖blockSymbol φ s k ξ‖) ^ 2)) *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
    simp_rw [hterm, ← ENNReal.tsum_mul_right]
    exact (lintegral_tsum hmeas).symm
  have hf : ‖f‖ₑ ^ 2 = ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ 2 := by
    rw [← L2.enorm_sq_eq_lintegral, ← ofReal_norm, ← ofReal_norm (𝓕 f), Lp.norm_fourier_eq]
  rw [hsum, hf, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ⟨lintegral_mono fun ξ ↦ mul_le_mul_left (hW ξ).1 _,
    lintegral_mono fun ξ ↦ mul_le_mul_left (hW ξ).2 _⟩

/-- **The `L²` Littlewood–Paley inequalities.** There are constants `0 < a` and `0 ≤ b`, depending
only on `s` and `φ`, such that whenever `J^s u = f ∈ L²` and the blocks `Δₖ u` are the `L²`
functions `gₖ`, the sequence `(2^{ks} ‖gₖ‖)²` is summable with
`a ‖f‖² ≤ ∑ₖ (2^{ks} ‖gₖ‖)² ≤ b ‖f‖²`. -/
private lemma exists_bounds (s : ℝ) : ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ {u : 𝓢'(E, F)}
    {f : Lp F 2 (volume : Measure E)}, besselPotential E F s u = f →
      ∀ g : ℕ → Lp F 2 (volume : Measure E), (∀ k, littlewoodPaleyBlock F φ k u = g k) →
        Summable (fun k : ℕ ↦ (2 ^ (s * k) * ‖g k‖) ^ 2) ∧
        a * ‖f‖ ^ 2 ≤ ∑' k : ℕ, (2 ^ (s * k) * ‖g k‖) ^ 2 ∧
        ∑' k : ℕ, (2 ^ (s * k) * ‖g k‖) ^ 2 ≤ b * ‖f‖ ^ 2 := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_enorm_bounds (F := F) φ s
  refine ⟨a, b, ha, hb, fun {u f} hu g hg ↦ ?_⟩
  obtain ⟨g', hg', h₁, h₂⟩ := h hu
  obtain rfl : g' = g := funext fun k ↦
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot ((hg' k).symm.trans (hg k))
  have ht : ∀ k : ℕ, 0 ≤ (2 ^ (s * k) * ‖g' k‖) ^ 2 := fun k ↦ sq_nonneg _
  have hf2 : ‖f‖ₑ ^ 2 = ENNReal.ofReal (‖f‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hf2, ← ENNReal.ofReal_mul ha.le] at h₁
  rw [hf2, ← ENNReal.ofReal_mul hb] at h₂
  have hs : Summable fun k : ℕ ↦ (2 ^ (s * k) * ‖g' k‖) ^ 2 :=
    (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h₂)).congr
      fun k ↦ ENNReal.toReal_ofReal (ht k)
  rw [← ENNReal.ofReal_tsum_of_nonneg ht hs] at h₁ h₂
  exact ⟨hs, (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg ht)).1 h₁,
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h₂⟩

/-- `H^s ⊆ B^s_{2,2}`. -/
private lemma memBesov_of_memSobolev {u : 𝓢'(E, F)} (hu : u.MemSobolev s 2) :
    u.MemBesov φ s 2 2 := by
  obtain ⟨f, hf⟩ := hu
  obtain ⟨a, b, -, -, hab⟩ := exists_bounds (F := F) φ s
  have hg := littlewoodPaleyBlock_eq_of_besselPotential_eq φ hf
  exact memBesov_iff.2 ⟨_, hg, memℓp_two_iff_summable_sq.2 <| (hab hf _ hg).1.congr fun k ↦ by
    rw [Real.norm_of_nonneg (by positivity)]⟩

/-- The blocks of `∑_{j ∈ [m, n)} Δⱼ u` are the images of the blocks of `u` under the Fourier
multiplier with symbol `∑_{j ∈ [m, n)} ψⱼ`, which is bounded by `2`, and they vanish at indices
`k` with `k + L ≤ m`. -/
private lemma exists_littlewoodPaleyBlock_sum_Ico_eq :
    ∃ L : ℕ, ∀ {u : 𝓢'(E, F)} {f : ℕ → Lp F 2 (volume : Measure E)},
      (∀ j, littlewoodPaleyBlock F φ j u = f j) → ∀ {m n : ℕ}, m ≤ n →
        ∃ g : ℕ → Lp F 2 (volume : Measure E),
          (∀ k, littlewoodPaleyBlock F φ k (∑ j ∈ Finset.Ico m n, littlewoodPaleyBlock F φ j u) =
            g k) ∧ (∀ k, ‖g k‖ ≤ 2 * ‖f k‖) ∧ ∀ k, k + L ≤ m → g k = 0 := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ φ
  refine ⟨L, fun {u f} hf {m n} hmn ↦ ?_⟩
  -- The symbol of `∑_{j < N} Δⱼ` is `φ (2^{1-N} ·) ∈ [0, 1]`.
  have hpartial : ∀ (N : ℕ) (ξ : E),
      |∑ j ∈ Finset.range N, φ.inhomogeneousLittlewoodPaley j ξ| ≤ 1 := by
    intro N ξ
    rcases N with _ | N
    · simp
    · rw [φ.sum_inhomogeneousLittlewoodPaley_range, abs_of_nonneg φ.nonneg]
      exact φ.le_one
  set χ : E → ℂ := fun ξ ↦ ∑ j ∈ Finset.Ico m n, (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)
  have hχt : χ.HasTemperateGrowth :=
    Function.HasTemperateGrowth.sum fun j _ ↦
      φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j
  have hχb : ∀ ξ, ‖χ ξ‖ ≤ 2 := fun ξ ↦ by
    have hχξ : χ ξ = ((∑ j ∈ Finset.range n, φ.inhomogeneousLittlewoodPaley j ξ -
        ∑ j ∈ Finset.range m, φ.inhomogeneousLittlewoodPaley j ξ : ℝ) : ℂ) := by
      rw [← Finset.sum_Ico_eq_sub _ hmn, Complex.ofReal_sum]
    rw [hχξ, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_sub (∑ j ∈ Finset.range n, φ.inhomogeneousLittlewoodPaley j ξ)
      (∑ j ∈ Finset.range m, φ.inhomogeneousLittlewoodPaley j ξ), hpartial n ξ, hpartial m ξ]
  have hχL : MemLp χ ∞ volume :=
    memLp_top_of_bound hχt.1.continuous.aestronglyMeasurable 2 (Eventually.of_forall hχb)
  have hχn : ‖hχL.toLp χ‖ ≤ 2 := by
    rw [Lp.norm_toLp, eLpNorm_exponent_top]
    · exact ENNReal.toReal_le_of_le_ofReal zero_le_two
        (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hχb))
    · exact hχL.aestronglyMeasurable
  have hχsum : fourierMultiplierCLM F χ = ∑ j ∈ Finset.Ico m n, littlewoodPaleyBlock F φ j := by
    simp_rw [littlewoodPaleyBlock_eq_fourierMultiplierCLM]
    exact fourierMultiplierCLM_sum F (s := Finset.Ico m n) fun j _ ↦
      φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j
  refine ⟨fun k ↦ if k + L ≤ m then 0 else Lp.fourierMultiplierCLM F (hχL.toLp χ) (f k),
    fun k ↦ ?_, fun k ↦ ?_, fun k hk ↦ by simp [hk]⟩
  · rw [map_sum]
    dsimp only
    split_ifs with hk
    · rw [Lp.toTemperedDistribution_zero]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have h0 := (hL k j (hk.trans (Finset.mem_Ico.1 hj).1)).1
      simpa using DFunLike.congr_fun h0 u
    · rw [← Lp.fourierMultiplierCLM_toTemperedDistribution_eq (f k) hχt hχL, ← hf k,
        hχsum, sum_apply]
      exact Finset.sum_congr rfl fun j _ ↦ littlewoodPaleyBlock_comm φ k j u
  · dsimp only
    split_ifs
    · simp [mul_nonneg zero_le_two (norm_nonneg (f k))]
    · exact (Lp.norm_fourierMultiplierCLM_apply_le _ _).trans
        (mul_le_mul_of_nonneg_right hχn (norm_nonneg _))

/-- Every Littlewood–Paley block of a distribution in `B^s_{2,2}` lies in `H^s`: it is an `L²`
function whose Fourier transform is carried by the region where the enlarged cutoff `Ψⱼ` is `1`. -/
private lemma memSobolev_littlewoodPaleyBlock {u : 𝓢'(E, F)} {f : Lp F 2 (volume : Measure E)}
    {j : ℕ} (hf : littlewoodPaleyBlock F φ j u = f) (s : ℝ) :
    (littlewoodPaleyBlock F φ j u).MemSobolev s 2 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  have hΨ : (fun ξ ↦ (φ.enlargedLittlewoodPaley L j ξ : ℂ)).HasTemperateGrowth :=
    ((φ.hasCompactSupport_enlargedLittlewoodPaley L j).comp_left
      Complex.ofReal_zero).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp (φ.contDiff_enlargedLittlewoodPaley L j))
  rw [hf]
  refine memSobolev_of_fourierMultiplierCLM_eq (φ.contDiff_enlargedLittlewoodPaley L j)
    (φ.hasCompactSupport_enlargedLittlewoodPaley L j) ?_ s
  rw [← hf, littlewoodPaleyBlock_apply, fourierMultiplierCLM_fourierMultiplierCLM_apply
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) hΨ]
  congr 2
  funext ξ
  rw [Pi.mul_apply, ← Complex.ofReal_mul, mul_comm,
    φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL j ξ]

/-- `B^s_{2,2} ⊆ H^s`: the partial sums `∑_{j < n} Δⱼ u` lie in `H^s` and form a Cauchy sequence
there, whose limit is `u`. -/
private lemma memSobolev_of_memBesov {u : 𝓢'(E, F)} (hu : u.MemBesov φ s 2 2) :
    u.MemSobolev s 2 := by
  obtain ⟨a, b, ha, -, hab⟩ := exists_bounds (F := F) φ s
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_sum_Ico_eq (F := F) φ
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  set T : ℕ → ℝ := fun k ↦ (2 ^ (s * k) * ‖f k‖) ^ 2
  have hT : Summable T := (memℓp_two_iff_summable_sq.1 hmem).congr fun k ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
  have hU : ∀ n, (∑ j ∈ Finset.range n, littlewoodPaleyBlock F φ j u).MemSobolev s 2 :=
    fun n ↦ MemSobolev.sum fun j _ ↦ memSobolev_littlewoodPaleyBlock φ (hf j) s
  set v : ℕ → H^{s}(E, F) := fun n ↦ (hU n).toBesselPotentialSpace
  -- The `H^s` norm of `v n - v (m + L)` is controlled by the tail `∑_{k ≥ m} 2^{2ks} ‖Δₖ u‖²`.
  have hdiff : ∀ m n, m + L ≤ n → a * ‖v n - v (m + L)‖ ^ 2 ≤ 4 * ∑' k, T (k + m) := by
    intro m n hn
    obtain ⟨g, hg, hgf, hg0⟩ := hL hf hn
    have hD : (v n - v (m + L)).toDistr =
        ∑ j ∈ Finset.Ico (m + L) n, littlewoodPaleyBlock F φ j u := by
      simp only [v, BesselPotentialSpace.toDistr_sub, MemSobolev.toBesselPotentialSpace_toDistr]
      exact (Finset.sum_Ico_eq_sub _ hn).symm
    obtain ⟨hs, hlow, -⟩ := hab (v n - v (m + L)).bessel_toDistr_eq_toLp g (hD ▸ hg)
    have hle : ∀ k : ℕ, (2 ^ (s * k) * ‖g k‖) ^ 2 ≤ 4 * T k := fun k ↦ by
      have := mul_le_mul_of_nonneg_left (hgf k) (by positivity : (0 : ℝ) ≤ 2 ^ (s * k))
      calc (2 ^ (s * k) * ‖g k‖) ^ 2 ≤ (2 ^ (s * k) * (2 * ‖f k‖)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ = 4 * T k := by ring
    rw [← BesselPotentialSpace.norm_toLp_eq]
    refine hlow.trans ?_
    rw [← hs.sum_add_tsum_nat_add m, Finset.sum_eq_zero fun k hk ↦ by
      rw [hg0 k (by simp only [Finset.mem_range] at hk; omega), norm_zero, mul_zero,
        zero_pow two_ne_zero], zero_add, ← tsum_mul_left]
    exact ((summable_nat_add_iff m).2 hs).tsum_le_tsum (fun k ↦ hle (k + m))
      (((summable_nat_add_iff m).2 hT).mul_left 4)
  have hcauchy : CauchySeq v := by
    refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
    obtain ⟨m, hm⟩ := ((tendsto_sum_nat_add T).eventually
      (gt_mem_nhds (show (0 : ℝ) < a * ε ^ 2 / 4 by positivity))).exists
    refine ⟨m + L, fun n hn ↦ ?_⟩
    rw [dist_eq_norm]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    have h := hdiff m n hn
    nlinarith
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have huw : u = w.toDistr :=
    tendsto_nhds_unique (tendsto_sum_littlewoodPaleyBlock φ u) <|
      ((BesselPotentialSpace.continuous_toDistr.tendsto w).comp hw).congr fun n ↦
        MemSobolev.toBesselPotentialSpace_toDistr _
  exact huw ▸ w.memSobolev_toDistr

/-- **`B^s_{2,2} = H^s`.** A tempered distribution lies in the Besov space `B^s_{2,2}` built from
`φ` exactly when it lies in the Bessel-potential space `H^s = H^{s,2}`. -/
theorem memBesov_two_two_iff_memSobolev {u : 𝓢'(E, F)} :
    u.MemBesov φ s 2 2 ↔ u.MemSobolev s 2 :=
  ⟨memSobolev_of_memBesov φ, memBesov_of_memSobolev φ⟩

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution TauCeti

variable (φ : ContDiffBump (0 : E)) {s : ℝ}

/-- The identification of `H^s` with `B^s_{2,2}` as a linear equivalence keeping the tempered
distribution. -/
private def besovSpaceEquivₗ : H^{s}(E, F) ≃ₗ[ℂ] BesovSpace F φ s 2 2 where
  toFun u := ((memBesov_two_two_iff_memSobolev φ).2 u.memSobolev_toDistr).toBesovSpace
  invFun v := ((memBesov_two_two_iff_memSobolev φ).1 v.memBesov_toDistr).toBesselPotentialSpace
  map_add' u v := BesovSpace.ext (by simp)
  map_smul' c u := BesovSpace.ext (by simp)
  left_inv u := BesselPotentialSpace.ext (by simp)
  right_inv v := BesovSpace.ext (by simp)

private lemma toDistr_besovSpaceEquivₗ (u : H^{s}(E, F)) :
    (besovSpaceEquivₗ φ u).toDistr = u.toDistr := by
  simp [besovSpaceEquivₗ]

private lemma toDistr_besovSpaceEquivₗ_symm (v : BesovSpace F φ s 2 2) :
    ((besovSpaceEquivₗ φ).symm v).toDistr = v.toDistr := by
  simp [besovSpaceEquivₗ]

/-- **`H^s = B^s_{2,2}` as normed spaces.** The identity on tempered distributions is an
isomorphism of normed spaces between the Bessel-potential space `H^s = H^{s,2}` and the Besov space
`B^s_{2,2}` built from `φ`, so the two norms are equivalent, with constants depending only on `s`
and `φ`. -/
def besovSpaceEquiv : H^{s}(E, F) ≃L[ℂ] BesovSpace F φ s 2 2 where
  toLinearEquiv := besovSpaceEquivₗ φ
  continuous_toFun := by
    obtain ⟨a, b, -, hb, hab⟩ := exists_bounds (F := F) φ s
    refine AddMonoidHomClass.continuous_of_bound (besovSpaceEquivₗ φ) (√b) fun u ↦ ?_
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    have h := BesovSpace.norm_rpow_eq_tsum ENNReal.ofNat_ne_top (besovSpaceEquivₗ φ u)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [h, mul_pow, Real.sq_sqrt hb, ← norm_toLp_eq]
    exact (hab u.bessel_toDistr_eq_toLp _ fun k ↦ by
      rw [BesovSpace.coe_block, toDistr_besovSpaceEquivₗ]).2.2
  continuous_invFun := by
    obtain ⟨a, b, ha, -, hab⟩ := exists_bounds (F := F) φ s
    refine AddMonoidHomClass.continuous_of_bound (besovSpaceEquivₗ φ).symm (√a⁻¹) fun v ↦ ?_
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    have h := BesovSpace.norm_rpow_eq_tsum ENNReal.ofNat_ne_top v
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [mul_pow, Real.sq_sqrt (inv_nonneg.2 ha.le), h, ← norm_toLp_eq, inv_mul_eq_div,
      le_div_iff₀' ha]
    exact (hab ((besovSpaceEquivₗ φ).symm v).bessel_toDistr_eq_toLp v.block fun k ↦ by
      rw [BesovSpace.coe_block, toDistr_besovSpaceEquivₗ_symm]).2.1

/-- `besovSpaceEquiv` keeps the underlying tempered distribution. -/
@[simp]
theorem toDistr_besovSpaceEquiv (u : H^{s}(E, F)) : (besovSpaceEquiv φ u).toDistr = u.toDistr :=
  toDistr_besovSpaceEquivₗ φ u

/-- The inverse of `besovSpaceEquiv` keeps the underlying tempered distribution. -/
@[simp]
theorem toDistr_besovSpaceEquiv_symm (v : BesovSpace F φ s 2 2) :
    ((besovSpaceEquiv φ).symm v).toDistr = v.toDistr :=
  toDistr_besovSpaceEquivₗ_symm φ v

end BesselPotentialSpace
