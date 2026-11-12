/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# The Besov regularity of the Dirac mass

Let `φ` be a smooth bump function on a real inner product space `E` of finite dimension `n`, with
inhomogeneous Littlewood–Paley partition `ψ₀ = φ, ψ₁, ψ₂, …` and blocks `Δⱼ`. The Fourier
transform of the Dirac mass `δ₀` is the constant `1`, so its blocks are the kernels themselves:
`Δⱼ δ₀ = 𝓕⁻ ψⱼ`, a Schwartz function. Since `ψ_{j+1} = ψ₁ (2^{-j} ·)`, the kernel `𝓕⁻ ψ_{j+1}` is
the `L¹`-normalised dilate `2^{jn} 𝓕⁻ ψ₁ (2^j ·)`, whose `Lᵖ` norm is `2^{jn/p'}` times that of
`𝓕⁻ ψ₁`, where `1/p + 1/p' = 1`. The weighted block norms `2^{js} ‖Δⱼ δ₀‖_p` therefore form, from
`j = 1` on, the geometric sequence `C 2^{j (s + n/p')}` with `C > 0` once `n ≥ 1`. This gives the
exact Besov regularity of `δ₀`: for every `1 ≤ p ≤ ∞` and `q ≠ 0`,

`δ₀ ∈ B^s_{p,q}` if and only if `s < -n/p'`, or `s = -n/p'` and `q = ∞`.

In particular `δ₀ ∈ B^{-n/p'}_{p,∞}`, and `δ₀` lies in the Hölder–Zygmund space `𝒞^{-n}`, the
case `p = ∞`. The exponent `-n/p'` is sharp, so the negative regularity of a point mass is not
`0`; at `p = 1` it is `0` only in the weakest space `B^0_{1,∞}`.

## Main declarations

* `TemperedDistribution.exists_littlewoodPaleyBlock_delta_eq`: `Δⱼ δ₀` is the `Lᵖ` function
  `𝓕⁻ ψⱼ`.
* `TemperedDistribution.memBesov_delta_iff`: the exact Besov regularity of `δ₀`.
* `TemperedDistribution.memBesov_delta`: `δ₀ ∈ B^{-n/p'}_{p,∞}`, in every dimension; at `p = ∞`
  this is `δ₀ ∈ 𝒞^{-n} = B^{-n}_{∞,∞}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Module
open scoped ENNReal SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E))

/-- **The blocks of the Dirac mass are the Littlewood–Paley kernels.** For every `1 ≤ p ≤ ∞`, the
block `Δⱼ δ₀` is the `Lᵖ` function `𝓕⁻ ψⱼ`, since the Fourier transform of `δ₀` is `1`. -/
theorem exists_littlewoodPaleyBlock_delta_eq (j : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ f : Lp ℂ p (volume : Measure E), littlewoodPaleyBlock ℂ φ j (delta 0) = f ∧
      f =ᵐ[volume] 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
  set σ := φ.inhomogeneousLittlewoodPaleySchwartz j
  have hσ : (σ : E → ℂ) = _ := φ.coe_inhomogeneousLittlewoodPaleySchwartz j
  refine ⟨(𝓕⁻ σ).toLp p, ?_, ?_⟩
  · rw [Lp.toTemperedDistribution_toLp_eq, ← fourierInv_toTemperedDistributionCLM_eq,
      littlewoodPaleyBlock_apply, fourierMultiplierCLM_apply, fourier_delta_zero]
    congr 1
    ext u
    simp [φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j, hσ, mul_comm]
  · filter_upwards [(𝓕⁻ σ).coeFn_toLp p] with x hx
    rw [hx, SchwartzMap.fourierInv_coe, hσ]

variable {φ}

/-- The weighted block norms of `δ₀` form, from `j = 1` on, a geometric sequence:
`2^{(j+1)s} ‖Δ_{j+1} δ₀‖_p = (2^s ‖Δ₁ δ₀‖_p) (2^{s + n/p'})^j`. -/
private theorem rpow_mul_norm_succ_eq {s : ℝ} {p : ℝ≥0∞}
    {f : ℕ → Lp ℂ p (volume : Measure E)}
    (hf : ∀ j, f j =ᵐ[volume] 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (j : ℕ) :
    (2 : ℝ) ^ (s * (j + 1 : ℕ)) * ‖f (j + 1)‖ =
      2 ^ s * ‖f 1‖ * (2 ^ (s + finrank ℝ E * (1 - p.toReal⁻¹))) ^ j := by
  set m : ℝ := finrank ℝ E * (1 - p.toReal⁻¹)
  -- The `Lᵖ` norm of the dilated kernel `𝓕⁻ ψ_{j+1}`.
  have hnorm : ‖f (j + 1)‖ = (2 : ℝ) ^ (m * j) * ‖f 1‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hf _), eLpNorm_congr_ae (hf 1),
      φ.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_succ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    congr 2
    rw [div_eq_mul_inv]
    ring
  rw [hnorm, ← Real.rpow_mul_natCast zero_le_two]
  calc (2 : ℝ) ^ (s * (j + 1 : ℕ)) * (2 ^ (m * j) * ‖f 1‖)
      = 2 ^ (s * (j + 1 : ℕ) + m * j) * ‖f 1‖ := by rw [Real.rpow_add two_pos]; ring
    _ = 2 ^ (s + (s + m) * j) * ‖f 1‖ := by push_cast; ring_nf
    _ = 2 ^ s * ‖f 1‖ * 2 ^ ((s + m) * j) := by rw [Real.rpow_add two_pos]; ring

variable (φ)

/-- **The exact Besov regularity of the Dirac mass.** On a real inner product space of dimension
`n ≥ 1`, for `1 ≤ p ≤ ∞` with conjugate exponent `p'` and `q ≠ 0`, the Dirac mass `δ₀` lies in the
Besov space `B^s_{p,q}` exactly when `s < -n/p'`, or `s = -n/p'` and `q = ∞`. Here
`n/p' = n (1 - 1/p)` with `1/∞ = 0`. -/
theorem memBesov_delta_iff [Nontrivial E] {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] (hq : q ≠ 0) :
    (delta (0 : E)).MemBesov φ s p q ↔
      s < -(finrank ℝ E * (1 - p.toReal⁻¹)) ∨ s = -(finrank ℝ E * (1 - p.toReal⁻¹)) ∧ q = ∞ := by
  choose f hf hfae using fun j ↦ exists_littlewoodPaleyBlock_delta_eq φ j p
  have hc : 0 < ‖f 1‖ := by
    refine ENNReal.toReal_pos ?_ (Lp.eLpNorm_ne_top _)
    rw [eLpNorm_congr_ae (hfae 1)]
    exact φ.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_one_ne_zero
      (zero_lt_one.trans_le Fact.out).ne'
  rw [memBesov_iff_memℓp hf, ← memℓp_comp_add_one_iff]
  simp_rw [rpow_mul_norm_succ_eq hfae]
  set m : ℝ := finrank ℝ E * (1 - p.toReal⁻¹)
  -- The ratio `2^{s + m}` of the geometric sequence is `< 1` or `= 1` according to the sign of
  -- `s + m`.
  have hlt : (2 : ℝ) ^ (s + m) < 1 ↔ s < -m := by
    rw [← Real.rpow_zero 2, Real.rpow_lt_rpow_left_iff one_lt_two, ← lt_neg_iff_add_neg]
  have heq : (2 : ℝ) ^ (s + m) = 1 ↔ s = -m := by
    rw [← Real.rpow_zero 2, Real.rpow_right_inj two_pos (by norm_num), ← eq_neg_iff_add_eq_zero]
  rw [memℓp_const_mul_pow_iff (by positivity) hq, Real.norm_of_nonneg (by positivity), hlt, heq]

/-- **The Dirac mass lies in `B^{-n/p'}_{p,∞}`.** On a real inner product space of dimension `n`,
for `1 ≤ p ≤ ∞` with conjugate exponent `p'`, the Dirac mass lies in `B^{-n/p'}_{p,∞}`, where
`n/p' = n (1 - 1/p)` with `1/∞ = 0`. For `p = ∞` this is `δ₀ ∈ 𝒞^{-n} = B^{-n}_{∞,∞}`. -/
theorem memBesov_delta (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (delta (0 : E)).MemBesov φ (-(finrank ℝ E * (1 - p.toReal⁻¹))) p ∞ := by
  choose f hf hfae using fun j ↦ exists_littlewoodPaleyBlock_delta_eq φ j p
  rw [memBesov_iff_memℓp hf, ← memℓp_comp_add_one_iff]
  simp_rw [rpow_mul_norm_succ_eq hfae, neg_add_cancel, Real.rpow_zero, one_pow, mul_one]
  exact memℓp_infty (by rw [Set.range_const]; exact bddAbove_singleton)

end TemperedDistribution
