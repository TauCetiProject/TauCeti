/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.SpecificLimits.DyadicSum

/-!
# Homogeneous Littlewood–Paley blocks under dyadic dilations

Let `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`, `j ∈ ℤ`, be the homogeneous Littlewood–Paley cutoffs
built from a bump function `φ` on a finite-dimensional real inner product space `V` of dimension
`n`, and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. The normalized dilation
`D_{2^k} f = 2^{-kn/2} f (2^{-k} ·)` of `L²` (`MeasureTheory.Measure.dilateLp`) shifts the blocks
by `k`,

`Pⱼ (D_{2^k} f) = D_{2^k} (P_{j+k} f)`

(`ContDiffBump.fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow`), since
`ψⱼ (2^{-k} ·) = ψ_{j+k}`. So the dyadic `ℓ¹` and `ℓ²` sums `∑ⱼ 2^{js} ‖Pⱼ f‖₂` and
`(∑ⱼ 2^{2js} ‖Pⱼ f‖₂²)^{1/2}`, the norms of `\dot B^s_{2,1}` and `\dot H^s`, are multiplied by
`2^{-ks}` (`ContDiffBump.tsum_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow`,
`ContDiffBump.tsum_sq_rpow_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow`). These
are the scaling laws that fix the regularity of homogeneous Strichartz estimates.
-/

public section

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace ContDiffBump

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (φ : ContDiffBump (0 : V))
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The homogeneous blocks under dyadic dilations.** Dilating by `2^k` shifts the homogeneous
Littlewood–Paley blocks by `k`: for the normalized dilation `D_r f = r ^ (-n/2) • f (r⁻¹ • ·)` of
`L²(V, F)`,

`Pⱼ (D_{2^k} f) = D_{2^k} (P_{j+k} f)`,

since `ψⱼ (2^{-k} ·) = ψ_{j+k}`. Each symbol enters as any element of `L^∞` almost everywhere equal
to `ψⱼ`. -/
theorem fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (j k : ℤ)
    (f : Lp F 2 (volume : Measure V)) :
    Lp.fourierMultiplierCLM F (m j) (Measure.dilateLp volume ℝ 2 _ (zpow_pos two_pos k) f) =
      Measure.dilateLp volume ℝ 2 _ (zpow_pos two_pos k)
        (Lp.fourierMultiplierCLM F (m (j + k)) f) := by
  have hsym : Measure.dilateLp volume ℝ ∞ _ (zpow_pos two_pos k) (m j) = m (j + k) := by
    refine Lp.ext ?_
    filter_upwards [Measure.coeFn_dilateLp_top_of_ae_eq (𝕜 := ℝ) (zpow_pos two_pos k) (hm j),
      hm (j + k)] with ξ h₁ h₂
    rw [h₁, h₂, φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply j,
      φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply (j + k), smul_smul, ← mul_inv,
      ← zpow_add₀ two_ne_zero]
  rw [Lp.fourierMultiplierCLM_dilateLp, hsym]

/-- Each weighted block `2^{js} ‖Pⱼ (D_{2^k} f)‖₂` is `2^{-ks}` times the weighted block
`2^{(j+k)s} ‖P_{j+k} f‖₂`. -/
private theorem ofReal_mul_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (s : ℝ) (j k : ℤ)
    (f : Lp F 2 (volume : Measure V)) :
    ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) *
        ‖Lp.fourierMultiplierCLM F (m j) (Measure.dilateLp volume ℝ 2 _ (zpow_pos two_pos k) f)‖ₑ =
      ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-s)) * (ENNReal.ofReal (((2 : ℝ) ^ (j + k)) ^ s) *
        ‖Lp.fourierMultiplierCLM F (m (j + k)) f‖ₑ) := by
  rw [φ.fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow hm, LinearIsometryEquiv.eNorm_map,
    TauCeti.ofReal_zpow_add_rpow two_pos, ← mul_assoc, ← mul_assoc,
    mul_right_comm _ _ (ENNReal.ofReal _),
    ← ENNReal.ofReal_mul (by positivity), Real.rpow_neg (by positivity),
    inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- **The dyadic `ℓ¹` sums under dyadic dilations.** For the normalized dilation `D_{2^k}` of
`L²(V, F)` and every `s ∈ ℝ`,

`∑ⱼ 2^{js} ‖Pⱼ (D_{2^k} f)‖₂ = 2^{-ks} ∑ⱼ 2^{js} ‖Pⱼ f‖₂`,

so the norm of the homogeneous Besov space `\dot B^s_{2,1}`, written through the blocks, is
homogeneous of degree `-s` under these dilations. Each symbol enters as any element of `L^∞` almost
everywhere equal to `ψⱼ`. -/
theorem tsum_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (s : ℝ) (k : ℤ)
    (f : Lp F 2 (volume : Measure V)) :
    ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) *
        ‖Lp.fourierMultiplierCLM F (m j) (Measure.dilateLp volume ℝ 2 _ (zpow_pos two_pos k) f)‖ₑ =
      ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-s)) *
        ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) * ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ := by
  simp_rw [φ.ofReal_mul_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow hm s _ k f]
  rw [ENNReal.tsum_mul_left]
  exact congrArg _ ((Equiv.addRight k).tsum_eq fun j ↦
    ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) * ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ)

/-- **The dyadic `ℓ²` sums under dyadic dilations.** For the normalized dilation `D_{2^k}` of
`L²(V, F)` and every `s ∈ ℝ`,

`(∑ⱼ 2^{2js} ‖Pⱼ (D_{2^k} f)‖₂²)^{1/2} = 2^{-ks} (∑ⱼ 2^{2js} ‖Pⱼ f‖₂²)^{1/2}`,

so the norm of the homogeneous Sobolev space `\dot H^s`, in its Littlewood–Paley form, is
homogeneous of degree `-s` under these dilations. Each symbol enters as any element of `L^∞` almost
everywhere equal to `ψⱼ`. -/
theorem tsum_sq_rpow_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (s : ℝ) (k : ℤ)
    (f : Lp F 2 (volume : Measure V)) :
    (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) *
        ‖Lp.fourierMultiplierCLM F (m j)
          (Measure.dilateLp volume ℝ 2 _ (zpow_pos two_pos k) f)‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-s)) * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) *
        ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  have hshift : ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ (j + k)) ^ s) ^ 2 *
        ‖Lp.fourierMultiplierCLM F (m (j + k)) f‖ₑ ^ 2 =
      ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) ^ 2 * ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ ^ 2 :=
    (Equiv.addRight k).tsum_eq fun j ↦
      ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) ^ 2 * ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ ^ 2
  simp_rw [φ.ofReal_mul_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow hm s _ k f,
    mul_pow]
  rw [ENNReal.tsum_mul_left, hshift, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end ContDiffBump
