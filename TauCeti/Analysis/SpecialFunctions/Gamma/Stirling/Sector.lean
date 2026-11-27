/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Envelope

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.SpecialFunctions.Integrals.Periodic.Bernoulli
import TauCeti.NumberTheory.ZetaValues

/-!
# Stieltjes' sharp sector bounds for Stirling's series

Combining the constant-sign remainder integral with the half-angle inequality
`cos (arg z / 2) * (‖z‖ + u) ≤ ‖u + z‖` compares the slit-plane remainder directly to its
real-axis value at `‖z‖`, giving Stieltjes' sharp sector bound
`‖r_n(z)‖ < ‖T_n(z)‖ / cos (arg z / 2) ^ (2 * n)`, its `n = 1` specialization in Ramaré's sector
form `‖r₁(z)‖ < 1 / (12 * sin (δ / 2) ^ 2 * ‖z‖)`, the sharp `1 / 12` derivative bounds for
`r₁^{(k)}(z)` on the slit plane and on closed sectors, and the resulting `1 / 12` sector bound for
`log ‖Γ s‖`.

## Main declarations

* `TauCeti.norm_iteratedDeriv_stirlingSeriesRemainder_le_real`: slit-plane derivative comparison
  against the positive real axis at `‖z‖`.
* `TauCeti.norm_stirlingSeriesRemainder_lt`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_lt`,
  `TauCeti.norm_stirlingRemainder_lt`,
  `TauCeti.norm_stirlingSeriesRemainder_lt_of_abs_arg_le`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le`,
  `TauCeti.norm_stirlingRemainder_lt_of_abs_arg_le`,
  `TauCeti.norm_stirlingRemainder_lt_of_re_nonneg`,
  `TauCeti.abs_log_norm_Gamma_sub_stirling_lt`: Stieltjes' sharp slit-plane, closed-sector,
  and closed right half-plane bounds and the `1 / 12` bound for `log ‖Γ s‖`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4, eq. (8.4.06).
* O. Ramaré, *Excursions in Multiplicative Number Theory*, §20.2.
* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444.
-/

public section

open Complex Real Filter Set Topology MeasureTheory
open scoped ContDiff Nat

namespace TauCeti

private theorem sin_half_pos_le_cos_half_arg {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : |z.arg| ≤ π - δ) :
    0 < Real.sin (δ / 2) ∧ Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) := by
  have hδπ : δ ≤ π := by linarith [abs_nonneg z.arg]
  exact ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]),
    Complex.sin_half_le_cos_half_arg_of_abs_arg_le hδ.le hz⟩

/-- Comparison of the slit-plane derivative `‖r_n^{(k)}(z)‖` to its positive real-axis value at
`‖z‖`: for `n ≥ 1`, `k : ℕ`, and `z ∈ slitPlane`,
`‖r_n^{(k)}(z)‖ ≤ ((-1)^k (-1)^{n+1} r_n^{(k)}(‖z‖)) / cos (arg z / 2) ^ (2n + k)`. -/
theorem norm_iteratedDeriv_stirlingSeriesRemainder_le_real {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    ‖iteratedDeriv k (stirlingSeriesRemainder n) z‖ ≤
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (n + 1) * iteratedDeriv k (realStirlingSeriesRemainder n) ‖z‖) /
        Real.cos (z.arg / 2) ^ (2 * n + k) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_half_arg_pos hz
  rw [iteratedDeriv_stirlingSeriesRemainder hn k hz,
    signed_iteratedDeriv_realStirlingSeriesRemainder hn k hz_pos,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div,
    Complex.norm_natCast, Complex.norm_natCast, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_eq_mul_inv, mul_comm _ (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi n (by omega : 2 ≤ 2 * n + k) hz).norm
    ((integrableOn_signed_bernoulli_sub_div_pow_Ioi n
      (by omega : 2 ≤ 2 * n + k) hz_pos).const_mul _)
    measurableSet_Ioi fun u hu ↦ ?_)
  have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
  have hnn := neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg n u
  have habs : |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)| =
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) := by
    simpa [abs_mul] using abs_of_nonneg hnn
  have hsec : Real.cos (z.arg / 2) * (u + ‖z‖) ≤ ‖(u : ℂ) + z‖ := by
    simpa [add_comm] using Complex.cos_half_arg_mul_norm_add_le_norm_add_ofReal z u
  have hpow : Real.cos (z.arg / 2) ^ (2 * n + k) * (u + ‖z‖) ^ (2 * n + k) ≤
      ‖(u : ℂ) + z‖ ^ (2 * n + k) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsec (2 * n + k)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, habs]
  calc (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        ‖(u : ℂ) + z‖ ^ (2 * n + k)
      ≤ (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (Real.cos (z.arg / 2) ^ (2 * n + k) * (u + ‖z‖) ^ (2 * n + k)) :=
        div_le_div_of_nonneg_left hnn (by positivity) hpow
    _ = (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹ *
          ((-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + ‖z‖) ^ (2 * n + k)) := by
        simp only [div_eq_mul_inv, mul_inv]; ring

/-- **Stieltjes' sharp sector bound** on the slit plane: for every `n ≥ 1` and `z ∈ slitPlane`,
`‖r_n(z)‖ < ‖T_n(z)‖ / cos (arg z / 2) ^ (2n)`. -/
theorem norm_stirlingSeriesRemainder_lt {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingSeriesRemainder n z‖ < ‖stirlingTerm n z‖ / Real.cos (z.arg / 2) ^ (2 * n) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_half_arg_pos hz
  have hle := norm_iteratedDeriv_stirlingSeriesRemainder_le_real hn 0 hz
  simp only [iteratedDeriv_zero, pow_zero, one_mul, add_zero] at hle
  have habs_r : (-1 : ℝ) ^ (n + 1) * realStirlingSeriesRemainder n ‖z‖ =
      |realStirlingSeriesRemainder n ‖z‖| := by
    simpa [abs_mul] using
      (abs_of_pos (neg_one_pow_succ_mul_realStirlingSeriesRemainder_pos hn hz_pos)).symm
  rw [habs_r] at hle
  have hlt := abs_realStirlingSeriesRemainder_lt_abs_stirlingTerm hn hz_pos
  rw [← norm_stirlingTerm_eq_abs_norm n z] at hlt
  exact lt_of_le_of_lt hle (div_lt_div_of_pos_right hlt (pow_pos hcos_pos _))

/-- Sharp `1 / 12` half-angle bound for all derivatives of `TauCeti.stirlingRemainder` on the
slit plane: for every `k : ℕ` and `z ∈ slitPlane`,
`‖iteratedDeriv k stirlingRemainder z‖ < k! / (12 * cos (arg z / 2) ^ (k + 2) * ‖z‖ ^ (k + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_lt (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖iteratedDeriv k stirlingRemainder z‖ <
      (k ! : ℝ) / (12 * Real.cos (z.arg / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_half_arg_pos hz
  have hle := norm_iteratedDeriv_stirlingSeriesRemainder_le_real le_rfl k hz
  have hpow : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
  have hidx : 2 * 1 + k = k + 2 := by omega
  rw [hpow, mul_one, hidx, stirlingSeriesRemainder_one] at hle
  -- Since `G₀ = -r₂` is strictly completely monotone,
  -- `(-1)^k r₁^{(k)}(‖z‖) < (-1)^k T₁^{(k)}(‖z‖)`.
  have hG := neg_one_pow_mul_iteratedDeriv_neg_realStirlingSeriesRemainder_even_pos 0 k hz_pos
  have heq_r2 : (fun t : ℝ ↦ -realStirlingSeriesRemainder 2 t) =
      fun t : ℝ ↦ (12⁻¹ : ℝ) / t - realStirlingSeriesRemainder 1 t := by
    ext t; rw [realStirlingSeriesRemainder_succ, stirlingTerm_one]
    simp only [div_eq_mul_inv, mul_inv]; ring
  simp only [Nat.mul_zero, zero_add] at hG
  have hT1_cd : ContDiffAt ℝ k (fun t : ℝ ↦ (12⁻¹ : ℝ) / t) ‖z‖ :=
    contDiffAt_const.div contDiffAt_id hz_pos.ne'
  rw [heq_r2, iteratedDeriv_fun_sub hT1_cd
    (((contDiffOn_realStirlingSeriesRemainder 1).contDiffAt (isOpen_Ioi.mem_nhds hz_pos)).of_le
      (by exact_mod_cast le_top))] at hG
  have hT1_deriv : iteratedDeriv k (fun t : ℝ ↦ (12⁻¹ : ℝ) / t) ‖z‖ =
      (-1 : ℝ) ^ k * ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) := by
    rw [TauCeti.iteratedDeriv_const_div]
    simp only [div_eq_mul_inv, mul_inv]; ring
  rw [hT1_deriv, mul_sub, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul] at hG
  calc ‖iteratedDeriv k stirlingRemainder z‖
      ≤ ((-1 : ℝ) ^ k * iteratedDeriv k (realStirlingSeriesRemainder 1) ‖z‖) /
          Real.cos (z.arg / 2) ^ (k + 2) := hle
    _ < ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) / Real.cos (z.arg / 2) ^ (k + 2) :=
        div_lt_div_of_pos_right (by linarith) (pow_pos hcos_pos _)
    _ = (k ! : ℝ) / (12 * Real.cos (z.arg / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
        simp only [div_eq_mul_inv, mul_inv]; ring

/-- Uniform sector form of Stieltjes' bound: for `0 < δ`, `|arg z| ≤ π - δ`, `z ≠ 0`, and
`n ≥ 1`, `‖r_n(z)‖ < ‖T_n(z)‖ / sin (δ / 2) ^ (2n)`. -/
theorem norm_stirlingSeriesRemainder_lt_of_abs_arg_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingSeriesRemainder n z‖ < ‖stirlingTerm n z‖ / Real.sin (δ / 2) ^ (2 * n) := by
  have hslit : z ∈ slitPlane := Complex.mem_slitPlane_of_abs_arg_le hδ hz hz0
  obtain ⟨hsin_pos, hsin_le⟩ := sin_half_pos_le_cos_half_arg hδ hz
  exact lt_of_lt_of_le (norm_stirlingSeriesRemainder_lt hn hslit)
    (div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hsin_pos _)
      (pow_le_pow_left₀ hsin_pos.le hsin_le _))

/-- Sharp `1 / 12` closed-sector bound for all derivatives of `TauCeti.stirlingRemainder`:
for `0 < δ`, nonzero `z` with `|arg z| ≤ π - δ`, and every `k : ℕ`,
`‖iteratedDeriv k stirlingRemainder z‖ < k! / (12 * sin (δ / 2) ^ (k + 2) * ‖z‖ ^ (k + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le (k : ℕ) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖iteratedDeriv k stirlingRemainder z‖ <
      (k ! : ℝ) / (12 * Real.sin (δ / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
  have hslit : z ∈ slitPlane := Complex.mem_slitPlane_of_abs_arg_le hδ hz hz0
  obtain ⟨hsin_pos, hsin_le⟩ := sin_half_pos_le_cos_half_arg hδ hz
  have : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  exact lt_of_lt_of_le (norm_iteratedDeriv_stirlingRemainder_lt k hslit) (by gcongr)

/-- Stieltjes' sharp `1 / 12` slit-plane bound for `TauCeti.stirlingRemainder`:
`‖stirlingRemainder z‖ < 1 / (12 * cos (arg z / 2) ^ 2 * ‖z‖)` for `z ∈ slitPlane`. -/
theorem norm_stirlingRemainder_lt {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingRemainder z‖ < 1 / (12 * Real.cos (z.arg / 2) ^ 2 * ‖z‖) := by
  simpa [iteratedDeriv_zero] using norm_iteratedDeriv_stirlingRemainder_lt 0 hz

/-- Ramaré's sector form of Stieltjes' `n = 1` bound for `TauCeti.stirlingRemainder`:
for `0 < δ`, `|arg z| ≤ π - δ`, and `z ≠ 0`,
`‖stirlingRemainder z‖ < 1 / (12 * sin (δ / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_lt_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingRemainder z‖ < 1 / (12 * Real.sin (δ / 2) ^ 2 * ‖z‖) := by
  simpa [iteratedDeriv_zero] using norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le 0 hδ hz hz0

/-- Stieltjes' `1 / 6` bound on the closed right half-plane: `‖stirlingRemainder z‖ < 1 / (6 * ‖z‖)`
for nonzero `z` with `0 ≤ re z`. This is the closed-sector bound at `δ = π / 2`. -/
theorem norm_stirlingRemainder_lt_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    ‖stirlingRemainder z‖ < 1 / (6 * ‖z‖) := by
  have hdiv : π / 2 / 2 = π / 4 := by ring
  have hsin : Real.sin (π / 2 / 2) ^ 2 = 1 / 2 := by
    rw [hdiv, Real.sin_pi_div_four, div_pow, Real.sq_sqrt zero_le_two]
    norm_num
  have h := norm_stirlingRemainder_lt_of_abs_arg_le (δ := π / 2) (by positivity)
    (by rw [sub_half]; exact abs_arg_le_pi_div_two_iff.mpr hz) hz0
  rw [hsin] at h
  exact h.trans_eq (by ring)

/-- Sharp `1 / 12` closed-sector Stirling bound for `log ‖Γ s‖`: for `0 < δ` and nonzero `s`
with `|arg s| ≤ π - δ`,
`|log ‖Γ s‖ - ((re s - 1/2) log ‖s‖ - im s · arg s - re s + log (2π) / 2)| <
1 / (12 * sin (δ / 2) ^ 2 * ‖s‖)`. -/
theorem abs_log_norm_Gamma_sub_stirling_lt {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : |s.arg| ≤ π - δ) (hs0 : s ≠ 0) :
    |Real.log ‖Complex.Gamma s‖ - ((s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re +
      Real.log (2 * π) / 2)| < 1 / (12 * Real.sin (δ / 2) ^ 2 * ‖s‖) := by
  rw [← stirlingRemainder_re (Complex.mem_slitPlane_of_abs_arg_le hδ hs hs0)]
  exact (abs_re_le_norm _).trans_lt (norm_stirlingRemainder_lt_of_abs_arg_le hδ hs hs0)

end TauCeti
