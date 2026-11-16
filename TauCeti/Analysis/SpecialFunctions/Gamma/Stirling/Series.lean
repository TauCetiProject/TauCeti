/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.Analysis.SpecialFunctions.Gamma.Log

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import TauCeti.NumberTheory.ZetaValues

/-!
# Stirling's asymptotic series for `log Γ` with periodic Bernoulli remainder

This file establishes Stirling's asymptotic expansion of the normalized holomorphic logarithm of
Gamma (`TauCeti.logGamma`) on the slit plane `ℂ ∖ (-∞, 0]` to arbitrary order `n ≥ 1`
(DLMF 5.11.1):
`logGamma z = (z - 1/2) log z - z + log (2π) / 2 + ∑_{j=1}^{n-1} T_j(z) + r_n(z)`,
where `T_j(z) = B_{2j} / (2j (2j - 1) z^{2j - 1})` is the `j`-th Stirling term and the exact
remainder admits both the constant-sign periodic Bernoulli representation
`r_n(z) = ∫₀^∞ (B_{2n} - B_{2n}({u})) / (2n (u + z)^{2n}) du`
and Olver's shifted form
`r_{n+1}(z) = -∫₀^∞ B_{2n}({u}) / (2n (u + z)^{2n}) du`.

Differentiation under the integral sign yields the exact integral representation for every
derivative `r_n^{(k)}(z)` on the slit plane.

## Main declarations

* `TauCeti.stirlingTerm`: the `j`-th Stirling term `B_{2j} / (2j (2j - 1) z^{2j - 1})` over any
  division ring.
* `TauCeti.stirlingRemainder`, `TauCeti.realStirlingRemainder`: the order-`n` Stirling remainder
  `r_n` on `ℂ` and on `ℝ`.
* `TauCeti.stirlingRemainder_succ_eq_neg_integral`: Olver's periodic Bernoulli integral for
  `r_{n+1}(z)` on `Complex.slitPlane`.
* `TauCeti.stirlingRemainder_eq_integral`: the exact periodic Bernoulli integral for `r_n(z)` on
  `Complex.slitPlane`.
* `TauCeti.stirlingRemainder_one_eq_integral`: the `n = 1` Stieltjes representation with
  `({u} - {u}²) / 2`.
* `TauCeti.differentiableOn_stirlingRemainder`, `TauCeti.iteratedDeriv_stirlingRemainder`:
  holomorphy and exact integral representation of every iterated derivative `r_n^{(k)}(z)` on
  `Complex.slitPlane`.

## References

* NIST *Digital Library of Mathematical Functions*, §5.11, formula 5.11.1.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444.
-/

public section

open Complex Real Filter Set Topology MeasureTheory
open scoped Nat

namespace TauCeti

/-! ### Stirling terms and remainders -/

/-- The `j`-th term `T_j(z) = B_{2j} / (2j (2j - 1) z^{2j - 1})` in Stirling's asymptotic series
for `log Γ(z)`. For `j = 0` this evaluates to `0`. -/
@[expose] def stirlingTerm {𝕜 : Type*} [DivisionRing 𝕜] (j : ℕ) (z : 𝕜) : 𝕜 :=
  (bernoulli (2 * j) : 𝕜) / ((2 * j : 𝕜) * (2 * j - 1 : 𝕜) * z ^ (2 * j - 1))

/-- The `0`-th Stirling term is `0`. -/
@[simp]
theorem stirlingTerm_zero {𝕜 : Type*} [DivisionRing 𝕜] (z : 𝕜) :
    stirlingTerm 0 z = 0 := by
  simp [stirlingTerm]

/-- The first Stirling term is `1 / (12 z)`. -/
theorem stirlingTerm_one {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 1 z = 1 / (12 * z) := by
  simp only [stirlingTerm, Nat.mul_one, bernoulli_two, Rat.cast_inv, Rat.cast_ofNat, Nat.cast_one]
  ring

private theorem bernoulli_four_eq : bernoulli 4 = -1 / 30 := by
  have h := sum_bernoulli 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, bernoulli_zero, bernoulli_one,
    bernoulli_two, bernoulli_eq_zero_of_odd (by decide : Odd 3) (by decide : 1 < 3)] at h
  norm_num [Nat.choose] at h
  linarith

private theorem bernoulli_six_eq : bernoulli 6 = 1 / 42 := by
  have h := sum_bernoulli 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, bernoulli_zero, bernoulli_one,
    bernoulli_two, bernoulli_four_eq,
    bernoulli_eq_zero_of_odd (by decide : Odd 3) (by decide : 1 < 3),
    bernoulli_eq_zero_of_odd (by decide : Odd 5) (by decide : 1 < 5)] at h
  norm_num [Nat.choose] at h
  linarith

/-- The second Stirling term is `-1 / (360 z³)`. -/
theorem stirlingTerm_two {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 2 z = -(1 / (360 * z ^ 3)) := by
  simp only [stirlingTerm, show 2 * 2 = 4 by rfl, show 4 - 1 = 3 by rfl, bernoulli_four_eq,
    Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat]
  ring

/-- The third Stirling term is `1 / (1260 z⁵)`. -/
theorem stirlingTerm_three {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 3 z = 1 / (1260 * z ^ 5) := by
  simp only [stirlingTerm, show 2 * 3 = 6 by rfl, show 6 - 1 = 5 by rfl, bernoulli_six_eq,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat]
  ring

/-- Coercion of a real Stirling term to `ℂ`. -/
@[simp]
theorem ofReal_stirlingTerm (j : ℕ) (x : ℝ) :
    ((stirlingTerm j x : ℝ) : ℂ) = stirlingTerm j (x : ℂ) := by
  simp only [stirlingTerm]
  push_cast
  rfl

/-- Explicit modulus of the `j`-th Stirling term. -/
theorem norm_stirlingTerm (j : ℕ) (z : ℂ) :
    ‖stirlingTerm j z‖ =
      |(bernoulli (2 * j) : ℝ)| / ((2 * j : ℝ) * (2 * j - 1 : ℝ) * ‖z‖ ^ (2 * j - 1)) := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · have hpos2 : (0 : ℝ) ≤ 2 * (j : ℝ) - 1 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      linarith
    simp only [stirlingTerm, norm_div, norm_mul, norm_pow, ← Complex.ofReal_ratCast,
      Complex.norm_real, Complex.norm_ofNat, Complex.norm_natCast, Real.norm_eq_abs]
    have h2 : ‖(2 : ℂ) * (j : ℂ) - 1‖ = 2 * (j : ℝ) - 1 := by
      rw [show (2 : ℂ) * (j : ℂ) - 1 = ((2 * (j : ℝ) - 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos2]
    rw [h2]

/-- The modulus of `stirlingTerm j z` equals `|stirlingTerm j ‖z‖|`. -/
theorem norm_stirlingTerm_eq_abs_norm (j : ℕ) (z : ℂ) :
    ‖stirlingTerm j z‖ = |stirlingTerm j ‖z‖| := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · have hpos1 : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
    have hpos2 : (0 : ℝ) ≤ 2 * (j : ℝ) - 1 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      linarith
    rw [norm_stirlingTerm, stirlingTerm, abs_div, abs_mul, abs_mul, abs_of_nonneg hpos1,
      abs_of_nonneg hpos2, abs_of_nonneg (pow_nonneg (norm_nonneg z) _)]

/-- The order-`n` remainder in Stirling's asymptotic series for `logGamma` on `ℂ`:
`r_n(z) = logGamma z - ((z - 1/2) log z - z + log (2π) / 2) - ∑_{j=1}^{n-1} T_j(z)`. -/
@[expose] noncomputable def stirlingRemainder (n : ℕ) (z : ℂ) : ℂ :=
  logGamma z - ((z - 1 / 2) * Complex.log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)) -
    ∑ j ∈ Finset.Ico 1 n, stirlingTerm j z

/-- The order-`n` remainder in Stirling's asymptotic series for `Real.log ∘ Real.Gamma` on `ℝ`:
`r_n(x) = log (Γ x) - ((x - 1/2) log x - x + log (2π) / 2) - ∑_{j=1}^{n-1} T_j(x)`. -/
@[expose] noncomputable def realStirlingRemainder (n : ℕ) (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) -
    ∑ j ∈ Finset.Ico 1 n, stirlingTerm j x

/-- The order-`1` complex Stirling remainder has no Bernoulli sum terms. -/
theorem stirlingRemainder_one (z : ℂ) :
    stirlingRemainder 1 z =
      logGamma z - ((z - 1 / 2) * Complex.log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)) := by
  simp [stirlingRemainder]

/-- The order-`1` real Stirling remainder has no Bernoulli sum terms. -/
theorem realStirlingRemainder_one (x : ℝ) :
    realStirlingRemainder 1 x =
      Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) := by
  simp [realStirlingRemainder]

/-- Recurrence relating consecutive complex Stirling remainders: `r_{n+1}(z) = r_n(z) - T_n(z)`. -/
theorem stirlingRemainder_succ (n : ℕ) (z : ℂ) :
    stirlingRemainder (n + 1) z = stirlingRemainder n z - stirlingTerm n z := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [stirlingRemainder]
  · simp only [stirlingRemainder, Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hn)]
    ring

/-- Recurrence relating consecutive real Stirling remainders: `r_{n+1}(x) = r_n(x) - T_n(x)`. -/
theorem realStirlingRemainder_succ (n : ℕ) (x : ℝ) :
    realStirlingRemainder (n + 1) x = realStirlingRemainder n x - stirlingTerm n x := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [realStirlingRemainder]
  · simp only [realStirlingRemainder, Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hn)]
    ring

/-- Additive form of Stirling's expansion for `logGamma`. -/
theorem logGamma_eq_stirling_add_remainder (n : ℕ) (z : ℂ) :
    logGamma z = (z - 1 / 2) * Complex.log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) +
      (∑ j ∈ Finset.Ico 1 n, stirlingTerm j z) + stirlingRemainder n z := by
  simp only [stirlingRemainder]
  ring

/-- Additive form of Stirling's expansion for `Real.log (Real.Gamma x)`. -/
theorem log_Gamma_eq_stirling_add_remainder (n : ℕ) (x : ℝ) :
    Real.log (Real.Gamma x) = (x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2 +
      (∑ j ∈ Finset.Ico 1 n, stirlingTerm j x) + realStirlingRemainder n x := by
  simp only [realStirlingRemainder]
  ring

/-- On the positive real axis, the complex Stirling remainder is the coercion of the real
Stirling remainder. -/
@[simp]
theorem stirlingRemainder_ofReal (n : ℕ) {x : ℝ} (hx : 0 < x) :
    stirlingRemainder n (x : ℂ) = (realStirlingRemainder n x : ℂ) := by
  simp only [stirlingRemainder, realStirlingRemainder, logGamma_ofReal hx,
    ← Complex.ofReal_log hx.le, ← ofReal_stirlingTerm]
  push_cast
  rfl

/-- Complex conjugation symmetry of the Stirling remainder on the slit plane. -/
theorem stirlingRemainder_conj (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder n (starRingEnd ℂ z) = starRingEnd ℂ (stirlingRemainder n z) := by
  have harg : z.arg ≠ π := (mem_slitPlane_iff_arg.mp hz).1
  simp only [stirlingRemainder, logGamma_conj hz, Complex.log_conj z harg, map_sub, map_add,
    map_mul, map_div₀, map_one, map_ofNat, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [stirlingTerm, map_div₀, map_mul, map_sub, map_pow, map_one, map_ofNat, map_natCast,
    ← Complex.ofReal_ratCast, Complex.conj_ofReal]

/-- Every Stirling remainder is holomorphic on the slit plane. -/
theorem differentiableOn_stirlingRemainder (n : ℕ) :
    DifferentiableOn ℂ (stirlingRemainder n) slitPlane := by
  have hlog : DifferentiableOn ℂ Complex.log slitPlane := fun z hz ↦
    (Complex.differentiableAt_log hz).differentiableWithinAt
  have hsum : DifferentiableOn ℂ (fun z ↦ ∑ j ∈ Finset.Ico 1 n, stirlingTerm j z) slitPlane := by
    refine DifferentiableOn.fun_sum fun j hj ↦ ?_
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    refine differentiableOn_const _ |>.div ?_ fun z hz ↦ ?_
    · exact (differentiableOn_const _).mul (differentiableOn_id.pow _)
    · refine mul_ne_zero (mul_ne_zero (by norm_cast; omega) ?_)
        (pow_ne_zero _ (slitPlane_ne_zero hz))
      have hpos : (0 : ℝ) < 2 * (j : ℝ) - 1 := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        linarith
      exact_mod_cast hpos.ne'
  refine (differentiableOn_logGamma.sub ?_).sub hsum
  exact (((differentiableOn_id.sub (differentiableOn_const _)).mul hlog).sub
    differentiableOn_id).add (differentiableOn_const _)

/-! ### Half-line reciprocal power integrals on the slit plane -/

/-- For `a > 0` and `k ≥ 2`, `u ↦ 1 / (u + a) ^ k` is integrable on `(0, ∞)`. -/
private theorem integrableOn_one_div_add_pow_Ioi {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    IntegrableOn (fun u : ℝ ↦ 1 / (u + a) ^ k) (Ioi 0) := by
  have hk' : -(k : ℝ) < -1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine (integrableOn_add_rpow_Ioi_of_lt hk' (by linarith : -a < 0)).congr_fun
    (fun u hu ↦ ?_) measurableSet_Ioi
  have hpos : 0 ≤ u + a := by linarith [mem_Ioi.mp hu]
  dsimp only
  rw [Real.rpow_neg hpos, Real.rpow_natCast, one_div]

private theorem hasDerivAt_neg_inv_mul_ofReal_add_pow {z : ℂ} {k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : (u : ℂ) + z ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ -(1 / (((k - 1 : ℕ) : ℂ) * ((t : ℂ) + z) ^ (k - 1))))
      (1 / ((u : ℂ) + z) ^ k) u := by
  have hk1 : ((k - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k - 1 ≠ 0)
  have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + z) 1 u := by
    simpa using (hasDerivAt_id (u : ℂ)).comp_ofReal.add_const z
  have hpow : HasDerivAt (fun t : ℝ ↦ ((t : ℂ) + z) ^ (k - 1))
      (((k - 1 : ℕ) : ℂ) * ((u : ℂ) + z) ^ (k - 2)) u := by
    simpa [Nat.sub_sub] using hlin.fun_pow (k - 1)
  have hden : HasDerivAt (fun t : ℝ ↦ ((k - 1 : ℕ) : ℂ) * ((t : ℂ) + z) ^ (k - 1))
      (((k - 1 : ℕ) : ℂ) * (((k - 1 : ℕ) : ℂ) * ((u : ℂ) + z) ^ (k - 2))) u :=
    hpow.const_mul _
  have hinv := (hden.inv (mul_ne_zero hk1 (pow_ne_zero _ hu))).neg
  refine (hinv.congr_of_eventuallyEq
    (Eventually.of_forall fun t ↦ by simp [one_div])).congr_deriv ?_
  have hpow_eq : ((u : ℂ) + z) ^ k = ((u : ℂ) + z) ^ (k - 2) * ((u : ℂ) + z) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hpow_eq' : ((u : ℂ) + z) ^ (k - 1) = ((u : ℂ) + z) ^ (k - 2) * ((u : ℂ) + z) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow_eq, hpow_eq']
  have hne2 : ((u : ℂ) + z) ^ (k - 2) ≠ 0 := pow_ne_zero _ hu
  field_simp

/-- For `z ∈ slitPlane` and `k ≥ 2`, `u ↦ 1 / (u + z) ^ k` is integrable on `(0, ∞)`. -/
private theorem integrableOn_one_div_ofReal_add_pow_Ioi {z : ℂ} (hz : z ∈ slitPlane) {k : ℕ}
    (hk : 2 ≤ k) :
    IntegrableOn (fun u : ℝ ↦ 1 / ((u : ℂ) + z) ^ k) (Ioi 0) := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_one_add_le_norm_ofReal_add hz
  have hcont : ContinuousOn (fun u : ℝ ↦ 1 / ((u : ℂ) + z) ^ k) (Ioi 0) := fun u hu ↦
    (continuousAt_const.div
      ((Complex.continuous_ofReal.add continuous_const).pow k).continuousAt
      (pow_ne_zero k (slitPlane_ne_zero (ofReal_add_mem_slitPlane hz (mem_Ioi.mp hu).le)))
      ).continuousWithinAt
  refine ((integrableOn_one_div_add_pow_Ioi one_pos hk).const_mul (c ^ k)⁻¹).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
  have hle : c * (u + 1) ≤ ‖(u : ℂ) + z‖ := by
    simpa [add_comm] using hbound u hu0
  have hpow : c ^ k * (u + 1) ^ k ≤ ‖(u : ℂ) + z‖ ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle k
  rw [norm_div, norm_one, norm_pow, ← one_div, one_div_mul_one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

/-- For `z ∈ slitPlane` and `k ≥ 2`, `∫₀^∞ (u + z)⁻ᵏ du = 1 / ((k - 1) z^{k - 1})`. -/
private theorem integral_Ioi_one_div_ofReal_add_pow {z : ℂ} (hz : z ∈ slitPlane) {k : ℕ}
    (hk : 2 ≤ k) :
    ∫ u in Ioi (0 : ℝ), 1 / ((u : ℂ) + z) ^ k = 1 / (((k - 1 : ℕ) : ℂ) * z ^ (k - 1)) := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_one_add_le_norm_ofReal_add hz
  have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  have htend : Tendsto
      (fun t : ℝ ↦ -(1 / (((k - 1 : ℕ) : ℂ) * ((t : ℂ) + z) ^ (k - 1)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ ↦
        1 / (((k - 1 : ℕ) : ℝ) * (c * (1 + t)) ^ (k - 1))) ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [norm_neg, norm_div, norm_one, norm_mul, norm_pow, Complex.norm_natCast]
      have hpow : (c * (1 + t)) ^ (k - 1) ≤ ‖(t : ℂ) + z‖ ^ (k - 1) :=
        pow_le_pow_left₀ (by positivity) (hbound t ht) (k - 1)
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
    · have hlin : Tendsto (fun t : ℝ ↦ c * (1 + t)) atTop atTop :=
        Tendsto.const_mul_atTop hc (tendsto_atTop_add_const_left _ 1 tendsto_id)
      have hpow : Tendsto (fun t : ℝ ↦ (c * (1 + t)) ^ (k - 1)) atTop atTop :=
        (tendsto_pow_atTop (by omega : k - 1 ≠ 0)).comp hlin
      exact tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hk1 hpow)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun u hu ↦ hasDerivAt_neg_inv_mul_ofReal_add_pow hk
      (slitPlane_ne_zero (ofReal_add_mem_slitPlane hz (mem_Ici.mp hu))))
    (integrableOn_one_div_ofReal_add_pow_Ioi hz hk) htend
  simpa only [zero_sub, neg_neg, Complex.ofReal_zero, zero_add] using h

/-- Integrability on `(0, ∞)` of `g(u) / (u + z) ^ k` for bounded measurable `g : ℝ → ℝ`,
`z ∈ slitPlane`, and `k ≥ 2`. -/
private theorem integrableOn_bounded_div_ofReal_add_pow_Ioi {g : ℝ → ℝ}
    (hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0))) {M : ℝ}
    (hg_bdd : ∀ u, |g u| ≤ M) {z : ℂ} (hz : z ∈ slitPlane) {k : ℕ} (hk : 2 ≤ k) :
    IntegrableOn (fun u : ℝ ↦ (g u : ℂ) / ((u : ℂ) + z) ^ k) (Ioi 0) := by
  have hint := integrableOn_one_div_ofReal_add_pow_Ioi hz hk
  have hmeas : AEStronglyMeasurable (fun u : ℝ ↦ (g u : ℂ)) (volume.restrict (Ioi 0)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas
  have hmul := hint.bdd_mul hmeas (Eventually.of_forall fun u ↦ by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hg_bdd u)
  exact hmul.congr (Eventually.of_forall fun u ↦ by ring)

private theorem measurable_bernoulliFun_fract (k : ℕ) :
    Measurable (fun u : ℝ ↦ bernoulliFun k (Int.fract u)) :=
  (continuous_bernoulliFun k).measurable.comp measurable_fract

/-- Integrability of the periodic Bernoulli integrand `(B_{2n} - B_{2n}({u})) / (u + z)^k` on
`(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
        ((u : ℂ) + z) ^ k) (Ioi 0) :=
  integrableOn_bounded_div_ofReal_add_pow_Ioi
    (measurable_const.sub (measurable_bernoulliFun_fract (2 * n))).aestronglyMeasurable
    (M := 2 * |(bernoulli (2 * n) : ℝ)|)
    (fun u ↦ by
      have hle := abs_bernoulliFun_even_fract_le n u
      calc |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)|
          ≤ |(bernoulli (2 * n) : ℝ)| + |bernoulliFun (2 * n) (Int.fract u)| := abs_sub _ _
        _ ≤ 2 * |(bernoulli (2 * n) : ℝ)| := by linarith)
    hz hk

/-- Integrability of Olver's periodic Bernoulli integrand `B_{2n}({u}) / (u + z)^k` on `(0, ∞)`
for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulliFun_fract_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((u : ℂ) + z) ^ k) (Ioi 0) :=
  integrableOn_bounded_div_ofReal_add_pow_Ioi
    (measurable_bernoulliFun_fract (2 * n)).aestronglyMeasurable
    (M := |(bernoulli (2 * n) : ℝ)|)
    (fun u ↦ abs_bernoulliFun_even_fract_le n u)
    hz hk

/-! ### Stirling's series via Euler–Maclaurin summation -/

private theorem tendsto_stirlingTerm_add_natCast (j : ℕ) (z : ℂ) :
    Tendsto (fun N : ℕ ↦ stirlingTerm j (z + N)) atTop (𝓝 0) := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · refine squeeze_zero_norm' (a := fun N : ℕ ↦
        |(bernoulli (2 * j) : ℝ)| /
          ((2 * j : ℝ) * (2 * j - 1 : ℝ) * ((N : ℝ) + z.re) ^ (2 * j - 1))) ?_ ?_
    · filter_upwards [eventually_ge_atTop (⌈-z.re⌉₊ + 1)] with N hN
      have hre : 0 < (N : ℝ) + z.re := by
        have h1 : -z.re ≤ (⌈-z.re⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈-z.re⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
        linarith
      have hnorm : (N : ℝ) + z.re ≤ ‖z + N‖ := by
        simpa [add_comm] using Complex.re_le_norm (z + N)
      rw [norm_stirlingTerm]
      have h1 : (0 : ℝ) < 2 * (j : ℝ) := by positivity
      have h2 : (0 : ℝ) < 2 * (j : ℝ) - 1 := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
        linarith
      refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hre.le hnorm _) (mul_pos h1 h2).le
    · have hpow : Tendsto (fun N : ℕ ↦ ((N : ℝ) + z.re) ^ (2 * j - 1)) atTop atTop :=
        (tendsto_pow_atTop (by omega : 2 * j - 1 ≠ 0)).comp
          (tendsto_atTop_add_const_right _ z.re tendsto_natCast_atTop_atTop)
      have h1 : (0 : ℝ) < 2 * (j : ℝ) := by positivity
      have h2 : (0 : ℝ) < 2 * (j : ℝ) - 1 := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
        linarith
      exact tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (mul_pos h1 h2) hpow)

private theorem tendsto_stirlingRemainder_one_add_natCast (z : ℂ) :
    Tendsto (fun N : ℕ ↦ stirlingRemainder 1 (z + N)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun N : ℕ ↦ 2 / ((N : ℝ) + z.re)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (⌈-z.re⌉₊ + 1)] with N hN
    have hre : 0 < (z + N).re := by
      have h1 : -z.re ≤ (⌈-z.re⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈-z.re⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
      simp only [add_re, natCast_re]
      linarith
    have hne : z + N ≠ 0 := by
      intro h0
      rw [h0, zero_re] at hre
      exact lt_irrefl 0 hre
    have harg : |(z + N).arg| ≤ π - π / 2 := by
      rw [show π - π / 2 = π / 2 by ring, Complex.abs_arg_le_pi_div_two_iff]
      exact hre.le
    have hbound := norm_logGamma_sub_stirling_le (s := z + N) (δ := π / 2)
      Real.pi_div_two_pos (by linarith [pi_pos]) harg hne
    rw [Real.cos_pi_div_two, sub_zero, one_pow, one_mul, ← stirlingRemainder_one] at hbound
    have hnorm : (N : ℝ) + z.re ≤ ‖z + N‖ := by
      simpa [add_comm] using Complex.re_le_norm (z + N)
    exact hbound.trans (div_le_div_of_nonneg_left zero_le_two (by simpa [add_comm] using hre) hnorm)
  · exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ z.re tendsto_natCast_atTop_atTop)

private theorem tendsto_stirlingRemainder_add_natCast (n : ℕ) (z : ℂ) :
    Tendsto (fun N : ℕ ↦ stirlingRemainder n (z + N)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N : ℕ ↦ ∑ j ∈ Finset.Ico 1 n, stirlingTerm j (z + N)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.Ico 1 n) fun j _ ↦ tendsto_stirlingTerm_add_natCast j z
  have hsub := (tendsto_stirlingRemainder_one_add_natCast z).sub hsum
  rw [sub_zero] at hsub
  exact hsub.congr fun N ↦ by simp [stirlingRemainder]

/-- The explicit family of derivatives of `u ↦ Complex.log (u + z)`. -/
private noncomputable def logAddDeriv (z : ℂ) : ℕ → ℝ → ℂ
  | 0, u => Complex.log ((u : ℂ) + z)
  | i + 1, u => (-1 : ℂ) ^ i * (i ! : ℂ) / ((u : ℂ) + z) ^ (i + 1)

private theorem hasDerivAt_logAddDeriv {z : ℂ} (hz : z ∈ slitPlane) (i : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (logAddDeriv z i) (logAddDeriv z (i + 1) u) u := by
  have hmem : (u : ℂ) + z ∈ slitPlane := ofReal_add_mem_slitPlane hz hu
  have hne : (u : ℂ) + z ≠ 0 := slitPlane_ne_zero hmem
  have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + z) 1 u := by
    simpa using (hasDerivAt_id (u : ℂ)).comp_ofReal.add_const z
  cases i with
  | zero =>
    have hlog := (Complex.hasDerivAt_log hmem).comp u hlin
    refine hlog.congr_deriv ?_
    simp [logAddDeriv]
  | succ i =>
    have hpow : HasDerivAt (fun t : ℝ ↦ ((t : ℂ) + z) ^ (i + 1))
        (((i + 1 : ℕ) : ℂ) * ((u : ℂ) + z) ^ i) u := by
      simpa using hlin.fun_pow (i + 1)
    have hinv := (hpow.inv (pow_ne_zero _ hne)).const_mul ((-1 : ℂ) ^ i * (i ! : ℂ))
    refine hinv.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ by
      simp [logAddDeriv, div_eq_mul_inv]) |>.congr_deriv ?_
    simp only [logAddDeriv, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hne_i : ((u : ℂ) + z) ^ i ≠ 0 := pow_ne_zero _ hne
    field_simp

private theorem continuousOn_logAddDeriv {z : ℂ} (hz : z ∈ slitPlane) (i : ℕ) (N : ℕ) :
    ContinuousOn (logAddDeriv z i) (Icc (0 : ℝ) N) := fun _ hu ↦
  (hasDerivAt_logAddDeriv hz i hu.1).continuousAt.continuousWithinAt

private theorem integral_log_ofReal_add {z : ℂ} (hz : z ∈ slitPlane) (N : ℕ) :
    ∫ u in (0 : ℝ)..(N : ℝ), Complex.log ((u : ℂ) + z) =
      ((z + N) * Complex.log (z + N) - (z + N)) - (z * Complex.log z - z) := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) (N : ℝ),
      HasDerivAt (fun t : ℝ ↦ ((t : ℂ) + z) * Complex.log ((t : ℂ) + z) - ((t : ℂ) + z))
        (Complex.log ((u : ℂ) + z)) u := by
    intro u hu
    rw [uIcc_of_le (Nat.cast_nonneg N)] at hu
    have hmem : (u : ℂ) + z ∈ slitPlane := ofReal_add_mem_slitPlane hz hu.1
    have hne : (u : ℂ) + z ≠ 0 := slitPlane_ne_zero hmem
    have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + z) 1 u := by
      simpa using (hasDerivAt_id (u : ℂ)).comp_ofReal.add_const z
    have hlog := (Complex.hasDerivAt_log hmem).comp u hlin
    refine ((hlin.mul hlog).sub hlin).congr_deriv ?_
    simp [mul_inv_cancel₀ hne]
  have hint : IntervalIntegrable (fun u : ℝ ↦ Complex.log ((u : ℂ) + z)) volume 0 N :=
    (continuousOn_logAddDeriv hz 0 N).intervalIntegrable_of_Icc (Nat.cast_nonneg N)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [add_comm] using h

/-- Finite-truncation identity from Euler–Maclaurin of order `2n` applied to `u ↦ log (u + z)`. -/
private theorem stirlingRemainder_succ_eq_sub_intervalIntegral {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ slitPlane) (N : ℕ) :
    stirlingRemainder (n + 1) z = stirlingRemainder (n + 1) (z + N) -
      ∫ u in (0 : ℝ)..(N : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  have hint2n : IntervalIntegrable (logAddDeriv z (2 * n)) volume (0 : ℤ) (N : ℤ) := by
    simpa using (continuousOn_logAddDeriv hz (2 * n) N).intervalIntegrable_of_Icc
      (Nat.cast_nonneg N)
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := logAddDeriv z)
    (a := (0 : ℤ)) (n := (N : ℤ)) (Nat.cast_nonneg N) (k := 2 * n) (by omega)
    (fun i _ ↦ by simpa using continuousOn_logAddDeriv hz i N)
    (fun i _ u hu ↦ hasDerivAt_logAddDeriv hz i (by simpa using hu.1.le))
    hint2n
  -- Identify the finite sum via the functional equation of `logGamma`.
  have hsum_lhs : ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), logAddDeriv z 0 (j : ℝ) =
      logGamma (z + N) + Complex.log (z + N) - logGamma z := by
    have hbij : ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), logAddDeriv z 0 (j : ℝ) =
        ∑ j ∈ Finset.range (N + 1), Complex.log (z + (j : ℂ)) := by
      refine Finset.sum_nbij (fun j : ℤ ↦ j.toNat) ?_ ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_Icc] at hj
        rw [Finset.mem_range]
        omega
      · intro j₁ hj₁ j₂ hj₂ heq
        simp only [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
        dsimp only at heq
        omega
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_range] at hk
        exact ⟨(k : ℤ), Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨Int.natCast_nonneg k, by omega⟩),
          Int.toNat_natCast k⟩
      · intro j hj
        rw [Finset.mem_Icc] at hj
        have hcast : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by
          exact_mod_cast Int.toNat_of_nonneg hj.1
        simp only [logAddDeriv, hcast, add_comm]
        norm_cast
    rw [hbij, Finset.sum_range_succ, ← sub_eq_iff_eq_add'.mpr (logGamma_add_natCast hz N)]
    ring
  -- Keep only even terms in the Euler–Maclaurin Bernoulli sum.
  have hbern_sum :
      ∑ s ∈ Finset.Icc 2 (2 * n),
        (bernoulli s / (s ! : ℝ) : ℝ) •
          (logAddDeriv z (s - 1) (N : ℝ) - logAddDeriv z (s - 1) 0) =
      ∑ j ∈ Finset.Icc 1 n, (stirlingTerm j (z + N) - stirlingTerm j z) := by
    have heven : ∀ m ≥ 1,
        ∑ s ∈ Finset.Icc 2 (2 * m),
          (bernoulli s / (s ! : ℝ) : ℝ) •
            (logAddDeriv z (s - 1) (N : ℝ) - logAddDeriv z (s - 1) 0) =
        ∑ j ∈ Finset.Icc 1 m,
          (bernoulli (2 * j) / ((2 * j)! : ℝ) : ℝ) •
            (logAddDeriv z (2 * j - 1) (N : ℝ) - logAddDeriv z (2 * j - 1) 0) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        have hodd : bernoulli (2 * m + 1) = 0 :=
          bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega)
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_Icc_succ_top (by omega),
          Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih, hodd]
        simp [mul_add]
    rw [heven n hn]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hsub1 : 2 * j - 1 = (2 * j - 2) + 1 := by omega
    have heven_pow : (-1 : ℂ) ^ (2 * j - 2) = 1 := by
      have : 2 * j - 2 = 2 * (j - 1) := by omega
      rw [this, pow_mul, neg_one_sq, one_pow]
    have hfac : ((2 * j)! : ℂ) = (2 * j : ℂ) * (2 * j - 1 : ℂ) * ((2 * j - 2)! : ℂ) := by
      have h1 : 2 * j = (2 * j - 1) + 1 := by omega
      have h2 : 2 * j - 1 = (2 * j - 2) + 1 := by omega
      have hnat : (2 * j)! = (2 * j) * (2 * j - 1) * (2 * j - 2)! := by
        calc (2 * j)! = ((2 * j - 1) + 1)! := by rw [← h1]
          _ = (2 * j) * (2 * j - 1)! := by rw [Nat.factorial_succ, ← h1]
          _ = (2 * j) * ((2 * j - 2) + 1)! := by rw [← h2]
          _ = (2 * j) * ((2 * j - 1) * (2 * j - 2)!) := by rw [Nat.factorial_succ, ← h2]
          _ = (2 * j) * (2 * j - 1) * (2 * j - 2)! := by ring
      have hc : ((2 * j - 1 : ℕ) : ℂ) = (2 * j : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]
        push_cast
        rfl
      have hcast : ((2 * j)! : ℂ) =
          ((2 * j : ℕ) : ℂ) * ((2 * j - 1 : ℕ) : ℂ) * ((2 * j - 2)! : ℂ) := by
        exact_mod_cast hnat
      rw [hcast, hc]
      push_cast
      rfl
    have hterm : ∀ w : ℝ, (bernoulli (2 * j) / ((2 * j)! : ℝ) : ℝ) • logAddDeriv z (2 * j - 1) w =
        stirlingTerm j (z + w) := by
      intro w
      rw [Complex.real_smul, hsub1, logAddDeriv, heven_pow, one_mul, ← hsub1, stirlingTerm]
      push_cast
      rw [hfac, add_comm (w : ℂ) z]
      have hne_fac : ((2 * j - 2)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    rw [smul_sub, hterm (N : ℝ), hterm 0]
    simp
  -- Simplify the remainder integral in `hEM`.
  have hrem_int :
      ((-1 : ℝ) ^ (2 * n) / ((2 * n)! : ℝ)) •
        ∫ u in (0 : ℝ)..(N : ℝ), bernoulliFun (2 * n) (Int.fract u) • logAddDeriv z (2 * n) u =
      -∫ u in (0 : ℝ)..(N : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
    have hsub1 : 2 * n = (2 * n - 1) + 1 := by omega
    have hodd_pow : (-1 : ℂ) ^ (2 * n - 1) = -1 := by
      have : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
      exact this.neg_one_pow
    have heven_pow : (-1 : ℝ) ^ (2 * n) = 1 := by
      rw [pow_mul, neg_one_sq, one_pow]
    have hfac : ((2 * n)! : ℂ) = (2 * n : ℂ) * ((2 * n - 1)! : ℂ) := by
      have hnat : (2 * n)! = (2 * n) * (2 * n - 1)! := by
        calc (2 * n)! = ((2 * n - 1) + 1)! := by rw [← hsub1]
          _ = (2 * n) * (2 * n - 1)! := by rw [Nat.factorial_succ, ← hsub1]
      exact_mod_cast hnat
    rw [heven_pow, ← intervalIntegral.integral_smul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    rw [Complex.real_smul, Complex.real_smul, hsub1, logAddDeriv, hodd_pow, ← hsub1]
    push_cast
    rw [hfac]
    have hne_fac : ((2 * n - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  -- Assemble the finite Euler–Maclaurin identity.
  simp only [Int.cast_zero, Int.cast_natCast] at hEM
  rw [hsum_lhs, hbern_sum, hrem_int, sub_neg_eq_add] at hEM
  have hint_log : ∫ u in (0 : ℝ)..(N : ℝ), logAddDeriv z 0 u =
      ((z + N) * Complex.log (z + N) - (z + N)) - (z * Complex.log z - z) :=
    integral_log_ofReal_add hz N
  rw [hint_log] at hEM
  simp only [logAddDeriv, Complex.ofReal_zero, zero_add, Complex.ofReal_natCast,
    add_comm (N : ℂ) z, Complex.real_smul] at hEM
  simp only [stirlingRemainder, Finset.Ico_add_one_right_eq_Icc, Finset.sum_sub_distrib] at hEM ⊢
  push_cast at hEM ⊢
  linear_combination -hEM

/-- **Olver's integral representation** for the Stirling remainder on the slit plane:
for `n ≥ 1` and `z ∈ slitPlane`,
`r_{n+1}(z) = -∫₀^∞ B_{2n}({u}) / (2n (u + z)^{2n}) du`. -/
theorem stirlingRemainder_succ_eq_neg_integral {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder (n + 1) z =
      -∫ u in Ioi (0 : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  have hint : IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      (Ioi 0) := by
    have h := (integrableOn_bernoulliFun_fract_div_pow_Ioi n (by omega : 2 ≤ 2 * n) hz).const_mul
      ((2 * n : ℂ)⁻¹)
    exact h.congr (Eventually.of_forall fun u ↦ by simp only [div_eq_mul_inv, mul_inv]; ring)
  have hlim_int : Tendsto (fun N : ℕ ↦
      ∫ u in (0 : ℝ)..(N : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      atTop (𝓝 (∫ u in Ioi (0 : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop
  have hlim_rhs : Tendsto (fun N : ℕ ↦
      stirlingRemainder (n + 1) (z + N) -
        ∫ u in (0 : ℝ)..(N : ℝ),
          (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      atTop (𝓝 (-∫ u in Ioi (0 : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))) := by
    simpa using (tendsto_stirlingRemainder_add_natCast (n + 1) z).sub hlim_int
  have hconst : Tendsto (fun _ : ℕ ↦ stirlingRemainder (n + 1) z) atTop
      (𝓝 (stirlingRemainder (n + 1) z)) := tendsto_const_nhds
  exact tendsto_nhds_unique hconst
    (hlim_rhs.congr fun N ↦ (stirlingRemainder_succ_eq_sub_intervalIntegral hn hz N).symm)

/-- **Stirling's series with periodic Bernoulli remainder** on the slit plane (DLMF 5.11.1):
for `n ≥ 1` and `z ∈ slitPlane`,
`r_n(z) = ∫₀^∞ (B_{2n} - B_{2n}({u})) / (2n (u + z)^{2n}) du`. -/
theorem stirlingRemainder_eq_integral {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder n z =
      ∫ u in Ioi (0 : ℝ),
        (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
          ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  have hpow_int := integrableOn_one_div_ofReal_add_pow_Ioi hz (by omega : 2 ≤ 2 * n)
  have hconst_int : IntegrableOn (fun u : ℝ ↦
      ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n))) (Ioi 0) :=
    (hpow_int.const_mul (((bernoulli (2 * n) : ℝ) : ℂ) / (2 * n : ℂ))).congr
      (Eventually.of_forall fun u ↦ by simp only [div_eq_mul_inv, mul_inv]; ring)
  have hper_int : IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      (Ioi 0) :=
    ((integrableOn_bernoulliFun_fract_div_pow_Ioi n (by omega : 2 ≤ 2 * n) hz).const_mul
      ((2 * n : ℂ)⁻¹)).congr
        (Eventually.of_forall fun u ↦ by simp only [div_eq_mul_inv, mul_inv]; ring)
  have hterm : stirlingTerm n z =
      ∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
    have heq : (fun u : ℝ ↦
          ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n))) =
        fun u : ℝ ↦
          (((bernoulli (2 * n) : ℝ) : ℂ) / (2 * n : ℂ)) * (1 / ((u : ℂ) + z) ^ (2 * n)) := by
      ext u; simp only [div_eq_mul_inv, mul_inv]; ring
    rw [heq, integral_const_mul, integral_Ioi_one_div_ofReal_add_pow hz (by omega : 2 ≤ 2 * n),
      stirlingTerm]
    have hc : ((2 * n - 1 : ℕ) : ℂ) = (2 * n : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
      push_cast
      rfl
    rw [hc, Complex.ofReal_ratCast]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hsplit : stirlingRemainder n z = stirlingTerm n z + stirlingRemainder (n + 1) z := by
    rw [stirlingRemainder_succ]
    ring
  rw [hsplit, hterm, stirlingRemainder_succ_eq_neg_integral hn hz, ← sub_eq_add_neg,
    ← integral_sub hconst_int hper_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  push_cast
  ring

/-- **Stieltjes' representation** of the leading Stirling remainder on the slit plane:
for `z ∈ slitPlane`, `r₁(z) = ∫₀^∞ (({u} - {u}²) / 2) / (u + z)² du`. -/
theorem stirlingRemainder_one_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder 1 z =
      ∫ u in Ioi (0 : ℝ),
        (((Int.fract u - Int.fract u ^ 2) / 2 : ℝ) : ℂ) / ((u : ℂ) + z) ^ 2 := by
  rw [stirlingRemainder_eq_integral le_rfl hz]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  simp only [Nat.mul_one, bernoulli_two, Rat.cast_inv, Rat.cast_ofNat, bernoulliFun_two,
    Nat.cast_one]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ### Differentiation under the integral sign -/

/-- Differentiation under the integral sign for slit-plane reciprocal power kernels
`w ↦ ∫₀^∞ g(u) / (u + w) ^ m du` with bounded measurable `g` and `m ≥ 2`. -/
private theorem hasDerivAt_integral_div_ofReal_add_pow {g : ℝ → ℝ}
    (hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0))) {M : ℝ}
    (hg_bdd : ∀ u, |g u| ≤ M) {m : ℕ} (hm : 2 ≤ m) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ ↦ ∫ u in Ioi (0 : ℝ), (g u : ℂ) / ((u : ℂ) + w) ^ m)
      (-(m : ℂ) * ∫ u in Ioi (0 : ℝ), (g u : ℂ) / ((u : ℂ) + z) ^ (m + 1)) z := by
  obtain ⟨c, hc, hball⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  have hM : 0 ≤ M := le_trans (abs_nonneg (g 0)) (hg_bdd 0)
  have hmeas_g : AEStronglyMeasurable (fun u : ℝ ↦ (g u : ℂ)) (volume.restrict (Ioi 0)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun u : ℝ ↦ (g u : ℂ) / ((u : ℂ) + w) ^ m)
        (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun w ↦ by
      have hden : Measurable (fun u : ℝ ↦ (((u : ℂ) + w) ^ m)⁻¹) :=
        ((Complex.continuous_ofReal.add continuous_const).pow m).measurable.inv
      exact (hmeas_g.mul hden.aestronglyMeasurable).congr
        (Eventually.of_forall fun u ↦ by simp only [Pi.mul_apply, div_eq_mul_inv])
  have hF_int : Integrable (fun u : ℝ ↦ (g u : ℂ) / ((u : ℂ) + z) ^ m)
      (volume.restrict (Ioi 0)) :=
    integrableOn_bounded_div_ofReal_add_pow_Ioi hg_meas hg_bdd hz hm
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ ↦ -(m : ℂ) * (g u : ℂ) / ((u : ℂ) + z) ^ (m + 1))
      (volume.restrict (Ioi 0)) := by
    have hden : Measurable (fun u : ℝ ↦ (((u : ℂ) + z) ^ (m + 1))⁻¹) :=
      ((Complex.continuous_ofReal.add continuous_const).pow (m + 1)).measurable.inv
    exact (((aestronglyMeasurable_const (b := -(m : ℂ))).mul hmeas_g).mul
      hden.aestronglyMeasurable).congr
      (Eventually.of_forall fun u ↦ by simp only [Pi.mul_apply, div_eq_mul_inv])
  have h_bound : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ∀ w ∈ Metric.ball z c,
      ‖-(m : ℂ) * (g u : ℂ) / ((u : ℂ) + w) ^ (m + 1)‖ ≤
        ((m : ℝ) * M / c ^ (m + 1)) * (1 / (u + 1) ^ (m + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu w hw
    have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
    have hle : c * (u + 1) ≤ ‖(u : ℂ) + w‖ := by
      have h : c * (1 + u) ≤ ‖w + (u : ℂ)‖ := hball w hw ⟨u, hu0⟩
      simpa only [add_comm 1 u, add_comm w (u : ℂ)] using h
    have hpow : (c * (u + 1)) ^ (m + 1) ≤ ‖(u : ℂ) + w‖ ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) hle (m + 1)
    rw [norm_div, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      norm_pow]
    calc (m : ℝ) * |g u| / ‖(u : ℂ) + w‖ ^ (m + 1)
        ≤ (m : ℝ) * M / (c * (u + 1)) ^ (m + 1) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hg_bdd u) (Nat.cast_nonneg m))
            (by positivity) hpow
      _ = ((m : ℝ) * M / c ^ (m + 1)) * (1 / (u + 1) ^ (m + 1)) := by
          rw [mul_pow]
          simp only [div_eq_mul_inv, mul_inv]
          ring
  have hbound_int : Integrable
      (fun u : ℝ ↦ ((m : ℝ) * M / c ^ (m + 1)) * (1 / (u + 1) ^ (m + 1)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_one_div_add_pow_Ioi one_pos (by omega : 2 ≤ m + 1)).const_mul _
  have h_diff : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ∀ w ∈ Metric.ball z c,
      HasDerivAt (fun w' : ℂ ↦ (g u : ℂ) / ((u : ℂ) + w') ^ m)
        (-(m : ℂ) * (g u : ℂ) / ((u : ℂ) + w) ^ (m + 1)) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu w hw
    have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
    have hne : (u : ℂ) + w ≠ 0 := by
      have h : c * (1 + u) ≤ ‖w + (u : ℂ)‖ := hball w hw ⟨u, hu0⟩
      have hpos : 0 < ‖(u : ℂ) + w‖ :=
        lt_of_lt_of_le (show 0 < c * (1 + u) by positivity) (by rwa [add_comm (u : ℂ) w])
      exact norm_pos_iff.mp hpos
    have hpow : HasDerivAt (fun w' : ℂ ↦ ((u : ℂ) + w') ^ m)
        ((m : ℂ) * ((u : ℂ) + w) ^ (m - 1)) w := by
      simpa using ((hasDerivAt_id w).const_add (u : ℂ)).fun_pow m
    have hinv := (hpow.inv (pow_ne_zero m hne)).const_mul (g u : ℂ)
    refine hinv.congr_of_eventuallyEq (Eventually.of_forall fun w' ↦ by simp [div_eq_mul_inv])
      |>.congr_deriv ?_
    have hpow1 : ((u : ℂ) + w) ^ m = ((u : ℂ) + w) ^ (m - 1) * ((u : ℂ) + w) := by
      rw [← pow_succ]
      congr 1
      omega
    have hpow2 : ((u : ℂ) + w) ^ (m + 1) = ((u : ℂ) + w) ^ (m - 1) * ((u : ℂ) + w) ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow1, hpow2]
    have hne' : ((u : ℂ) + w) ^ (m - 1) ≠ 0 := pow_ne_zero _ hne
    field_simp
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z hc)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  refine hres.congr_deriv ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  ring

/-- Exact integral representation of every iterated derivative of the Stirling remainder on the
slit plane: for `n ≥ 1`, `k : ℕ`, and `z ∈ slitPlane`,
`r_n^{(k)}(z) = (-1)^k ((2n + k - 1)! / (2n)!) ∫₀^∞ (B_{2n} - B_{2n}({u})) / (u + z)^{2n + k} du`.
-/
theorem iteratedDeriv_stirlingRemainder {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv k (stirlingRemainder n) z =
      (-1 : ℂ) ^ k * (((2 * n + k - 1)! : ℂ) / ((2 * n)! : ℂ)) *
        ∫ u in Ioi (0 : ℝ),
          (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
            ((u : ℂ) + z) ^ (2 * n + k) := by
  induction k generalizing z with
  | zero =>
    rw [iteratedDeriv_zero, pow_zero, one_mul, add_zero, stirlingRemainder_eq_integral hn hz,
      ← integral_const_mul]
    have hfac : ((2 * n)! : ℂ) = (2 * n : ℂ) * ((2 * n - 1)! : ℂ) := by
      have h1 : 2 * n = (2 * n - 1) + 1 := by omega
      have hnat : (2 * n)! = (2 * n) * (2 * n - 1)! := by
        calc (2 * n)! = ((2 * n - 1) + 1)! := by rw [← h1]
          _ = (2 * n) * (2 * n - 1)! := by rw [Nat.factorial_succ, ← h1]
      exact_mod_cast hnat
    have hne_fac : ((2 * n - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    rw [hfac]
    field_simp
  | succ k ih =>
    have hev : iteratedDeriv k (stirlingRemainder n) =ᶠ[𝓝 z]
        fun w ↦ (-1 : ℂ) ^ k * (((2 * n + k - 1)! : ℂ) / ((2 * n)! : ℂ)) *
          ∫ u in Ioi (0 : ℝ),
            (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
              ((u : ℂ) + w) ^ (2 * n + k) :=
      Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw ↦ ih hw
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hderiv := (hasDerivAt_integral_div_ofReal_add_pow
      (g := fun u ↦ (bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u))
      (measurable_const.sub (measurable_bernoulliFun_fract (2 * n))).aestronglyMeasurable
      (M := 2 * |(bernoulli (2 * n) : ℝ)|)
      (fun u ↦ by
        have hle := abs_bernoulliFun_even_fract_le n u
        calc |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)|
            ≤ |(bernoulli (2 * n) : ℝ)| + |bernoulliFun (2 * n) (Int.fract u)| := abs_sub _ _
          _ ≤ 2 * |(bernoulli (2 * n) : ℝ)| := by linarith)
      (m := 2 * n + k) (by omega) hz).const_mul
        ((-1 : ℂ) ^ k * (((2 * n + k - 1)! : ℂ) / ((2 * n)! : ℂ)))
    rw [hderiv.deriv]
    have hfac : ((2 * n + (k + 1) - 1)! : ℂ) = ((2 * n + k : ℕ) : ℂ) * ((2 * n + k - 1)! : ℂ) := by
      have h1 : 2 * n + (k + 1) - 1 = (2 * n + k - 1) + 1 := by omega
      have h2 : (2 * n + k - 1) + 1 = 2 * n + k := by omega
      have hnat : (2 * n + (k + 1) - 1)! = (2 * n + k) * (2 * n + k - 1)! := by
        rw [h1, Nat.factorial_succ, h2]
      exact_mod_cast hnat
    rw [hfac, pow_succ, show 2 * n + k + 1 = 2 * n + (k + 1) by omega]
    ring

end TauCeti
