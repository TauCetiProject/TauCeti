/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.HalfLineRational
import TauCeti.Analysis.SpecialFunctions.Integrals.PeriodicBernoulli
import TauCeti.Analysis.SpecialFunctions.Integrals.PeriodicStieltjes
import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

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
derivative `r_n^{(k)}(z)` on the slit plane and on `(0, ∞)`.

## Main declarations

* `TauCeti.stirlingTerm`: the `j`-th Stirling term `B_{2j} / (2j (2j - 1) z^{2j - 1})` over any
  division ring.
* `TauCeti.stirlingSeriesRemainder`, `TauCeti.realStirlingSeriesRemainder`: the order-`n`
  Stirling remainder `r_n` on `ℂ` and on `ℝ`.
* `TauCeti.stirlingSeriesRemainder_succ_eq_neg_integral`: Olver's periodic Bernoulli integral for
  `r_{n+1}(z)` on `Complex.slitPlane`.
* `TauCeti.stirlingSeriesRemainder_eq_integral`: the exact periodic Bernoulli integral for `r_n(z)`
  on `Complex.slitPlane`.
* `TauCeti.differentiableOn_stirlingSeriesRemainder`,
  `TauCeti.iteratedDeriv_stirlingSeriesRemainder`:
  holomorphy and exact integral representation of every iterated derivative `r_n^{(k)}(z)` on
  `Complex.slitPlane`.
* `TauCeti.contDiffOn_realStirlingSeriesRemainder`,
  `TauCeti.iteratedDeriv_stirlingSeriesRemainder_ofReal`,
  `TauCeti.iteratedDeriv_realStirlingSeriesRemainder`,
  `TauCeti.realStirlingSeriesRemainder_eq_integral`: smoothness and real integral representation of
  `realStirlingSeriesRemainder n` and its derivatives on `(0, ∞)`.

## References

* NIST *Digital Library of Mathematical Functions*, §5.11, formula 5.11.1.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444.
-/

public section

open Complex Real Filter Set Topology MeasureTheory
open scoped ContDiff Nat

namespace TauCeti

/-! ### Stirling terms and remainders -/

/-- The `j`-th term `T_j(z) = B_{2j} / (2j (2j - 1) z^{2j - 1})` in Stirling's asymptotic series
for `log Γ(z)`. For `j = 0` this evaluates to `0`. -/
def stirlingTerm {𝕜 : Type*} [DivisionRing 𝕜] (j : ℕ) (z : 𝕜) : 𝕜 :=
  (bernoulli (2 * j) : 𝕜) / ((2 * j : 𝕜) * (2 * j - 1 : 𝕜) * z ^ (2 * j - 1))

/-- Unfolding formula for `TauCeti.stirlingTerm`. -/
theorem stirlingTerm_def {𝕜 : Type*} [DivisionRing 𝕜] (j : ℕ) (z : 𝕜) :
    stirlingTerm j z =
      (bernoulli (2 * j) : 𝕜) / ((2 * j : 𝕜) * (2 * j - 1 : 𝕜) * z ^ (2 * j - 1)) :=
  (rfl)

/-- The `0`-th Stirling term is `0`. -/
@[simp]
theorem stirlingTerm_zero {𝕜 : Type*} [DivisionRing 𝕜] (z : 𝕜) :
    stirlingTerm 0 z = 0 := by
  simp [stirlingTerm_def]

/-- The first Stirling term is `1 / (12 z)`. -/
@[simp]
theorem stirlingTerm_one {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 1 z = 1 / (12 * z) := by
  simp only [stirlingTerm_def, Nat.mul_one, bernoulli_two, Rat.cast_inv, Rat.cast_ofNat,
    Nat.cast_one]
  ring

/-- The second Stirling term is `-1 / (360 z³)`. -/
@[simp]
theorem stirlingTerm_two {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 2 z = -(1 / (360 * z ^ 3)) := by
  simp only [stirlingTerm_def, Nat.reduceMul, Nat.reduceSub, bernoulli_four,
    Rat.cast_neg, Rat.cast_inv, Rat.cast_ofNat, Nat.cast_ofNat]
  ring

/-- The third Stirling term is `1 / (1260 z⁵)`. -/
@[simp]
theorem stirlingTerm_three {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 3 z = 1 / (1260 * z ^ 5) := by
  simp only [stirlingTerm_def, Nat.reduceMul, Nat.reduceSub, bernoulli_six,
    Rat.cast_inv, Rat.cast_ofNat, Nat.cast_ofNat]
  ring

/-- Coercion of a real Stirling term to `ℂ`. -/
@[simp]
theorem ofReal_stirlingTerm (j : ℕ) (x : ℝ) :
    ((stirlingTerm j x : ℝ) : ℂ) = stirlingTerm j (x : ℂ) := by
  simp only [stirlingTerm_def]
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
    simp only [stirlingTerm_def, norm_div, norm_mul, norm_pow, ← Complex.ofReal_ratCast,
      Complex.norm_real, Complex.norm_ofNat, Complex.norm_natCast, Real.norm_eq_abs]
    have hc : (2 : ℂ) * (j : ℂ) - 1 = ((2 * (j : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos2]

/-- The modulus of `stirlingTerm j z` equals `|stirlingTerm j ‖z‖|`. -/
theorem norm_stirlingTerm_eq_abs_norm (j : ℕ) (z : ℂ) :
    ‖stirlingTerm j z‖ = |stirlingTerm j ‖z‖| := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · have hpos1 : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
    have hpos2 : (0 : ℝ) ≤ 2 * (j : ℝ) - 1 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      linarith
    rw [norm_stirlingTerm, stirlingTerm_def, abs_div, abs_mul, abs_mul, abs_of_nonneg hpos1,
      abs_of_nonneg hpos2, abs_of_nonneg (pow_nonneg (norm_nonneg z) _)]

/-- The order-`n` remainder in Stirling's asymptotic series for `logGamma` on `ℂ`:
`r_n(z) = stirlingRemainder z - ∑_{j=1}^{n-1} T_j(z)`. -/
noncomputable def stirlingSeriesRemainder (n : ℕ) (z : ℂ) : ℂ :=
  stirlingRemainder z - ∑ j ∈ Finset.Ico 1 n, stirlingTerm j z

/-- Unfolding formula for `TauCeti.stirlingSeriesRemainder`. -/
theorem stirlingSeriesRemainder_def (n : ℕ) (z : ℂ) :
    stirlingSeriesRemainder n z =
      stirlingRemainder z - ∑ j ∈ Finset.Ico 1 n, stirlingTerm j z :=
  (rfl)

/-- The order-`n` remainder in Stirling's asymptotic series for `Real.log ∘ Real.Gamma` on `ℝ`:
`r_n(x) = log (Γ x) - ((x - 1/2) log x - x + log (2π) / 2) - ∑_{j=1}^{n-1} T_j(x)`. -/
noncomputable def realStirlingSeriesRemainder (n : ℕ) (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) -
    ∑ j ∈ Finset.Ico 1 n, stirlingTerm j x

/-- Unfolding formula for `TauCeti.realStirlingSeriesRemainder`. -/
theorem realStirlingSeriesRemainder_def (n : ℕ) (x : ℝ) :
    realStirlingSeriesRemainder n x =
      Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) -
        ∑ j ∈ Finset.Ico 1 n, stirlingTerm j x :=
  (rfl)

/-- The order-`1` Stirling series remainder coincides with `TauCeti.stirlingRemainder`. -/
@[simp]
theorem stirlingSeriesRemainder_one_eq_stirlingRemainder (z : ℂ) :
    stirlingSeriesRemainder 1 z = stirlingRemainder z := by
  simp [stirlingSeriesRemainder_def]

/-- The order-`1` real Stirling remainder has no Bernoulli sum terms. -/
theorem realStirlingSeriesRemainder_one (x : ℝ) :
    realStirlingSeriesRemainder 1 x =
      Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) := by
  simp [realStirlingSeriesRemainder_def]

/-- Recurrence relating consecutive complex Stirling remainders: `r_{n+1}(z) = r_n(z) - T_n(z)`. -/
theorem stirlingSeriesRemainder_succ (n : ℕ) (z : ℂ) :
    stirlingSeriesRemainder (n + 1) z = stirlingSeriesRemainder n z - stirlingTerm n z := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [stirlingSeriesRemainder_def]
  · simp only [stirlingSeriesRemainder_def,
      Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hn)]
    ring

/-- Recurrence relating consecutive real Stirling remainders: `r_{n+1}(x) = r_n(x) - T_n(x)`. -/
theorem realStirlingSeriesRemainder_succ (n : ℕ) (x : ℝ) :
    realStirlingSeriesRemainder (n + 1) x = realStirlingSeriesRemainder n x - stirlingTerm n x := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [realStirlingSeriesRemainder_def]
  · simp only [realStirlingSeriesRemainder_def,
      Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hn)]
    ring

/-- Additive form of Stirling's expansion for `logGamma`. -/
theorem logGamma_eq_stirling_add_remainder (n : ℕ) (z : ℂ) :
    logGamma z = (z - 1 / 2) * Complex.log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) +
      (∑ j ∈ Finset.Ico 1 n, stirlingTerm j z) + stirlingSeriesRemainder n z := by
  rw [stirlingSeriesRemainder_def, stirlingRemainder_def]
  ring

/-- Additive form of Stirling's expansion for `Real.log (Real.Gamma x)`. -/
theorem log_Gamma_eq_stirling_add_remainder (n : ℕ) (x : ℝ) :
    Real.log (Real.Gamma x) = (x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2 +
      (∑ j ∈ Finset.Ico 1 n, stirlingTerm j x) + realStirlingSeriesRemainder n x := by
  rw [realStirlingSeriesRemainder_def]
  ring

/-- On the positive real axis, the complex Stirling remainder is the coercion of the real
Stirling remainder. -/
@[simp]
theorem stirlingSeriesRemainder_ofReal (n : ℕ) {x : ℝ} (hx : 0 < x) :
    stirlingSeriesRemainder n (x : ℂ) = (realStirlingSeriesRemainder n x : ℂ) := by
  simp only [stirlingSeriesRemainder_def, realStirlingSeriesRemainder_def,
    stirlingRemainder_ofReal hx, ← ofReal_stirlingTerm]
  push_cast
  rfl

/-- Complex conjugation symmetry of the Stirling remainder on the slit plane. -/
theorem stirlingSeriesRemainder_conj (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingSeriesRemainder n (starRingEnd ℂ z) = starRingEnd ℂ (stirlingSeriesRemainder n z) := by
  simp only [stirlingSeriesRemainder_def, stirlingRemainder_conj hz, map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [stirlingTerm_def, map_div₀, map_mul, map_sub, map_pow, map_one, map_ofNat,
    map_natCast, ← Complex.ofReal_ratCast, Complex.conj_ofReal]

/-- Every Stirling remainder is holomorphic on the slit plane. -/
theorem differentiableOn_stirlingSeriesRemainder (n : ℕ) :
    DifferentiableOn ℂ (stirlingSeriesRemainder n) slitPlane := by
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
  exact (differentiableOn_stirlingRemainder.sub hsum).congr fun _ _ ↦
    (stirlingSeriesRemainder_def n _).symm

/-! ### Stirling's series via Euler–Maclaurin summation -/

private theorem tendsto_stirlingTerm_add_natCast (j : ℕ) (z : ℂ) :
    Tendsto (fun N : ℕ ↦ stirlingTerm j (z + N)) atTop (𝓝 0) := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · have h1 : (0 : ℝ) < 2 * (j : ℝ) := by positivity
    have h2 : (0 : ℝ) < 2 * (j : ℝ) - 1 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      linarith
    refine squeeze_zero_norm' (a := fun N : ℕ ↦
        |(bernoulli (2 * j) : ℝ)| /
          ((2 * j : ℝ) * (2 * j - 1 : ℝ) * ((N : ℝ) + z.re) ^ (2 * j - 1))) ?_ ?_
    · filter_upwards [eventually_ge_atTop (⌈-z.re⌉₊ + 1)] with N hN
      have hre : 0 < (N : ℝ) + z.re := by
        have h1' : -z.re ≤ (⌈-z.re⌉₊ : ℝ) := Nat.le_ceil _
        have h2' : (⌈-z.re⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
        linarith
      have hnorm : (N : ℝ) + z.re ≤ ‖z + N‖ := by
        simpa [add_comm] using Complex.re_le_norm (z + N)
      rw [norm_stirlingTerm]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hre.le hnorm _) (mul_pos h1 h2).le)
    · have hpow : Tendsto (fun N : ℕ ↦ ((N : ℝ) + z.re) ^ (2 * j - 1)) atTop atTop :=
        (tendsto_pow_atTop (by omega : 2 * j - 1 ≠ 0)).comp
          (tendsto_atTop_add_const_right _ z.re tendsto_natCast_atTop_atTop)
      exact tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (mul_pos h1 h2) hpow)

private theorem tendsto_stirlingSeriesRemainder_one_add_natCast (z : ℂ) :
    Tendsto (fun N : ℕ ↦ stirlingSeriesRemainder 1 (z + N)) atTop (𝓝 0) := by
  have hsin : 0 < Real.sin (π / 2 / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  refine squeeze_zero_norm'
    (a := fun N : ℕ ↦ 1 / (8 * Real.sin (π / 2 / 2) ^ 2 * ((N : ℝ) + z.re))) ?_
    (tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop (by positivity)
        (tendsto_atTop_add_const_right _ z.re tendsto_natCast_atTop_atTop)))
  filter_upwards [eventually_ge_atTop (⌈-z.re⌉₊ + 1)] with N hN
  have hre : 0 < (z + N).re := by
    have h1 : -z.re ≤ (⌈-z.re⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈-z.re⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    simp only [add_re, natCast_re]; linarith
  have hne : z + N ≠ 0 := fun h0 ↦ by simp [h0] at hre
  have harg : |(z + N).arg| ≤ π - π / 2 := by
    have hhalf : π - π / 2 = π / 2 := by ring
    rw [hhalf, Complex.abs_arg_le_pi_div_two_iff]
    exact hre.le
  have hbound : ‖stirlingSeriesRemainder 1 (z + N)‖ ≤
      1 / (8 * Real.sin (π / 2 / 2) ^ 2 * ‖z + N‖) := by
    rw [stirlingSeriesRemainder_one_eq_stirlingRemainder,
      stirlingRemainder_eq_integral (mem_slitPlane_of_abs_arg_le Real.pi_div_two_pos harg hne)]
    simpa using norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le_of_abs_arg_le 0
      Real.pi_div_two_pos harg
  have hre' : 0 < (N : ℝ) + z.re := by
    simpa only [add_re, natCast_re, add_comm] using hre
  have hnorm : (N : ℝ) + z.re ≤ ‖z + N‖ := by simpa [add_comm] using Complex.re_le_norm (z + N)
  exact hbound.trans (div_le_div_of_nonneg_left zero_le_one (by positivity)
    (mul_le_mul_of_nonneg_left hnorm (by positivity)))

private theorem tendsto_stirlingSeriesRemainder_add_natCast (n : ℕ) (z : ℂ) :
    Tendsto (fun N : ℕ ↦ stirlingSeriesRemainder n (z + N)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N : ℕ ↦ ∑ j ∈ Finset.Ico 1 n, stirlingTerm j (z + N)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.Ico 1 n) fun j _ ↦ tendsto_stirlingTerm_add_natCast j z
  simpa using ((tendsto_stirlingSeriesRemainder_one_add_natCast z).sub hsum).congr fun N ↦ by
    simp [stirlingSeriesRemainder_def]

private theorem stirlingTerm_eq_bernoulli_smul_iteratedDeriv_log {z : ℂ} (j : ℕ) (hj : 1 ≤ j)
    {w : ℝ} (hw : (w : ℂ) + z ∈ slitPlane) :
    (bernoulli (2 * j) / ((2 * j)! : ℝ) : ℝ) •
        iteratedDeriv (2 * j - 1) (fun t : ℝ ↦ Complex.log ((t : ℂ) + z)) w =
      stirlingTerm j (z + w) := by
  have heven_pow : (-1 : ℂ) ^ (2 * j - 1 - 1) = 1 := by
    have hidx : 2 * j - 1 - 1 = 2 * (j - 1) := by omega
    rw [hidx, pow_mul, neg_one_sq, one_pow]
  have hfac : ((2 * j)! : ℂ) = (2 * j : ℂ) * (2 * j - 1 : ℂ) * ((2 * j - 1 - 1)! : ℂ) := by
    have hnat : (2 * j)! = (2 * j) * ((2 * j - 1) * (2 * j - 1 - 1)!) := by
      rw [Nat.mul_factorial_pred (by omega), Nat.mul_factorial_pred (by omega)]
    have hc : ((2 * j - 1 : ℕ) : ℂ) = (2 * j : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]; push_cast; rfl
    have hcast : ((2 * j)! : ℂ) =
        (2 * j : ℂ) * ((2 * j - 1 : ℕ) : ℂ) * ((2 * j - 1 - 1)! : ℂ) := by
      rw [← mul_assoc] at hnat; exact_mod_cast hnat
    rw [hcast, hc]
  have hpow_eq : ((w : ℂ) + z) ^ (2 * j - 1) = (z + w) ^ (2 * j - 1) := by
    rw [add_comm (w : ℂ) z]
  have hne_fac : ((2 * j - 1 - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Complex.iteratedDeriv_log_ofReal_add (by omega) hw, Complex.real_smul, heven_pow, one_mul,
    stirlingTerm_def, hpow_eq]
  push_cast
  rw [hfac]
  field_simp

private theorem div_factorial_smul_bernoulliFun_iteratedDeriv_log {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    {u : ℝ} (hu : (u : ℂ) + z ∈ slitPlane) :
    ((-1 : ℝ) ^ (2 * n) / ((2 * n)! : ℝ)) • bernoulliFun (2 * n) (Int.fract u) •
        iteratedDeriv (2 * n) (fun t : ℝ ↦ Complex.log ((t : ℂ) + z)) u =
      -((bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n))) := by
  have hodd_pow : (-1 : ℂ) ^ (2 * n - 1) = -1 := Odd.neg_one_pow ⟨n - 1, by omega⟩
  have heven_pow : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  have hfac : ((2 * n)! : ℂ) = (2 * n : ℂ) * ((2 * n - 1)! : ℂ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : 2 * n ≠ 0)).symm
  have hne_fac : ((2 * n - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Complex.iteratedDeriv_log_ofReal_add (by omega) hu, heven_pow, Complex.real_smul,
    Complex.real_smul, hodd_pow]
  push_cast
  rw [hfac]
  field_simp

/-- Finite-truncation identity from Euler–Maclaurin of order `2n` applied to `u ↦ log (u + z)`. -/
private theorem stirlingSeriesRemainder_succ_eq_sub_intervalIntegral {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ slitPlane) (N : ℕ) :
    stirlingSeriesRemainder (n + 1) z = stirlingSeriesRemainder (n + 1) (z + N) -
      ∫ u in (0 : ℝ)..(N : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  let f : ℝ → ℂ := fun t ↦ Complex.log ((t : ℂ) + z)
  let g : ℕ → ℝ → ℂ := fun i u ↦ iteratedDeriv i f u
  let U : Set ℝ := {t : ℝ | (t : ℂ) + z ∈ slitPlane}
  have hU : IsOpen U := isOpen_slitPlane.preimage (continuous_ofReal.add continuous_const)
  have hIcc : Icc (0 : ℝ) N ⊆ U := fun u hu ↦ ofReal_add_mem_slitPlane hz hu.1
  have hcd : ContDiffOn ℝ ∞ f U :=
    fun u hu ↦ (Complex.contDiffAt_log_ofReal_add hu ∞).contDiffWithinAt
  have hdiff (i : ℕ) : DifferentiableOn ℝ (g i) U :=
    (hcd.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast ENat.natCast_lt_top i) hU.uniqueDiffOn).congr
      fun _ hu ↦ (iteratedDerivWithin_of_isOpen hU hu).symm
  have hsum_lhs : ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), g 0 (j : ℝ) =
      logGamma (z + N) + Complex.log (z + N) - logGamma z := by
    have hcard : ((N : ℤ) + 1 - 0).toNat = N + 1 := by omega
    rw [Int.Icc_eq_finset_map, hcard, Finset.sum_map]
    simp only [g, iteratedDeriv_zero, f, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, zero_add, Int.cast_natCast, Complex.ofReal_natCast, add_comm _ z,
      Finset.sum_range_succ]
    rw [logGamma_add_natCast hz N]
    ring
  have hint2n : IntervalIntegrable (g (2 * n)) volume (0 : ℤ) (N : ℤ) := by
    simpa using ((hdiff (2 * n)).continuousOn.mono hIcc).intervalIntegrable_of_Icc
      (Nat.cast_nonneg N)
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := g)
    (a := (0 : ℤ)) (n := (N : ℤ)) (Nat.cast_nonneg N) (k := 2 * n) (by omega)
    (fun i _ ↦ by simpa using (hdiff i).continuousOn.mono hIcc)
    (fun i _ u hu ↦ by
      have huU : u ∈ U := hIcc (Ioo_subset_Icc_self (by simpa using hu))
      simpa [g, iteratedDeriv_succ] using ((hdiff i).differentiableAt (hU.mem_nhds huU)).hasDerivAt)
    hint2n
  have hbern_sum :
      ∑ s ∈ Finset.Icc 2 (2 * n),
        (bernoulli s / (s ! : ℝ) : ℝ) • (g (s - 1) (N : ℝ) - g (s - 1) 0) =
      ∑ j ∈ Finset.Icc 1 n, (stirlingTerm j (z + N) - stirlingTerm j z) := by
    rw [sum_Icc_two_mul_bernoulli_smul n fun s ↦ g (s - 1) (N : ℝ) - g (s - 1) 0]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [smul_sub,
      stirlingTerm_eq_bernoulli_smul_iteratedDeriv_log j hj1
        (ofReal_add_mem_slitPlane hz (Nat.cast_nonneg N)),
      stirlingTerm_eq_bernoulli_smul_iteratedDeriv_log j hj1 (ofReal_add_mem_slitPlane hz le_rfl)]
    simp
  have hrem_int :
      ((-1 : ℝ) ^ (2 * n) / ((2 * n)! : ℝ)) •
        ∫ u in (0 : ℝ)..(N : ℝ), bernoulliFun (2 * n) (Int.fract u) • g (2 * n) u =
      -∫ u in (0 : ℝ)..(N : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
    rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [uIcc_of_le (Nat.cast_nonneg N)] at hu
    exact div_factorial_smul_bernoulliFun_iteratedDeriv_log hn (ofReal_add_mem_slitPlane hz hu.1)
  have hint_log : ∫ u in (0 : ℝ)..(N : ℝ), g 0 u =
      ((z + N) * Complex.log (z + N) - (z + N)) - (z * Complex.log z - z) := by
    simp only [g, iteratedDeriv_zero, f]
    have hlog := TauCeti.integral_log_ofReal_add (a := (0 : ℝ)) (b := (N : ℝ)) (z := z) fun u hu ↦
      by
        rw [uIcc_of_le (Nat.cast_nonneg N)] at hu
        exact ofReal_add_mem_slitPlane hz hu.1
    simpa only [Complex.ofReal_zero, add_zero, Complex.ofReal_natCast] using hlog
  simp only [Int.cast_zero, Int.cast_natCast] at hEM
  rw [hsum_lhs, hbern_sum, hrem_int, sub_neg_eq_add, hint_log] at hEM
  simp only [g, iteratedDeriv_zero, f, Complex.ofReal_zero, zero_add, Complex.ofReal_natCast,
    add_comm (N : ℂ) z, Complex.real_smul] at hEM
  simp only [stirlingSeriesRemainder_def, stirlingRemainder_def,
    Finset.Ico_add_one_right_eq_Icc, Finset.sum_sub_distrib] at hEM ⊢
  push_cast at hEM ⊢
  linear_combination -hEM

private theorem integrableOn_bernoulliFun_fract_div_two_mul_pow {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      (Ioi 0) :=
  ((integrableOn_bernoulliFun_fract_div_pow_Ioi n (by omega : 2 ≤ 2 * n) hz).const_mul
    ((2 * n : ℂ)⁻¹)).congr
    (Eventually.of_forall fun _ ↦ by simp only [div_eq_mul_inv, mul_inv]; ring)

/-- **Olver's integral representation** for the Stirling remainder on the slit plane:
for `n ≥ 1` and `z ∈ slitPlane`,
`r_{n+1}(z) = -∫₀^∞ B_{2n}({u}) / (2n (u + z)^{2n}) du`. -/
theorem stirlingSeriesRemainder_succ_eq_neg_integral {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ slitPlane) :
    stirlingSeriesRemainder (n + 1) z =
      -∫ u in Ioi (0 : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  have hint := integrableOn_bernoulliFun_fract_div_two_mul_pow hn hz
  have hlim_rhs : Tendsto (fun N : ℕ ↦
      stirlingSeriesRemainder (n + 1) (z + N) -
        ∫ u in (0 : ℝ)..(N : ℝ),
          (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      atTop (𝓝 (-∫ u in Ioi (0 : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))) := by
    simpa using (tendsto_stirlingSeriesRemainder_add_natCast (n + 1) z).sub
      (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop)
  exact tendsto_nhds_unique tendsto_const_nhds
    (hlim_rhs.congr fun N ↦ (stirlingSeriesRemainder_succ_eq_sub_intervalIntegral hn hz N).symm)

/-- **Stirling's series with periodic Bernoulli remainder** on the slit plane (DLMF 5.11.1):
for `n ≥ 1` and `z ∈ slitPlane`,
`r_n(z) = ∫₀^∞ (B_{2n} - B_{2n}({u})) / (2n (u + z)^{2n}) du`. -/
theorem stirlingSeriesRemainder_eq_integral {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingSeriesRemainder n z =
      ∫ u in Ioi (0 : ℝ),
        (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
          ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  have h2n : 2 * n = (2 * n - 2) + 2 := by omega
  have hconst_int : IntegrableOn (fun u : ℝ ↦
      ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n))) (Ioi 0) :=
    (((integrableOn_Ioi_one_div_ofReal_add_pow hz (2 * n - 2)).congr_fun
      (fun u _ ↦ by rw [← h2n]) measurableSet_Ioi).const_mul
      (((bernoulli (2 * n) : ℝ) : ℂ) / (2 * n : ℂ))).congr
      (Eventually.of_forall fun _ ↦ by simp only [div_eq_mul_inv, mul_inv]; ring)
  have hper_int := integrableOn_bernoulliFun_fract_div_two_mul_pow hn hz
  have hterm : stirlingTerm n z =
      ∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
    have heq : (fun u : ℝ ↦
          ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n))) =
        fun u : ℝ ↦
          (((bernoulli (2 * n) : ℝ) : ℂ) / (2 * n : ℂ)) * (1 / ((u : ℂ) + z) ^ (2 * n)) := by
      ext u; simp only [div_eq_mul_inv, mul_inv]; ring
    have hsub : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    have hint_val : ∫ u in Ioi (0 : ℝ), 1 / ((u : ℂ) + z) ^ (2 * n) =
        1 / (((2 * n - 1 : ℕ) : ℂ) * z ^ (2 * n - 1)) := by
      simpa only [← h2n, hsub] using integral_Ioi_one_div_ofReal_add_pow hz (2 * n - 2)
    rw [heq, integral_const_mul, hint_val, stirlingTerm_def]
    have hc : ((2 * n - 1 : ℕ) : ℂ) = (2 * n : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; rfl
    rw [hc, Complex.ofReal_ratCast]; simp only [div_eq_mul_inv, mul_inv]; ring
  have hsplit : stirlingSeriesRemainder n z =
      stirlingTerm n z + stirlingSeriesRemainder (n + 1) z := by
    rw [stirlingSeriesRemainder_succ]; ring
  rw [hsplit, hterm, stirlingSeriesRemainder_succ_eq_neg_integral hn hz, ← sub_eq_add_neg,
    ← integral_sub hconst_int hper_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  push_cast; ring

/-! ### Differentiation under the integral sign -/

/-- Exact integral representation of every iterated derivative of the Stirling remainder on the
slit plane: for `n ≥ 1`, `k : ℕ`, and `z ∈ slitPlane`,
`r_n^{(k)}(z) = (-1)^k ((2n + k - 1)! / (2n)!) ∫₀^∞ (B_{2n} - B_{2n}({u})) / (u + z)^{2n + k} du`.
-/
theorem iteratedDeriv_stirlingSeriesRemainder {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv k (stirlingSeriesRemainder n) z =
      (-1 : ℂ) ^ k * (((2 * n + k - 1)! : ℂ) / ((2 * n)! : ℂ)) *
        ∫ u in Ioi (0 : ℝ),
          (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
            ((u : ℂ) + z) ^ (2 * n + k) := by
  induction k generalizing z with
  | zero =>
    rw [iteratedDeriv_zero, pow_zero, one_mul, add_zero, stirlingSeriesRemainder_eq_integral hn hz,
      ← integral_const_mul]
    have hfac : ((2 * n)! : ℂ) = (2 * n : ℂ) * ((2 * n - 1)! : ℂ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by omega : 2 * n ≠ 0)).symm
    have hne_fac : ((2 * n - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    refine setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ ?_
    rw [hfac]; field_simp
  | succ k ih =>
    let g : ℝ → ℂ := fun u ↦
      (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ)
    have hcpow (w : ℂ) (u : ℝ) (m : ℕ) :
        g u * ((u : ℂ) + w) ^ (-((m : ℕ) : ℂ)) = g u / ((u : ℂ) + w) ^ m := by
      rw [Complex.cpow_neg, Complex.cpow_natCast, div_eq_mul_inv]
    have hg_int :
        IntegrableOn (fun u : ℝ ↦ g u * ((u : ℂ) + z) ^ (-(((2 * n + k : ℕ) : ℂ)))) (Ioi 0) :=
      (integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi n (by omega : 2 ≤ 2 * n + k)
        hz).congr_fun (fun u _ ↦ (hcpow z u (2 * n + k)).symm) measurableSet_Ioi
    have hhd := hasDerivAt_integral_mul_ofReal_add_cpow hz hg_int
    have hfun :
        (fun w : ℂ ↦ ∫ u in Ioi (0 : ℝ), g u * ((u : ℂ) + w) ^ (-(((2 * n + k : ℕ) : ℂ)))) =
          fun w : ℂ ↦ ∫ u in Ioi (0 : ℝ), g u / ((u : ℂ) + w) ^ (2 * n + k) := by
      ext w
      exact setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ hcpow w u (2 * n + k)
    rw [hfun] at hhd
    have hev : iteratedDeriv k (stirlingSeriesRemainder n) =ᶠ[𝓝 z]
        fun w ↦ (-1 : ℂ) ^ k * (((2 * n + k - 1)! : ℂ) / ((2 * n)! : ℂ)) *
          ∫ u in Ioi (0 : ℝ), g u / ((u : ℂ) + w) ^ (2 * n + k) :=
      Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun _ hw ↦ ih hw
    rw [iteratedDeriv_succ, hev.deriv_eq, (hhd.const_mul _).deriv]
    have hs1 : -(((2 * n + k : ℕ) : ℂ)) - 1 = -(((2 * n + (k + 1) : ℕ) : ℂ)) := by
      push_cast; ring
    rw [hs1]
    have hint_eq :
        ∫ u in Ioi (0 : ℝ), g u * ((u : ℂ) + z) ^ (-(((2 * n + (k + 1) : ℕ) : ℂ))) =
          ∫ u in Ioi (0 : ℝ), g u / ((u : ℂ) + z) ^ (2 * n + (k + 1)) :=
      setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ hcpow z u (2 * n + (k + 1))
    rw [hint_eq]
    have hidx : 2 * n + (k + 1) - 1 = 2 * n + k := by omega
    have hfac : ((2 * n + (k + 1) - 1)! : ℂ) = ((2 * n + k : ℕ) : ℂ) * ((2 * n + k - 1)! : ℂ) := by
      rw [hidx]
      exact_mod_cast (Nat.mul_factorial_pred (by omega : 2 * n + k ≠ 0)).symm
    rw [hfac, pow_succ]
    ring

/-! ### Real-axis derivatives on `(0, ∞)` -/

/-- Every real Stirling remainder `realStirlingSeriesRemainder n` is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_realStirlingSeriesRemainder (n : ℕ) :
    ContDiffOn ℝ ∞ (realStirlingSeriesRemainder n) (Ioi 0) :=
  (differentiableOn_stirlingSeriesRemainder n).contDiffOn_ofReal isOpen_slitPlane
    (fun _ ht ↦ Complex.ofReal_mem_slitPlane.mpr ht)
    fun _ hx ↦ stirlingSeriesRemainder_ofReal n hx

/-- On `(0, ∞)`, every complex iterated derivative of `stirlingSeriesRemainder n` is the coercion
of the corresponding real iterated derivative of `realStirlingSeriesRemainder n`. -/
@[simp]
theorem iteratedDeriv_stirlingSeriesRemainder_ofReal (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (stirlingSeriesRemainder n) (x : ℂ) =
      ((iteratedDeriv k (realStirlingSeriesRemainder n) x : ℝ) : ℂ) :=
  (differentiableOn_stirlingSeriesRemainder n).iteratedDeriv_ofReal isOpen_slitPlane isOpen_Ioi
    (fun _ ht ↦ Complex.ofReal_mem_slitPlane.mpr ht)
    (fun _ ht ↦ stirlingSeriesRemainder_ofReal n ht) k hx

/-- Exact real integral representation for every iterated derivative of
`realStirlingSeriesRemainder n` on `(0, ∞)`: for `n ≥ 1`, `k : ℕ`, and `x > 0`,
`r_n^{(k)}(x) = (-1)^k ((2n + k - 1)! / (2n)!) ∫₀^∞ (B_{2n} - B_{2n}({u})) / (u + x)^{2n + k} du`.
-/
theorem iteratedDeriv_realStirlingSeriesRemainder {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    iteratedDeriv k (realStirlingSeriesRemainder n) x =
      (-1 : ℝ) ^ k * (((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
        ∫ u in Ioi (0 : ℝ),
          ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + x) ^ (2 * n + k) := by
  apply Complex.ofReal_injective
  rw [← iteratedDeriv_stirlingSeriesRemainder_ofReal n k hx,
    iteratedDeriv_stirlingSeriesRemainder hn k (Complex.ofReal_mem_slitPlane.mpr hx)]
  have hint :
      ∫ u in Ioi (0 : ℝ),
        (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
          ((u : ℂ) + (x : ℂ)) ^ (2 * n + k) =
      ((∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (u + x) ^ (2 * n + k) : ℝ) : ℂ) :=
    (setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ by push_cast; rfl).trans
      (integral_ofReal (𝕜 := ℂ))
  rw [hint]; push_cast; rfl

/-- Exact real integral representation of `realStirlingSeriesRemainder n` on `(0, ∞)` for
`n ≥ 1`. -/
theorem realStirlingSeriesRemainder_eq_integral {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    realStirlingSeriesRemainder n x =
      ∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          ((2 * n : ℝ) * (u + x) ^ (2 * n)) := by
  have h0 := iteratedDeriv_realStirlingSeriesRemainder hn 0 hx
  rw [iteratedDeriv_zero, pow_zero, one_mul, add_zero, ← integral_const_mul] at h0
  rw [h0]
  have hfac : ((2 * n)! : ℝ) = (2 * n : ℝ) * ((2 * n - 1)! : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : 2 * n ≠ 0)).symm
  have hne : ((2 * n - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ ?_
  rw [hfac]; field_simp

end TauCeti
