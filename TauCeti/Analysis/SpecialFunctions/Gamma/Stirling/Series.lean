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
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Integrals.HalfLineRational
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral
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
theorem stirlingTerm_one {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 1 z = 1 / (12 * z) := by
  simp only [stirlingTerm_def, Nat.mul_one, bernoulli_two, Rat.cast_inv, Rat.cast_ofNat,
    Nat.cast_one]
  ring

/-- The second Stirling term is `-1 / (360 z³)`. -/
theorem stirlingTerm_two {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 2 z = -(1 / (360 * z ^ 3)) := by
  simp only [stirlingTerm_def, show 2 * 2 = 4 by rfl, show 4 - 1 = 3 by rfl, bernoulli_four,
    Rat.cast_neg, Rat.cast_inv, Rat.cast_ofNat, Nat.cast_ofNat]
  ring

/-- The third Stirling term is `1 / (1260 z⁵)`. -/
theorem stirlingTerm_three {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (z : 𝕜) :
    stirlingTerm 3 z = 1 / (1260 * z ^ 5) := by
  simp only [stirlingTerm_def, show 2 * 3 = 6 by rfl, show 6 - 1 = 5 by rfl, bernoulli_six,
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

/-! ### Integrability of periodic Bernoulli kernels -/

/-- Integrability of the periodic Bernoulli integrand `(B_{2n} - B_{2n}({u})) / (u + z)^k` on
`(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
        ((u : ℂ) + z) ^ k) (Ioi 0) := by
  let g : ℝ → ℂ := fun u ↦
    (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ)
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.sub (measurable_bernoulliFun_fract (2 * n)))).aestronglyMeasurable
  have hg_bdd : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ‖g u‖ ≤ 2 * |(bernoulli (2 * n) : ℝ)| :=
    Eventually.of_forall fun u ↦ by
      have htri : |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)| ≤
          |(bernoulli (2 * n) : ℝ)| + |bernoulliFun (2 * n) (Int.fract u)| := by
        simpa using abs_sub_le (bernoulli (2 * n) : ℝ) 0 (bernoulliFun (2 * n) (Int.fract u))
      have hle : |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)| ≤
          2 * |(bernoulli (2 * n) : ℝ)| := by
        linarith [abs_bernoulliFun_even_fract_le n u]
      simpa only [g, Complex.norm_real, Real.norm_eq_abs] using hle
  have hs : (-(k : ℂ)).re < -1 := by
    simp only [Complex.neg_re, Complex.natCast_re]
    exact_mod_cast (by omega : -(k : ℤ) < -1)
  refine (integrableOn_mul_ofReal_add_cpow_of_norm_le hg_meas hg_bdd hz hs).congr_fun
    (fun u _ ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [Complex.cpow_neg, Complex.cpow_natCast, div_eq_mul_inv]

/-- Integrability of Olver's periodic Bernoulli integrand `B_{2n}({u}) / (u + z)^k` on `(0, ∞)`
for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulliFun_fract_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((u : ℂ) + z) ^ k) (Ioi 0) := by
  let g : ℝ → ℂ := fun u ↦ (bernoulliFun (2 * n) (Int.fract u) : ℂ)
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_bernoulliFun_fract (2 * n))).aestronglyMeasurable
  have hg_bdd : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ‖g u‖ ≤ |(bernoulli (2 * n) : ℝ)| :=
    Eventually.of_forall fun u ↦ by
      simpa [g, Complex.norm_real, Real.norm_eq_abs] using abs_bernoulliFun_even_fract_le n u
  have hs : (-(k : ℂ)).re < -1 := by
    simp only [Complex.neg_re, Complex.natCast_re]
    exact_mod_cast (by omega : -(k : ℤ) < -1)
  refine (integrableOn_mul_ofReal_add_cpow_of_norm_le hg_meas hg_bdd hz hs).congr_fun
    (fun u _ ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [Complex.cpow_neg, Complex.cpow_natCast, div_eq_mul_inv]

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
    rw [show π - π / 2 = π / 2 by ring, Complex.abs_arg_le_pi_div_two_iff]; exact hre.le
  have hbound := norm_stirlingRemainder_le_of_abs_arg_le (z := z + N) (δ := π / 2)
    Real.pi_div_two_pos harg hne
  rw [← stirlingSeriesRemainder_one_eq_stirlingRemainder] at hbound
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
    refine ((Complex.hasDerivAt_log hmem).comp u hlin).congr_deriv ?_
    simp [logAddDeriv]
  | succ i =>
    refine (HasDerivAt.const_div_pow hlin hne ((-1 : ℂ) ^ i * (i ! : ℂ)) (i + 1)).congr_deriv ?_
    simp only [logAddDeriv, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

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
    have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + z) 1 u := by
      simpa using (hasDerivAt_id (u : ℂ)).comp_ofReal.add_const z
    refine ((hlin.mul ((Complex.hasDerivAt_log hmem).comp u hlin)).sub hlin).congr_deriv ?_
    simp [mul_inv_cancel₀ (slitPlane_ne_zero hmem)]
  simpa [add_comm] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuousOn_logAddDeriv hz 0 N).intervalIntegrable_of_Icc (Nat.cast_nonneg N))

/-- Finite-truncation identity from Euler–Maclaurin of order `2n` applied to `u ↦ log (u + z)`. -/
private theorem stirlingSeriesRemainder_succ_eq_sub_intervalIntegral {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ slitPlane) (N : ℕ) :
    stirlingSeriesRemainder (n + 1) z = stirlingSeriesRemainder (n + 1) (z + N) -
      ∫ u in (0 : ℝ)..(N : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  -- Identify the finite sum via `logGamma_add_natCast`.
  have hsum_lhs : ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), logAddDeriv z 0 (j : ℝ) =
      logGamma (z + N) + Complex.log (z + N) - logGamma z := by
    rw [Int.Icc_eq_finset_map, show ((N : ℤ) + 1 - 0).toNat = N + 1 by omega, Finset.sum_map]
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
      zero_add, Int.cast_natCast, logAddDeriv, Complex.ofReal_natCast, add_comm _ z,
      Finset.sum_range_succ]
    rw [logGamma_add_natCast hz N]
    ring
  have hint2n : IntervalIntegrable (logAddDeriv z (2 * n)) volume (0 : ℤ) (N : ℤ) := by
    simpa using (continuousOn_logAddDeriv hz (2 * n) N).intervalIntegrable_of_Icc
      (Nat.cast_nonneg N)
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := logAddDeriv z)
    (a := (0 : ℤ)) (n := (N : ℤ)) (Nat.cast_nonneg N) (k := 2 * n) (by omega)
    (fun i _ ↦ by simpa using continuousOn_logAddDeriv hz i N)
    (fun i _ u hu ↦ hasDerivAt_logAddDeriv hz i (by simpa using hu.1.le))
    hint2n
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
      rw [show 2 * j - 2 = 2 * (j - 1) by omega, pow_mul, neg_one_sq, one_pow]
    have hfac : ((2 * j)! : ℂ) = (2 * j : ℂ) * (2 * j - 1 : ℂ) * ((2 * j - 2)! : ℂ) := by
      have hnat : (2 * j)! = (2 * j) * ((2 * j - 1) * (2 * j - 2)!) := by
        rw [show 2 * j - 2 = (2 * j - 1) - 1 by omega,
          Nat.mul_factorial_pred (by omega), Nat.mul_factorial_pred (by omega)]
      have hc : ((2 * j - 1 : ℕ) : ℂ) = (2 * j : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]; push_cast; rfl
      have hcast : ((2 * j)! : ℂ) =
          (2 * j : ℂ) * ((2 * j - 1 : ℕ) : ℂ) * ((2 * j - 2)! : ℂ) := by
        rw [← mul_assoc] at hnat; exact_mod_cast hnat
      rw [hcast, hc]
    have hterm : ∀ w : ℝ, (bernoulli (2 * j) / ((2 * j)! : ℝ) : ℝ) • logAddDeriv z (2 * j - 1) w =
        stirlingTerm j (z + w) := by
      intro w
      rw [Complex.real_smul, hsub1, logAddDeriv, heven_pow, one_mul, ← hsub1, stirlingTerm_def]
      push_cast
      rw [hfac, add_comm (w : ℂ) z]
      have hne_fac : ((2 * j - 2)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    rw [smul_sub, hterm (N : ℝ), hterm 0]; simp
  -- Simplify the remainder integral in `hEM`.
  have hrem_int :
      ((-1 : ℝ) ^ (2 * n) / ((2 * n)! : ℝ)) •
        ∫ u in (0 : ℝ)..(N : ℝ), bernoulliFun (2 * n) (Int.fract u) • logAddDeriv z (2 * n) u =
      -∫ u in (0 : ℝ)..(N : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
    have hsub1 : 2 * n = (2 * n - 1) + 1 := by omega
    have hodd_pow : (-1 : ℂ) ^ (2 * n - 1) = -1 := Odd.neg_one_pow ⟨n - 1, by omega⟩
    have heven_pow : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
    have hfac : ((2 * n)! : ℂ) = (2 * n : ℂ) * ((2 * n - 1)! : ℂ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by omega : 2 * n ≠ 0)).symm
    rw [heven_pow, ← intervalIntegral.integral_smul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    rw [Complex.real_smul, Complex.real_smul, hsub1, logAddDeriv, hodd_pow, ← hsub1]
    push_cast
    rw [hfac]
    have hne_fac : ((2 * n - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  -- Assemble the finite Euler–Maclaurin identity.
  simp only [Int.cast_zero, Int.cast_natCast] at hEM
  rw [hsum_lhs, hbern_sum, hrem_int, sub_neg_eq_add,
    show ∫ u in (0 : ℝ)..(N : ℝ), logAddDeriv z 0 u =
      ((z + N) * Complex.log (z + N) - (z + N)) - (z * Complex.log z - z) from
      integral_log_ofReal_add hz N] at hEM
  simp only [logAddDeriv, Complex.ofReal_zero, zero_add, Complex.ofReal_natCast,
    add_comm (N : ℂ) z, Complex.real_smul] at hEM
  simp only [stirlingSeriesRemainder_def, stirlingRemainder_def,
    Finset.Ico_add_one_right_eq_Icc, Finset.sum_sub_distrib] at hEM ⊢
  push_cast at hEM ⊢
  linear_combination -hEM

/-- **Olver's integral representation** for the Stirling remainder on the slit plane:
for `n ≥ 1` and `z ∈ slitPlane`,
`r_{n+1}(z) = -∫₀^∞ B_{2n}({u}) / (2n (u + z)^{2n}) du`. -/
theorem stirlingSeriesRemainder_succ_eq_neg_integral {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ slitPlane) :
    stirlingSeriesRemainder (n + 1) z =
      -∫ u in Ioi (0 : ℝ),
        (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
  have hint : IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      (Ioi 0) :=
    ((integrableOn_bernoulliFun_fract_div_pow_Ioi n (by omega : 2 ≤ 2 * n) hz).const_mul
      ((2 * n : ℂ)⁻¹)).congr
      (Eventually.of_forall fun _ ↦ by simp only [div_eq_mul_inv, mul_inv]; ring)
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
  have hper_int : IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)))
      (Ioi 0) :=
    ((integrableOn_bernoulliFun_fract_div_pow_Ioi n (by omega : 2 ≤ 2 * n) hz).const_mul
      ((2 * n : ℂ)⁻¹)).congr
      (Eventually.of_forall fun _ ↦ by simp only [div_eq_mul_inv, mul_inv]; ring)
  have hterm : stirlingTerm n z =
      ∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n)) := by
    have heq : (fun u : ℝ ↦
          ((bernoulli (2 * n) : ℝ) : ℂ) / ((2 * n : ℂ) * ((u : ℂ) + z) ^ (2 * n))) =
        fun u : ℝ ↦
          (((bernoulli (2 * n) : ℝ) : ℂ) / (2 * n : ℂ)) * (1 / ((u : ℂ) + z) ^ (2 * n)) := by
      ext u; simp only [div_eq_mul_inv, mul_inv]; ring
    have hint_val : ∫ u in Ioi (0 : ℝ), 1 / ((u : ℂ) + z) ^ (2 * n) =
        1 / (((2 * n - 1 : ℕ) : ℂ) * z ^ (2 * n - 1)) := by
      simpa only [← h2n, show 2 * n - 2 + 1 = 2 * n - 1 by omega] using
        integral_Ioi_one_div_ofReal_add_pow hz (2 * n - 2)
    rw [heq, integral_const_mul, hint_val, stirlingTerm_def]
    have hc : ((2 * n - 1 : ℕ) : ℂ) = (2 * n : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; rfl
    rw [hc, Complex.ofReal_ratCast]; simp only [div_eq_mul_inv, mul_inv]; ring
  rw [show stirlingSeriesRemainder n z = stirlingTerm n z + stirlingSeriesRemainder (n + 1) z by
      rw [stirlingSeriesRemainder_succ]; ring,
    hterm, stirlingSeriesRemainder_succ_eq_neg_integral hn hz, ← sub_eq_add_neg,
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
    have hfac : ((2 * n + (k + 1) - 1)! : ℂ) = ((2 * n + k : ℕ) : ℂ) * ((2 * n + k - 1)! : ℂ) := by
      rw [show 2 * n + (k + 1) - 1 = 2 * n + k by omega]
      exact_mod_cast (Nat.mul_factorial_pred (by omega : 2 * n + k ≠ 0)).symm
    rw [hfac, pow_succ]
    ring

end TauCeti
