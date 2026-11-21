/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Basic

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The incomplete Beta function

The incomplete Beta function is the unnormalized integral
`B_x(a, b) = ∫ t in 0..x, t ^ (a - 1) * (1 - t) ^ (b - 1)` with real powers, for `a, b > 0` and
`0 ≤ x ≤ 1` ([DLMF 8.17.1](https://dlmf.nist.gov/8.17.E1)). Dividing by Euler's beta function
gives the regularized incomplete Beta function `I_x(a, b)` of
`TauCeti.regularizedIncompleteBeta`, through `TauCeti.regularizedIncompleteBeta_def_of_mem_Icc`
and `TauCeti.incompleteBeta_def`.

The substitution `u = 4 t (1 - t)` maps `[0, 1/2]` onto `[0, 1]` and turns the symmetric integrand
`t ^ (a - 1) * (1 - t) ^ (a - 1)` into a multiple of the integrand with parameters `a` and `1/2`.
This gives the quadratic transformation `I_x(a, a) = I_{4x(1-x)}(a, 1/2) / 2` for `x ≤ 1/2`.

At natural parameters the unit-step recurrence in the first parameter peels one negative binomial
weight off `I_x(m, n)` at a time, and the negative binomial series of `(1 - x) ^ (-n)` sums all of
them to `1`. Together they give `I_x(m, n) = (1 - x) ^ n * ∑_{j ≥ m} (n + j - 1).choose j * x ^ j`
for `0 ≤ x < 1`.

## Main definitions

* `TauCeti.incompleteBeta`: the incomplete Beta function `B_x(a, b)`.

## Main results

* `TauCeti.incompleteBeta_one_one`, `TauCeti.incompleteBeta_one_right` and
  `TauCeti.incompleteBeta_one_eq_beta`: the values `B_x(1, 1) = x`, `B_x(a, 1) = x ^ a / a` and
  `B_1(a, b) = Β(a, b)`;
* `TauCeti.incompleteBeta_one_half_four_mul_mul_one_sub`: the substitution
  `B_{4x(1-x)}(a, 1/2) = 4 ^ a * B_x(a, a)` for `0 ≤ x ≤ 1/2`;
* `TauCeti.regularizedIncompleteBeta_self_eq_regularizedIncompleteBeta_one_half_div_two`: the
  quadratic transformation, [DLMF 8.17.6](https://dlmf.nist.gov/8.17.E6);
* `TauCeti.inv_natCast_mul_beta_natCast`: `(m * Β(m, n))⁻¹ = (n + m - 1).choose m` for `m > 0`;
* `TauCeti.regularizedIncompleteBeta_natCast_eq_one_sub_sum_range`: the finite form
  `I_x(m, n) = 1 - (1 - x) ^ n * ∑_{j < m} (n + j - 1).choose j * x ^ j`;
* `TauCeti.hasSum_choose_mul_pow_regularizedIncompleteBeta`: the negative binomial series,
  [DLMF 8.17.24](https://dlmf.nist.gov/8.17.E24).

The quadratic substitution is adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/IncompleteGamma/Beta.lean`.

## References

* [NIST Digital Library of Mathematical Functions, §8.17](https://dlmf.nist.gov/8.17).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Nat

namespace TauCeti

variable {a b x : ℝ}

/-- The incomplete Beta function `B_x(a, b) = ∫ t in 0..x, t ^ (a - 1) * (1 - t) ^ (b - 1)`
([DLMF 8.17.1](https://dlmf.nist.gov/8.17.E1)), with real powers. It is meant for `a, b > 0` and
`0 ≤ x ≤ 1`, and elsewhere takes the value of the interval integral. -/
def incompleteBeta (a b x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, t ^ (a - 1) * (1 - t) ^ (b - 1)

/-- The defining interval integral of `TauCeti.incompleteBeta`. -/
theorem incompleteBeta_def (a b x : ℝ) :
    incompleteBeta a b x = ∫ t in (0 : ℝ)..x, t ^ (a - 1) * (1 - t) ^ (b - 1) := (rfl)

/-! ## Elementary values -/

/-- At both parameters `1` the integrand is `1`, and `B_x(1, 1) = x`. -/
theorem incompleteBeta_one_one : incompleteBeta 1 1 x = x := by
  simp [incompleteBeta_def]

/-- At second parameter `1` the integrand is a power, and `B_x(a, 1) = x ^ a / a`. At `a = 0`
both sides vanish: the integral of `t⁻¹` is not defined at `0`, and `x ^ 0 / 0 = 0`. -/
@[simp]
theorem incompleteBeta_one_right (ha : 0 ≤ a) : incompleteBeta a 1 x = x ^ a / a := by
  rw [incompleteBeta_def, sub_self]
  simp only [Real.rpow_zero, mul_one]
  rcases ha.eq_or_lt with rfl | ha
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [div_zero, intervalIntegral.integral_undef]
    simp_rw [zero_sub, Real.rpow_neg_one]
    simp [hx.symm]
  rw [integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow ha.ne', sub_zero]

/-- At `x = 1` the incomplete Beta function is Euler's beta function: `B_1(a, b) = Β(a, b)`.
When a parameter is `0` both sides vanish: the integrand is not integrable, and `Β` takes the
value `0` through `Γ(0) = 0`. -/
@[simp]
theorem incompleteBeta_one_eq_beta (ha : 0 ≤ a) (hb : 0 ≤ b) : incompleteBeta a b 1 = beta a b := by
  by_cases h : 0 < a ∧ 0 < b
  · exact integral_rpow_mul_one_sub_rpow h.1 h.2
  have hbeta : beta a b = 0 := by
    have h0 : a = 0 ∨ b = 0 := by
      by_contra! hne
      exact h ⟨ha.lt_of_ne' hne.1, hb.lt_of_ne' hne.2⟩
    rcases h0 with rfl | rfl <;> simp [ProbabilityTheory.beta]
  rw [hbeta, incompleteBeta_def, intervalIntegral.integral_undef]
  rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one,
    integrableOn_rpow_mul_one_sub_rpow_iff]

/-! ## The quadratic transformation -/

/-- The pointwise form of the substitution `u = 4 t (1 - t)`: on `(0, 1/2)` the integrand with
parameters `a` and `1/2` at `u`, times `du/dt = 4 (1 - 2 t)`, is `4 ^ a` times the symmetric
integrand at `t`. -/
private lemma rpow_mul_one_sub_rpow_four_mul_mul_one_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (4 * t * (1 - t)) ^ (a - 1) * (1 - 4 * t * (1 - t)) ^ ((1 / 2 : ℝ) - 1) * (4 * (1 - 2 * t)) =
      4 ^ a * (t ^ (a - 1) * (1 - t) ^ (a - 1)) := by
  have h2 : 0 < 1 - 2 * t := by linarith
  have h2' : 1 - t * 2 ≠ 0 := by linarith
  have hsq : 1 - 4 * t * (1 - t) = (1 - 2 * t) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    ring
  rw [hsq, ← Real.rpow_mul h2.le, Real.mul_rpow (by positivity) (by linarith),
    Real.mul_rpow (by norm_num) ht0.le, Real.rpow_sub_one four_ne_zero]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

/-- The substitution `u = 4 t (1 - t)` on `[0, x]`, for `0 ≤ x ≤ 1/2`:
`B_{4x(1-x)}(a, 1/2) = 4 ^ a * B_x(a, a)`. -/
theorem incompleteBeta_one_half_four_mul_mul_one_sub (ha : 0 < a) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 2) :
    incompleteBeta a (1 / 2) (4 * x * (1 - x)) = 4 ^ a * incompleteBeta a a x := by
  set f : ℝ → ℝ := fun t => 4 * t * (1 - t) with hf
  set g : ℝ → ℝ := fun u => u ^ (a - 1) * (1 - u) ^ ((1 / 2 : ℝ) - 1)
  have hae : ∀ᵐ t ∂(volume.restrict (uIcc 0 x)), (g ∘ f) t * (4 * (1 - 2 * t)) =
      4 ^ a * (t ^ (a - 1) * (1 - t) ^ (a - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_uIcc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ)),
      ae_restrict_of_ae (Measure.ae_ne volume (1 / 2 : ℝ))] with t ht h0 h12
    rw [uIcc_of_le hx0] at ht
    exact rpow_mul_one_sub_rpow_four_mul_mul_one_sub (lt_of_le_of_ne ht.1 (Ne.symm h0))
      (lt_of_le_of_ne (ht.2.trans hx1) h12)
  have hI : IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (a - 1)) volume 0 x :=
    intervalIntegrable_rpow_mul_one_sub_rpow ha ha ⟨le_rfl, zero_le_one⟩ ⟨hx0, by linarith⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv''' (a := 0) (b := x) (f := f)
    (f' := fun t => 4 * (1 - 2 * t)) (g := g) (by fun_prop)
    (fun t _ => ((((hasDerivAt_id' t).const_mul 4).mul
      ((hasDerivAt_id' t).const_sub 1)).congr_deriv (by ring)).hasDerivWithinAt)
    ?_ ?_ ?_
  · simp only [hf, mul_zero, zero_mul] at hsub
    rw [incompleteBeta_def, incompleteBeta_def, ← hsub, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hx0]
    have := (ae_restrict_iff' (measurableSet_uIcc (a := (0 : ℝ)) (b := x))).mp hae
    filter_upwards [this] with t ht hmem
    exact ht (by rw [uIcc_of_le hx0]; exact Ioc_subset_Icc_self hmem)
  · rintro u ⟨t, ht, rfl⟩
    rw [min_eq_left hx0, max_eq_right hx0] at ht
    have hu0 : f t ≠ 0 := (mul_pos (mul_pos four_pos ht.1) (by linarith [ht.2])).ne'
    have hu1 : 1 - f t ≠ 0 := by
      simp only [hf]
      nlinarith [ht.1, ht.2]
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hu0)).mul
      ((Real.continuousAt_rpow_const _ _ (Or.inl hu1)).comp
        (continuousAt_const.sub continuousAt_id))).continuousWithinAt
  · have h01 : IntervalIntegrable g volume 0 1 :=
      intervalIntegrable_rpow_mul_one_sub_rpow ha (by norm_num : (0 : ℝ) < 1 / 2)
        ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    have h01' : IntegrableOn g (Icc 0 1) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h01
    refine h01'.mono_set ?_
    rintro u ⟨t, ht, rfl⟩
    rw [uIcc_of_le hx0] at ht
    simp only [hf]
    constructor <;> nlinarith [ht.1, ht.2]
  · have h := ((intervalIntegrable_iff_integrableOn_Icc_of_le hx0).mp hI).const_mul (4 ^ a)
    rw [← uIcc_of_le hx0] at h
    exact Integrable.congr h (by filter_upwards [hae] with t ht using ht.symm)

/-- The quadratic transformation of the symmetric regularized incomplete Beta function,
`I_x(a, a) = I_{4x(1-x)}(a, 1/2) / 2` for `x ≤ 1/2`
([DLMF 8.17.6](https://dlmf.nist.gov/8.17.E6)). DLMF states it for `0 ≤ x ≤ 1/2`; for `x < 0`
both sides are `0`, because `4x(1-x) < 0` too. -/
theorem regularizedIncompleteBeta_self_eq_regularizedIncompleteBeta_one_half_div_two
    (ha : 0 < a) (hx1 : x ≤ 1 / 2) :
    regularizedIncompleteBeta a a x =
      regularizedIncompleteBeta a (1 / 2) (4 * x * (1 - x)) / 2 := by
  rcases lt_or_ge x 0 with hx | hx0
  · have hy : 4 * x * (1 - x) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    rw [regularizedIncompleteBeta_eq_zero_of_neg _ _ hx,
      regularizedIncompleteBeta_eq_zero_of_neg _ _ hy, zero_div]
  have hy : 4 * x * (1 - x) ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  rw [regularizedIncompleteBeta_def_of_mem_Icc ha ha ⟨hx0, by linarith⟩,
    regularizedIncompleteBeta_def_of_mem_Icc ha hh hy, ← incompleteBeta_def,
    ← incompleteBeta_def, incompleteBeta_one_half_four_mul_mul_one_sub ha hx0 hx1,
    beta_comm a (1 / 2), beta_one_half_left_eq_two_rpow_mul_beta_self]
  have h4 : (4 : ℝ) ^ a = 2 ^ (2 * a - 1) * 2 := by
    rw [← Real.rpow_add_one two_ne_zero, sub_add_cancel, Real.rpow_mul zero_le_two]
    norm_num
  have hB := (beta_pos ha ha).ne'
  have h2 : (2 : ℝ) ^ (2 * a - 1) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
  rw [h4]
  field_simp

/-! ## The negative binomial series -/

/-- At natural parameters `m > 0` and `n`, the normalizing factor of the unit-step recurrence
`TauCeti.regularizedIncompleteBeta_add_one_left` is a binomial coefficient:
`(m * Β(m, n))⁻¹ = (n + m - 1).choose m`. At `n = 0` both sides are `0`. -/
theorem inv_natCast_mul_beta_natCast {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ((m : ℝ) * beta m n)⁻¹ = ((n + m - 1).choose m : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rcases n with _ | k
  · simp [ProbabilityTheory.beta]
  have hchoose := Nat.add_choose_mul_factorial_mul_factorial k (j + 1)
  have h1 : Real.Gamma ((j + 1 : ℕ) : ℝ) = j ! := by
    rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]
  have h2 : Real.Gamma ((k + 1 : ℕ) : ℝ) = k ! := by
    rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]
  have h3 : Real.Gamma (((j + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ)) = (k + (j + 1))! := by
    rw [show ((j + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) = ((k + (j + 1) : ℕ) : ℝ) + 1 by
      push_cast; ring, Real.Gamma_nat_eq_factorial]
  rw [ProbabilityTheory.beta, h1, h2, h3, show k + 1 + (j + 1) - 1 = k + (j + 1) by omega,
    ← hchoose, Nat.factorial_succ]
  push_cast
  field_simp

/-- At natural parameters with `0 < n`, the regularized incomplete Beta function is one minus
the first `m` negative binomial weights:
`I_x(m, n) = 1 - (1 - x) ^ n * ∑_{j < m} (n + j - 1).choose j * x ^ j` for `0 ≤ x ≤ 1`. At
`m = 0` this is the boundary value `I_x(0, n) = 1`. -/
theorem regularizedIncompleteBeta_natCast_eq_one_sub_sum_range {m n : ℕ} (hn : 0 < n)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta m n x =
      1 - ∑ j ∈ Finset.range m, (1 - x) ^ n * ((n + j - 1).choose j : ℝ) * x ^ j := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero =>
    rw [Nat.cast_zero, regularizedIncompleteBeta_zero_left (by positivity) hx0]
    simp
  | succ m ih =>
    rcases m.eq_zero_or_pos with rfl | hm
    · rw [Nat.cast_one, regularizedIncompleteBeta_one_left (by positivity) hx0 hx1,
        Real.rpow_natCast]
      simp
    have hstep := regularizedIncompleteBeta_add_one_left (a := m) (b := (k + 1 : ℕ)) (x := x)
      (by positivity) (by positivity) hx0 hx1
    rw [Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv,
      inv_natCast_mul_beta_natCast hm] at hstep
    rw [Nat.cast_succ, hstep, ih, Finset.sum_range_succ]
    ring

/-- The negative binomial series for the regularized incomplete Beta function at natural
parameters, `I_x(m, n) = (1 - x) ^ n * ∑_{j ≥ m} (n + j - 1).choose j * x ^ j` for `0 < n` and
`0 ≤ x < 1` ([DLMF 8.17.24](https://dlmf.nist.gov/8.17.E24)), with the summation index shifted
to start at `0`. DLMF states it for `m > 0`; at `m = 0` it is the negative binomial series of
`(1 - x) ^ (-n)` together with the boundary value `I_x(0, n) = 1`. -/
theorem hasSum_choose_mul_pow_regularizedIncompleteBeta {m n : ℕ} (hn : 0 < n) (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    HasSum (fun j => (1 - x) ^ n * ((n + (j + m) - 1).choose (j + m) : ℝ) * x ^ (j + m))
      (regularizedIncompleteBeta m n x) := by
  rw [regularizedIncompleteBeta_natCast_eq_one_sub_sum_range hn hx0 hx1.le,
    hasSum_nat_add_iff' (f := fun j => (1 - x) ^ n * ((n + j - 1).choose j : ℝ) * x ^ j) m]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k
    (by rwa [Real.norm_of_nonneg hx0] : ‖x‖ < 1)).mul_left ((1 - x) ^ (k + 1))
  have hx : (1 - x) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by linarith)
  rw [mul_one_div_cancel hx] at h
  convert h using 2 with j
  rw [show k + 1 + j - 1 = j + k by omega, Nat.choose_symm_add]
  ring

end TauCeti
