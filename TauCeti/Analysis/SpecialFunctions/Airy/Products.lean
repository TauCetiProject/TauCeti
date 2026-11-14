/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Gamma.Multiplication
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Products of Airy functions: Nicholson's integral for `Ai(z)² + Bi(z)²`

The sum of squares `Ai(z)² + Bi(z)²` admits the everywhere-convergent Laplace-type integral
representation

$$
\operatorname{Ai}(z)^2 + \operatorname{Bi}(z)^2 =
  \pi^{-3/2} \int_0^\infty \exp\!\left(z t - \frac{t^3}{12}\right) t^{-1/2}\,dt
$$

(DLMF 9.11.4), together with the power series

$$
\operatorname{Ai}(z)^2 + \operatorname{Bi}(z)^2 =
  \frac{\pi^{-3/2}}{3} \sum_{n=0}^\infty
    12^{(n + 1/2)/3}\,\Gamma\!\left(\frac{n + 1/2}{3}\right) \frac{z^n}{n!}.
$$

Expanding `Ai(z)² + Bi(z)²` from the defining `₀F₁` representations cancels the odd cross terms in
`√3` and leaves three Cauchy products of regularized `₀F₁` series at `z³ / 9`. Combining Legendre's
duplication formula and Gauss's triplication formula identifies the three residue-class subseries
modulo `3` with the termwise Gamma moments of `exp(z t - t³ / 12) t^{-1/2}` on `(0, ∞)`.

## Main results

* `TauCeti.airyAi_sq_add_airyBi_sq_eq_regularizedHGFun` — `Ai(z)² + Bi(z)²` expressed through
  products of `₀F₁(; 2/3; z³ / 9)` and `₀F₁(; 4/3; z³ / 9)`.
* `TauCeti.integrableOn_exp_mul_sub_cube_div_twelve_mul_rpow`,
  `TauCeti.integrableOn_cexp_mul_sub_cube_div_twelve_mul_cpow` — absolute integrability of
  `t ↦ exp(z t - t³ / 12) t^w` on `(0, ∞)` for `Re w > -1`.
* `TauCeti.integral_cexp_neg_cube_div_twelve_mul_cpow`,
  `TauCeti.hasSum_integral_cexp_mul_sub_cube_div_twelve_mul_cpow` — Gamma moment evaluation and
  power-series expansion of the weighted cubic-exponential Laplace integral for `Re w > -1`.
* `TauCeti.airyAi_sq_add_airyBi_sq_eq_integral` — Nicholson's integral representation of
  `Ai(z)² + Bi(z)²` (DLMF 9.11.4).
* `TauCeti.hasSum_airyAi_sq_add_airyBi_sq`, `TauCeti.summable_norm_airyAi_sq_add_airyBi_sq` — the
  everywhere-convergent Maclaurin series of `Ai(z)² + Bi(z)²`.
* `TauCeti.iteratedDeriv_airyAi_sq_add_airyBi_sq_eq_integral`,
  `TauCeti.deriv_airyAi_sq_add_airyBi_sq_eq_integral` — higher derivatives of `Ai(z)² + Bi(z)²` as
  moments of the cubic-exponential kernel.
* `TauCeti.four_mul_airyAi_zero_sq` — DLMF 9.11.4 at `z = 0`:
  `4 Ai(0)² = π^{-3/2} 12^{1/6} Γ(1/6) / 3`.
* `TauCeti.airyAi_sq_add_airyBi_sq_ofReal_eq_integral`,
  `TauCeti.airyAi_sq_add_airyBi_sq_ofReal_re_pos`,
  `TauCeti.airyAi_sq_add_airyBi_sq_ofReal_ne_zero` — reality and strict positivity of
  `Ai(x)² + Bi(x)²` along the real axis.

## References

* NIST Digital Library of Mathematical Functions, §9.11, <https://dlmf.nist.gov/9.11>.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Hypergeometric product decomposition of `Ai(z)² + Bi(z)²` -/

/-- The sum of squares `Ai(z)² + Bi(z)²` in terms of the regularized `₀F₁` functions at `z³ / 9`. -/
theorem airyAi_sq_add_airyBi_sq_eq_regularizedHGFun (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) ^ 2 +
      (4 / 9 : ℂ) * z *
        (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
          regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) +
      4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
        regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) ^ 2 := by
  have hthree : (3 : ℂ) ≠ 0 := by norm_num
  have h1 : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) = (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    rw [← cpow_add _ _ hthree]; norm_num
  have h2 : (3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-1 / 6 : ℂ) = 3 * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    rw [← cpow_add _ _ hthree, show (-1 / 6 : ℂ) + (-1 / 6) = -4 / 3 + 1 by norm_num,
      cpow_add _ _ hthree, cpow_one, mul_comm]
  have h3 : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) = 1 / 9 := by
    rw [← cpow_add _ _ hthree, show (-2 / 3 : ℂ) + (-4 / 3) = -(2 : ℕ) by norm_num,
      cpow_neg, cpow_natCast]; norm_num
  have h4 : (3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-5 / 6 : ℂ) = 1 / 3 := by
    rw [← cpow_add _ _ hthree, show (-1 / 6 : ℂ) + (-5 / 6) = -1 by norm_num, cpow_neg_one]
    norm_num
  have h5 : (3 : ℂ) ^ (-4 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) = (3 : ℂ) ^ (-8 / 3 : ℂ) := by
    rw [← cpow_add _ _ hthree]; norm_num
  have h6 : (3 : ℂ) ^ (-5 / 6 : ℂ) * (3 : ℂ) ^ (-5 / 6 : ℂ) = 3 * (3 : ℂ) ^ (-8 / 3 : ℂ) := by
    rw [← cpow_add _ _ hthree, show (-5 / 6 : ℂ) + (-5 / 6) = -8 / 3 + 1 by norm_num,
      cpow_add _ _ hthree, cpow_one, mul_comm]
  rw [airyAi_def, airyBi_def]
  set F₁ := regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
  set F₂ := regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)
  linear_combination
    F₁ ^ 2 * h1 + F₁ ^ 2 * h2 - 2 * z * F₁ * F₂ * h3 + 2 * z * F₁ * F₂ * h4 +
      z ^ 2 * F₂ ^ 2 * h5 + z ^ 2 * F₂ ^ 2 * h6

/-- At the origin, `Bi(0)² = 3 Ai(0)²`, so `Ai(0)² + Bi(0)² = 4 Ai(0)²`. -/
theorem airyAi_zero_sq_add_airyBi_zero_sq :
    airyAi 0 ^ 2 + airyBi 0 ^ 2 = 4 * airyAi 0 ^ 2 := by
  have h1 : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) = (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    rw [← cpow_add _ _ (by norm_num)]; norm_num
  have h2 : (3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-1 / 6 : ℂ) = 3 * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    rw [← cpow_add _ _ (by norm_num), show (-1 / 6 : ℂ) + (-1 / 6) = -4 / 3 + 1 by norm_num,
      cpow_add _ _ (by norm_num), cpow_one, mul_comm]
  rw [airyAi_zero, airyBi_zero]
  simp only [div_pow]
  linear_combination ((Gamma (2 / 3)) ^ 2)⁻¹ * (h2 - 3 * h1)

/-! ### Duplication–triplication Gamma identity for the series coefficients -/

private theorem real_gamma_duplication_triplication_coeff {s : ℝ} (hs : 0 < s) :
    4 * (3 : ℝ) ^ (-2 * s - 1) * Real.Gamma (2 * s) /
        (Real.Gamma (s + 1 / 6) * Real.Gamma (s + 1 / 2) ^ 2 * Real.Gamma (s + 5 / 6)) =
      Real.pi ^ (-3 / 2 : ℝ) * ((12 : ℝ) ^ s * Real.Gamma s / 3) /
        Real.Gamma (3 * s + 1 / 2) := by
  have hdup := Real.Gamma_mul_Gamma_add_half s
  have htrip : Real.Gamma (s + 1 / 6) * Real.Gamma (s + 1 / 2) * Real.Gamma (s + 5 / 6) =
      2 * Real.pi * (3 : ℝ) ^ (-3 * s) * Real.Gamma (3 * s + 1 / 2) := by
    have h := Real.prod_Gamma_add_div (m := 3) (by norm_num) (s + 1 / 6)
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one, zero_div, add_zero] at h
    rw [show ((3 : ℝ) - 1) / 2 = 1 by norm_num, Real.rpow_one] at h
    convert h using 2 <;> ring_nf
  have h12 : (12 : ℝ) ^ s = (2 : ℝ) ^ (2 * s) * (3 : ℝ) ^ s := by
    rw [show (12 : ℝ) = 2 ^ (2 : ℝ) * 3 by norm_num, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul zero_le_two]
  have h2pow : (2 : ℝ) ^ (1 - 2 * s) * (2 : ℝ) ^ (2 * s) = 2 := by
    rw [← Real.rpow_add two_pos, show (1 - 2 * s) + 2 * s = 1 by ring, Real.rpow_one]
  have h3pow : (3 : ℝ) ^ (-2 * s - 1) * 3 = (3 : ℝ) ^ s * (3 : ℝ) ^ (-3 * s) := by
    rw [← Real.rpow_add_one (by positivity), ← Real.rpow_add (by positivity)]
    congr 1; ring
  have hpipow : Real.pi ^ (-3 / 2 : ℝ) * Real.pi * √Real.pi = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one Real.pi_pos.ne', ← Real.rpow_add Real.pi_pos]
    norm_num
  have : 0 < Real.Gamma (s + 1 / 6) := Real.Gamma_pos_of_pos (by linarith)
  have : 0 < Real.Gamma (s + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have : 0 < Real.Gamma (s + 5 / 6) := Real.Gamma_pos_of_pos (by linarith)
  have hG3s : 0 < Real.Gamma (3 * s + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  rw [div_eq_div_iff (by positivity) hG3s.ne']
  have hprod : Real.Gamma (s + 1 / 6) * Real.Gamma (s + 1 / 2) ^ 2 * Real.Gamma (s + 5 / 6) =
      Real.Gamma (s + 1 / 2) * (2 * Real.pi * (3 : ℝ) ^ (-3 * s) * Real.Gamma (3 * s + 1 / 2)) := by
    linear_combination Real.Gamma (s + 1 / 2) * htrip
  rw [hprod, h12]
  calc 4 * (3 : ℝ) ^ (-2 * s - 1) * Real.Gamma (2 * s) * Real.Gamma (3 * s + 1 / 2)
      = 4 * (3 : ℝ) ^ (-2 * s - 1) * Real.Gamma (2 * s) * Real.Gamma (3 * s + 1 / 2) *
          ((Real.pi ^ (-3 / 2 : ℝ) * Real.pi * √Real.pi) *
            ((2 : ℝ) ^ (1 - 2 * s) * (2 : ℝ) ^ (2 * s) / 2)) := by
          rw [hpipow, h2pow]; ring
    _ = 2 * ((3 : ℝ) ^ (-2 * s - 1) * 3) / 3 *
          (Real.Gamma (2 * s) * (2 : ℝ) ^ (1 - 2 * s) * √Real.pi) *
          (Real.pi ^ (-3 / 2 : ℝ) * Real.pi * (2 : ℝ) ^ (2 * s) * Real.Gamma (3 * s + 1 / 2)) := by
          ring
    _ = Real.pi ^ (-3 / 2 : ℝ) * ((2 : ℝ) ^ (2 * s) * (3 : ℝ) ^ s * Real.Gamma s / 3) *
          (Real.Gamma (s + 1 / 2) *
            (2 * Real.pi * (3 : ℝ) ^ (-3 * s) * Real.Gamma (3 * s + 1 / 2))) := by
          rw [h3pow, ← hdup]; ring

private theorem complex_gamma_duplication_triplication_coeff {s : ℝ} (hs : 0 < s) :
    4 * (3 : ℂ) ^ (-2 * (s : ℂ) - 1) * Gamma (2 * (s : ℂ)) /
        (Gamma ((s : ℂ) + 1 / 6) * Gamma ((s : ℂ) + 1 / 2) ^ 2 * Gamma ((s : ℂ) + 5 / 6)) =
      (π : ℂ) ^ (-3 / 2 : ℂ) * ((12 : ℂ) ^ (s : ℂ) * Gamma s / 3) /
        Gamma (3 * (s : ℂ) + 1 / 2) := by
  have h := congrArg ((↑) : ℝ → ℂ) (real_gamma_duplication_triplication_coeff hs)
  simp only [ofReal_div, ofReal_mul, ofReal_pow, ofReal_ofNat, ← Gamma_ofReal] at h
  rw [ofReal_cpow (by positivity : (0 : ℝ) ≤ 3), ofReal_cpow Real.pi_pos.le,
    ofReal_cpow (by positivity : (0 : ℝ) ≤ 12)] at h
  push_cast at h
  exact h

private theorem ascPochhammer_eval_eq_Gamma_div {a : ℝ} (ha : 0 < a) (m : ℕ) :
    (ascPochhammer ℂ m).eval ((a : ℂ) + m) =
      Gamma ((a : ℂ) + 2 * m) / Gamma ((a : ℂ) + m) := by
  have hne : ∀ k : ℕ, (a : ℂ) + m ≠ -k :=
    ne_neg_natCast_of_re_pos (by
      simp only [add_re, ofReal_re, natCast_re]; linarith [m.cast_nonneg (α := ℝ)])
  convert (Gamma_add_nat_div_Gamma_eq ((a : ℂ) + m) hne (n := m)).symm using 3
  ring

private theorem pow_cube_div_nine (z : ℂ) (m : ℕ) :
    (z ^ 3 / 9) ^ m = z ^ (m * 3) * (3 : ℂ) ^ (-2 * (m : ℂ)) := by
  rw [div_pow, ← pow_mul, mul_comm 3 m, div_eq_mul_inv,
    show (9 : ℂ) = (3 : ℂ) ^ 2 by norm_num, ← pow_mul,
    ← cpow_natCast 3 (2 * m), ← cpow_neg]
  congr 2; push_cast; ring

private theorem airyModulusSq_term_mod_zero (z : ℂ) (m : ℕ) :
    4 * (3 : ℂ) ^ (-4 / 3 : ℂ) *
        ((ascPochhammer ℂ m).eval ((2 / 3 : ℂ) + 2 / 3 + m - 1) /
          (m ! * Gamma (2 / 3 + m) * Gamma (2 / 3 + m)) * (z ^ 3 / 9) ^ m) =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ ((((m * 3 : ℕ) : ℂ) + 1 / 2) / 3) *
          Gamma ((((m * 3 : ℕ) : ℂ) + 1 / 2) / 3) / 3) *
        z ^ (m * 3) / (m * 3)! := by
  have hc0 : (3 : ℂ) ^ (-4 / 3 : ℂ) * (3 : ℂ) ^ (-2 * (m : ℂ)) =
      (3 : ℂ) ^ (-2 * ((m : ℂ) + 1 / 6) - 1) := by
    rw [← cpow_add _ _ (by norm_num)]; congr 1; ring
  have hr0 := complex_gamma_duplication_triplication_coeff (s := m + 1 / 6) (by positivity)
  push_cast at hr0
  rw [← hc0, show 2 * ((m : ℂ) + 1 / 6) = ((1 / 3 : ℝ) : ℂ) + 2 * m by push_cast; ring,
    show (m : ℂ) + 1 / 6 + 1 / 6 = ((1 / 3 : ℝ) : ℂ) + m by push_cast; ring,
    show (m : ℂ) + 1 / 6 + 1 / 2 = 2 / 3 + (m : ℂ) by ring,
    show (m : ℂ) + 1 / 6 + 5 / 6 = (m : ℂ) + 1 by ring,
    show 3 * ((m : ℂ) + 1 / 6) + 1 / 2 = ((m * 3 : ℕ) : ℂ) + 1 by push_cast; ring,
    show (m : ℂ) + 1 / 6 = (((m * 3 : ℕ) : ℂ) + 1 / 2) / 3 by push_cast; ring,
    Gamma_nat_eq_factorial m, Gamma_nat_eq_factorial (m * 3)] at hr0
  rw [pow_cube_div_nine,
    show (2 / 3 : ℂ) + 2 / 3 + m - 1 = ((1 / 3 : ℝ) : ℂ) + m by push_cast; ring,
    ascPochhammer_eval_eq_Gamma_div (by norm_num : (0 : ℝ) < 1 / 3) m,
    ← div_mul_eq_mul_div, ← hr0]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem airyModulusSq_term_mod_one (z : ℂ) (m : ℕ) :
    (4 / 9 : ℂ) * z *
        ((ascPochhammer ℂ m).eval ((2 / 3 : ℂ) + 4 / 3 + m - 1) /
          (m ! * Gamma (2 / 3 + m) * Gamma (4 / 3 + m)) * (z ^ 3 / 9) ^ m) =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ ((((m * 3 + 1 : ℕ) : ℂ) + 1 / 2) / 3) *
          Gamma ((((m * 3 + 1 : ℕ) : ℂ) + 1 / 2) / 3) / 3) *
        z ^ (m * 3 + 1) / (m * 3 + 1)! := by
  have hc1 : (4 / 9 : ℂ) * (3 : ℂ) ^ (-2 * (m : ℂ)) =
      4 * (3 : ℂ) ^ (-2 * ((m : ℂ) + 1 / 2) - 1) := by
    have h9 : (1 / 9 : ℂ) = (3 : ℂ) ^ (-2 : ℂ) := by
      rw [show (-2 : ℂ) = -(2 : ℕ) by norm_num, cpow_neg, cpow_natCast]; norm_num
    rw [show (4 / 9 : ℂ) = 4 * (1 / 9) by ring, mul_assoc, h9, ← cpow_add _ _ (by norm_num)]
    congr 2; ring
  have hr1 := complex_gamma_duplication_triplication_coeff (s := m + 1 / 2) (by positivity)
  push_cast at hr1
  rw [← hc1, show 2 * ((m : ℂ) + 1 / 2) = ((1 : ℝ) : ℂ) + 2 * m by push_cast; ring,
    show (m : ℂ) + 1 / 2 + 1 / 6 = 2 / 3 + (m : ℂ) by ring,
    show (m : ℂ) + 1 / 2 + 1 / 2 = (m : ℂ) + 1 by ring,
    show (m : ℂ) + 1 / 2 + 5 / 6 = 4 / 3 + (m : ℂ) by ring,
    show 3 * ((m : ℂ) + 1 / 2) + 1 / 2 = ((m * 3 + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
    show (m : ℂ) + 1 / 2 = (((m * 3 + 1 : ℕ) : ℂ) + 1 / 2) / 3 by push_cast; ring,
    Gamma_nat_eq_factorial m, Gamma_nat_eq_factorial (m * 3 + 1)] at hr1
  have h1 : ((1 : ℝ) : ℂ) + (m : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  rw [pow_cube_div_nine, show (2 / 3 : ℂ) + 4 / 3 + m - 1 = ((1 : ℝ) : ℂ) + m by push_cast; ring,
    ascPochhammer_eval_eq_Gamma_div (by norm_num : (0 : ℝ) < 1) m,
    h1, Gamma_nat_eq_factorial m, pow_succ, ← div_mul_eq_mul_div, ← hr1]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem airyModulusSq_term_mod_two (z : ℂ) (m : ℕ) :
    4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
        ((ascPochhammer ℂ m).eval ((4 / 3 : ℂ) + 4 / 3 + m - 1) /
          (m ! * Gamma (4 / 3 + m) * Gamma (4 / 3 + m)) * (z ^ 3 / 9) ^ m) =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ ((((m * 3 + 2 : ℕ) : ℂ) + 1 / 2) / 3) *
          Gamma ((((m * 3 + 2 : ℕ) : ℂ) + 1 / 2) / 3) / 3) *
        z ^ (m * 3 + 2) / (m * 3 + 2)! := by
  have hc2 : (3 : ℂ) ^ (-8 / 3 : ℂ) * (3 : ℂ) ^ (-2 * (m : ℂ)) =
      (3 : ℂ) ^ (-2 * ((m : ℂ) + 5 / 6) - 1) := by
    rw [← cpow_add _ _ (by norm_num)]; congr 1; ring
  have hr2 := complex_gamma_duplication_triplication_coeff (s := m + 5 / 6) (by positivity)
  push_cast at hr2
  rw [← hc2, show 2 * ((m : ℂ) + 5 / 6) = ((5 / 3 : ℝ) : ℂ) + 2 * m by push_cast; ring,
    show (m : ℂ) + 5 / 6 + 1 / 6 = (m : ℂ) + 1 by ring,
    show (m : ℂ) + 5 / 6 + 1 / 2 = 4 / 3 + (m : ℂ) by ring,
    show (m : ℂ) + 5 / 6 + 5 / 6 = ((5 / 3 : ℝ) : ℂ) + m by push_cast; ring,
    show 3 * ((m : ℂ) + 5 / 6) + 1 / 2 = ((m * 3 + 2 : ℕ) : ℂ) + 1 by push_cast; ring,
    show (m : ℂ) + 5 / 6 = (((m * 3 + 2 : ℕ) : ℂ) + 1 / 2) / 3 by push_cast; ring,
    Gamma_nat_eq_factorial m, Gamma_nat_eq_factorial (m * 3 + 2)] at hr2
  rw [pow_cube_div_nine,
    show (4 / 3 : ℂ) + 4 / 3 + m - 1 = ((5 / 3 : ℝ) : ℂ) + m by push_cast; ring,
    ascPochhammer_eval_eq_Gamma_div (by norm_num : (0 : ℝ) < 5 / 3) m,
    pow_add, ← div_mul_eq_mul_div, ← hr2]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem hasSum_airyAi_sq_add_airyBi_sq_blocks (z : ℂ) :
    HasSum (fun m : ℕ =>
      ∑ r : Fin 3,
        (π : ℂ) ^ (-3 / 2 : ℂ) *
          ((12 : ℂ) ^ ((((m * 3 + (r : ℕ) : ℕ) : ℂ) + 1 / 2) / 3) *
            Gamma ((((m * 3 + (r : ℕ) : ℕ) : ℂ) + 1 / 2) / 3) / 3) *
          z ^ (m * 3 + (r : ℕ)) / (m * 3 + (r : ℕ))!)
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  have h1 := (hasSum_mul_regularizedHGFun_zero_singleton (2 / 3) (2 / 3) (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-4 / 3 : ℂ))
  have h2 := (hasSum_mul_regularizedHGFun_zero_singleton (2 / 3) (4 / 3) (z ^ 3 / 9)).mul_left
    ((4 / 9 : ℂ) * z)
  have h3 := (hasSum_mul_regularizedHGFun_zero_singleton (4 / 3) (4 / 3) (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2)
  rw [airyAi_sq_add_airyBi_sq_eq_regularizedHGFun, sq (regularizedHGFun 0 {(2 / 3 : ℂ)} _),
    sq (regularizedHGFun 0 {(4 / 3 : ℂ)} _)]
  convert (h1.add h2).add h3 using 1
  ext m
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero]
  rw [airyModulusSq_term_mod_zero, airyModulusSq_term_mod_one, airyModulusSq_term_mod_two]

/-! ### Absolute integrability and termwise expansion of the cubic-exponential Laplace integral -/

private theorem linear_sub_cube_div_twelve_le (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    a * t - t ^ 3 / 12 ≤ |a| * (24 * |a| + 1) - (1 / 24) * t ^ 3 := by
  have ha : a * t ≤ |a| * t := mul_le_mul_of_nonneg_right (le_abs_self a) ht
  rcases le_total t (24 * |a| + 1) with hle | hge
  · have hcube : 0 ≤ t ^ 3 := pow_nonneg ht 3
    have hmul : |a| * t ≤ |a| * (24 * |a| + 1) := mul_le_mul_of_nonneg_left hle (abs_nonneg a)
    linarith
  · have ht1 : 1 ≤ t := by linarith [abs_nonneg a]
    have : 24 * |a| ≤ t ^ 2 := by nlinarith
    have ht3 : 24 * (|a| * t) ≤ t ^ 3 := by nlinarith
    have hpos : 0 ≤ |a| * (24 * |a| + 1) := by positivity
    linarith

/-- For `q > -1` and every real rate `a`, `t ↦ exp(a t - t³ / 12) t^q` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_mul_sub_cube_div_twelve_mul_rpow {q : ℝ} (hq : -1 < q) (a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (a * t - t ^ 3 / 12) * t ^ q) (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ =>
      Real.exp (|a| * (24 * |a| + 1)) * (t ^ q * Real.exp (-(1 / 24) * t ^ (3 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num) (by norm_num)).const_mul _
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (Real.continuous_exp.comp (by fun_prop)).continuousOn.mul
      (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0 q)),
      Real.rpow_ofNat, mul_left_comm (Real.exp _) (t ^ q), ← Real.exp_add, mul_comm (t ^ q)]
    gcongr
    linarith [linear_sub_cube_div_twelve_le a ht0]

/-- For `Re w > -1` and every `z : ℂ`, `t ↦ exp(z t - t³ / 12) t^w` is Bochner integrable on
`(0, ∞)`. -/
theorem integrableOn_cexp_mul_sub_cube_div_twelve_mul_cpow {w : ℂ} (hw : -1 < w.re) (z : ℂ) :
    IntegrableOn (fun t : ℝ => cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ w) (Ioi 0) := by
  refine (integrableOn_exp_mul_sub_cube_div_twelve_mul_rpow hw z.re).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Continuous.continuousOn (by fun_prop)).mul ?_
    intro t ht
    exact (continuousAt_ofReal_cpow_const t w (Or.inr (ne_of_gt ht))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht]
    apply le_of_eq
    congr 2
    simp [sub_re, mul_re, div_ofNat_re, pow_three]

private theorem ofReal_div_twelve_mul_cube_cpow {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ((12⁻¹ * t ^ 3 : ℝ) : ℂ) ^ (s - 1) =
      (12 : ℂ) ^ (1 - s) * (t : ℂ) ^ (3 * (s - 1)) := by
  have hpos : 0 < (12⁻¹ : ℝ) * t ^ 3 := by positivity
  have h12 : (12 : ℂ) = ((12 : ℝ) : ℂ) := by norm_num
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hpos.ne'), h12,
    cpow_def_of_ne_zero (by norm_num), cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'),
    ← ofReal_log hpos.le, ← ofReal_log (by norm_num : (0 : ℝ) ≤ 12), ← ofReal_log ht.le,
    Real.log_mul (by norm_num) (by positivity), Real.log_inv, Real.log_pow, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Complex Gamma moment of the cubic-exponential kernel on `(0, ∞)` for `Re w > -1`:
`∫₀^∞ exp(-t³ / 12) t^w dt = 12^{(w + 1)/3} Γ((w + 1)/3) / 3`. -/
theorem integral_cexp_neg_cube_div_twelve_mul_cpow {w : ℂ} (hw : -1 < w.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w =
      (12 : ℂ) ^ ((w + 1) / 3) * Gamma ((w + 1) / 3) / 3 := by
  let s : ℂ := (w + 1) / 3
  have hs_def : s = (w + 1) / 3 := rfl
  have hs : 0 < s.re := by simp only [hs_def, add_re, one_re, div_ofNat_re]; linarith
  let g : ℝ → ℂ := fun u => (Real.exp (-(12⁻¹ * u)) : ℂ) * ((12⁻¹ * u : ℝ) : ℂ) ^ (s - 1)
  have hc1 : ∫ u in Ioi (0 : ℝ), g u = 12 * Gamma s := by
    have h := integral_comp_mul_left_Ioi (fun x : ℝ => (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) 0
      (b := 12⁻¹) (by norm_num)
    rw [mul_zero, inv_inv, real_smul, ofReal_ofNat, ← GammaIntegral, ← Gamma_eq_integral hs] at h
    exact h
  have hc2 : ∫ t in Ioi (0 : ℝ), ((3 : ℝ) * t ^ ((3 : ℝ) - 1)) • g (t ^ (3 : ℝ)) =
      12 * Gamma s := by
    rw [integral_comp_rpow_Ioi_of_pos (g := g) (by norm_num : (0 : ℝ) < 3), hc1]
  have heq : EqOn (fun t : ℝ => ((3 : ℝ) * t ^ ((3 : ℝ) - 1)) • g (t ^ (3 : ℝ)))
      (fun t : ℝ => (3 * (12 : ℂ) ^ (1 - s)) * (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w))
      (Ioi 0) := by
    intro t ht
    have ht' : 0 < t := ht
    dsimp only [g]
    have hpowt : (t : ℂ) ^ 2 * (t : ℂ) ^ (3 * (s - 1)) = (t : ℂ) ^ w := by
      rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht'.ne')]
      congr 1; rw [hs_def]; ring
    rw [real_smul, show ((3 : ℝ) - 1) = (2 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_ofNat,
      ofReal_mul, ofReal_ofNat, ofReal_pow, ofReal_exp, ofReal_div_twelve_mul_cube_cpow ht' s,
      show ((-(12⁻¹ * t ^ 3) : ℝ) : ℂ) = -((t : ℂ) ^ 3 / 12) by push_cast; ring]
    linear_combination (3 * (12 : ℂ) ^ (1 - s) * cexp (-((t : ℂ) ^ 3 / 12))) * hpowt
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul] at hc2
  have h12s : (12 : ℂ) ^ ((w + 1) / 3) * (12 : ℂ) ^ (1 - s) = 12 := by
    rw [← cpow_add _ _ (by norm_num), show (w + 1) / 3 + (1 - s) = 1 by rw [hs_def]; ring, cpow_one]
  calc ∫ t in Ioi (0 : ℝ), cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w
      = ((12 : ℂ) ^ ((w + 1) / 3) / 36) *
          ((3 * (12 : ℂ) ^ (1 - s)) *
            ∫ t in Ioi (0 : ℝ), cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w) := by
        linear_combination
          -(∫ t in Ioi (0 : ℝ), cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w) / 12 * h12s
    _ = (12 : ℂ) ^ ((w + 1) / 3) * Gamma ((w + 1) / 3) / 3 := by
        rw [hc2, hs_def]; ring

private theorem integral_cexp_term_eq {w : ℂ} (hw : -1 < w.re) (z : ℂ) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ),
        (z * t) ^ n / n ! * (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w) =
      (12 : ℂ) ^ (((n : ℂ) + w + 1) / 3) * Gamma (((n : ℂ) + w + 1) / 3) / 3 * z ^ n / n ! := by
  have heq : EqOn
      (fun t : ℝ => (z * t) ^ n / n ! * (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w))
      (fun t : ℝ => (z ^ n / n !) * (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ ((n : ℂ) + w)))
      (Ioi 0) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    dsimp only
    rw [mul_pow, ← cpow_natCast (t : ℂ) n, cpow_add _ _ ht0]
    ring
  have hwn : -1 < ((n : ℂ) + w).re := by
    simp only [add_re, natCast_re]
    linarith [n.cast_nonneg (α := ℝ)]
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    integral_cexp_neg_cube_div_twelve_mul_cpow hwn]
  ring

/-- Termwise power-series expansion of the cubic-exponential Laplace integral
`∫₀^∞ exp(z t - t³ / 12) t^w dt` for `Re w > -1`. -/
theorem hasSum_integral_cexp_mul_sub_cube_div_twelve_mul_cpow {w : ℂ} (hw : -1 < w.re) (z : ℂ) :
    HasSum (fun n : ℕ =>
      (12 : ℂ) ^ (((n : ℂ) + w + 1) / 3) * Gamma (((n : ℂ) + w + 1) / 3) / 3 * z ^ n / n !)
      (∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ w) := by
  have hdom := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (n : ℕ) (t : ℝ) =>
      (z * t) ^ n / n ! * (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w))
    (f := fun t : ℝ => cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ w)
    (bound := fun (n : ℕ) (t : ℝ) =>
      (‖z‖ * t) ^ n / n ! * (Real.exp (-(t ^ 3 / 12)) * t ^ w.re))
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · refine hdom.congr_fun fun n => (integral_cexp_term_eq hw z n).symm
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Continuous.continuousOn (by fun_prop)).mul
      ((Continuous.continuousOn (by fun_prop)).mul ?_)
    intro t ht
    exact (continuousAt_ofReal_cpow_const t w (Or.inr (ne_of_gt ht))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_of_nonneg ht.le, norm_natCast,
      norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht]
    apply le_of_eq
    congr 3
    simp [div_ofNat_re, pow_three]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    exact (Real.summable_pow_div_factorial (‖z‖ * t)).mul_right _
  · refine (integrableOn_exp_mul_sub_cube_div_twelve_mul_rpow hw ‖z‖).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    dsimp only
    rw [tsum_mul_right, (NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)).tsum_eq,
      ← Real.exp_eq_exp_ℝ, ← mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    convert (NormedSpace.expSeries_div_hasSum_exp (z * t)).mul_right
      (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ w) using 1
    rw [← exp_eq_exp_ℂ, ← mul_assoc, ← Complex.exp_add, sub_eq_add_neg]

/-! ### Nicholson's integral representation (DLMF 9.11.4) and Maclaurin series -/

/-- **DLMF 9.11.4**: Nicholson's Laplace-type integral representation of `Ai(z)² + Bi(z)²`,
absolutely convergent for every `z : ℂ`. -/
theorem airyAi_sq_add_airyBi_sq_eq_integral (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
  have hint := ((hasSum_integral_cexp_mul_sub_cube_div_twelve_mul_cpow
    (w := -1 / 2) (by norm_num) z).mul_left ((π : ℂ) ^ (-3 / 2 : ℂ))).sum_fin_add_add_nat 3
  refine (hasSum_airyAi_sq_add_airyBi_sq_blocks z).unique (hint.congr_fun fun m => ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  have harg : (((m * 3 + (r : ℕ) : ℕ) : ℂ) + (-1 / 2) + 1) / 3 =
      (((m * 3 + (r : ℕ) : ℕ) : ℂ) + 1 / 2) / 3 := by ring
  rw [harg]; ring

/-- The everywhere-convergent Maclaurin series of `Ai(z)² + Bi(z)²`:
`Ai(z)² + Bi(z)² = π^{-3/2} ∑_{n=0}^∞ (12^{(n + 1/2)/3} Γ((n + 1/2)/3) / 3) zⁿ / n!`. -/
theorem hasSum_airyAi_sq_add_airyBi_sq (z : ℂ) :
    HasSum (fun n : ℕ =>
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((n : ℂ) + 1 / 2) / 3) * Gamma (((n : ℂ) + 1 / 2) / 3) / 3) *
        z ^ n / n !)
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral]
  refine ((hasSum_integral_cexp_mul_sub_cube_div_twelve_mul_cpow
    (w := -1 / 2) (by norm_num) z).mul_left ((π : ℂ) ^ (-3 / 2 : ℂ))).congr_fun fun n => ?_
  have harg : ((n : ℂ) + (-1 / 2) + 1) / 3 = ((n : ℂ) + 1 / 2) / 3 := by ring
  rw [harg]; ring

private theorem airyModulusSq_coeff_eq_ofReal (m : ℕ) :
    (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) * Gamma (((m : ℂ) + 1 / 2) / 3) / 3) =
      ((Real.pi ^ (-3 / 2 : ℝ) *
        ((12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) *
          Real.Gamma (((m : ℝ) + 1 / 2) / 3) / 3) : ℝ) : ℂ) := by
  simp only [ofReal_mul, ofReal_div, ofReal_ofNat, ← Gamma_ofReal]
  rw [ofReal_cpow Real.pi_pos.le, ofReal_cpow (by positivity : (0 : ℝ) ≤ 12)]
  push_cast
  rfl

private theorem summable_norm_airyModulusSq_shifted (k : ℕ) (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖(π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((n + k : ℕ) + 1 / 2 : ℂ) / 3) *
          Gamma (((n + k : ℕ) + 1 / 2 : ℂ) / 3) / 3) *
        z ^ n / (n !)‖) := by
  have hw : -1 < ((k : ℂ) - 1 / 2).re := by
    simp only [sub_re, natCast_re]; norm_num; linarith [k.cast_nonneg (α := ℝ)]
  have hs := (hasSum_integral_cexp_mul_sub_cube_div_twelve_mul_cpow hw (‖z‖ : ℂ)).mul_left
    ((π : ℂ) ^ (-3 / 2 : ℂ))
  refine (Complex.hasSum_re hs).summable.congr fun n => ?_
  have hm_pos : 0 < (((n + k : ℕ) : ℝ) + 1 / 2) / 3 := by linarith [(n + k).cast_nonneg (α := ℝ)]
  have : 0 < Real.Gamma ((((n + k : ℕ) : ℝ) + 1 / 2) / 3) := Real.Gamma_pos_of_pos hm_pos
  have harg : ((n : ℂ) + ((k : ℂ) - 1 / 2) + 1) / 3 = (((n + k : ℕ) : ℂ) + 1 / 2) / 3 := by
    push_cast; ring
  have hc := airyModulusSq_coeff_eq_ofReal (n + k)
  rw [Nat.cast_add] at hc
  push_cast at harg ⊢
  rw [harg]
  have hterm : (π : ℂ) ^ (-3 / 2 : ℂ) *
      ((12 : ℂ) ^ (((n : ℂ) + k + 1 / 2) / 3) * Gamma (((n : ℂ) + k + 1 / 2) / 3) / 3 *
        (‖z‖ : ℂ) ^ n / n !) =
      ((Real.pi ^ (-3 / 2 : ℝ) *
        ((12 : ℝ) ^ ((((n + k : ℕ) : ℝ) + 1 / 2) / 3) *
          Real.Gamma ((((n + k : ℕ) : ℝ) + 1 / 2) / 3) / 3) *
        ‖z‖ ^ n / n ! : ℝ) : ℂ) := by
    rw [← mul_div_assoc, ← mul_assoc ((π : ℂ) ^ (-3 / 2 : ℂ)), hc]
    push_cast
    rfl
  rw [hterm, ofReal_re, norm_div, norm_mul, norm_pow, norm_natCast, hc,
    Complex.norm_of_nonneg (by positivity)]

/-- The Maclaurin series of `Ai(z)² + Bi(z)²` converges absolutely at every `z : ℂ`. -/
theorem summable_norm_airyAi_sq_add_airyBi_sq (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖(π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((n : ℂ) + 1 / 2) / 3) * Gamma (((n : ℂ) + 1 / 2) / 3) / 3) *
        z ^ n / (n !)‖) := by
  simpa using summable_norm_airyModulusSq_shifted 0 z

/-! ### Iterated derivatives and moment integrals -/

/-- The Maclaurin series of the `k`-th derivative of `Ai(z)² + Bi(z)²`. -/
theorem hasSum_iteratedDeriv_airyAi_sq_add_airyBi_sq (k : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ =>
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((n + k : ℕ) + 1 / 2 : ℂ) / 3) *
          Gamma (((n + k : ℕ) + 1 / 2 : ℂ) / 3) / 3) *
        z ^ n / n !)
      (iteratedDeriv k (fun w => airyAi w ^ 2 + airyBi w ^ 2) z) := by
  induction k generalizing z with
  | zero => simpa using hasSum_airyAi_sq_add_airyBi_sq z
  | succ k ih =>
    set R : ℝ := ‖z‖ + 1
    have hfun : iteratedDeriv k (fun w => airyAi w ^ 2 + airyBi w ^ 2) =
        fun w => ∑' n : ℕ, ((π : ℂ) ^ (-3 / 2 : ℂ) *
          ((12 : ℂ) ^ (((n + k : ℕ) + 1 / 2 : ℂ) / 3) *
            Gamma (((n + k : ℕ) + 1 / 2 : ℂ) / 3) / 3) / n !) * w ^ n := by
      ext w
      simpa [mul_div_right_comm] using (ih w).tsum_eq.symm
    have hsumR : Summable (fun n : ℕ =>
        ‖((π : ℂ) ^ (-3 / 2 : ℂ) *
          ((12 : ℂ) ^ (((n + k : ℕ) + 1 / 2 : ℂ) / 3) *
            Gamma (((n + k : ℕ) + 1 / 2 : ℂ) / 3) / 3) / n !) * (R : ℂ) ^ n‖) := by
      simpa [mul_div_right_comm] using summable_norm_airyModulusSq_shifted k (R : ℂ)
    have hd := hasSum_deriv_of_summable_norm hsumR
      (F := fun n w => ((π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((n + k : ℕ) + 1 / 2 : ℂ) / 3) *
          Gamma (((n + k : ℕ) + 1 / 2 : ℂ) / 3) / 3) / n !) * w ^ n)
      (U := Metric.ball 0 R)
      (fun n => ((differentiable_pow n).const_mul _).differentiableOn) Metric.isOpen_ball
      (fun n w hw => ?_) (z := z) (by simp [R])
    · rw [iteratedDeriv_succ, hfun]
      have hd' := (hasSum_nat_add_iff' 1).mpr hd
      simp only [Finset.sum_range_one, pow_zero, mul_one, deriv_const, sub_zero] at hd'
      refine hd'.congr_fun fun n => ?_
      simp only [deriv_const_mul_field', deriv_pow_field, add_tsub_cancel_right]
      have hidx : n + 1 + k = n + (k + 1) := by omega
      rw [hidx, Nat.factorial_succ]
      push_cast
      have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
    · rw [Metric.mem_ball, dist_zero_right] at hw
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      gcongr

/-- Differentiating DLMF 9.11.4 `k` times gives the `k`-th moment of the cubic-exponential
kernel: `∂_z^k (Ai(z)² + Bi(z)²) = π^{-3/2} ∫₀^∞ exp(z t - t³ / 12) t^{k - 1/2} dt`. -/
theorem iteratedDeriv_airyAi_sq_add_airyBi_sq_eq_integral (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => airyAi w ^ 2 + airyBi w ^ 2) z =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ ((k : ℂ) - 1 / 2) := by
  have hw : -1 < ((k : ℂ) - 1 / 2).re := by
    simp only [sub_re, natCast_re]; norm_num; linarith [k.cast_nonneg (α := ℝ)]
  have hint := (hasSum_integral_cexp_mul_sub_cube_div_twelve_mul_cpow hw z).mul_left
    ((π : ℂ) ^ (-3 / 2 : ℂ))
  refine (hasSum_iteratedDeriv_airyAi_sq_add_airyBi_sq k z).unique (hint.congr_fun fun n => ?_)
  have harg : ((n : ℂ) + ((k : ℂ) - 1 / 2) + 1) / 3 =
      ((n + k : ℕ) + 1 / 2 : ℂ) / 3 := by push_cast; ring
  rw [harg]; ring

/-- The first derivative of `Ai(z)² + Bi(z)²` in integral form:
`2 (Ai(z) Ai′(z) + Bi(z) Bi′(z)) = π^{-3/2} ∫₀^∞ exp(z t - t³ / 12) t^{1/2} dt`. -/
theorem deriv_airyAi_sq_add_airyBi_sq_eq_integral (z : ℂ) :
    2 * (airyAi z * deriv airyAi z + airyBi z * deriv airyBi z) =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (1 / 2 : ℂ) := by
  have hd : HasDerivAt (fun w => airyAi w ^ 2 + airyBi w ^ 2)
      (2 * (airyAi z * deriv airyAi z + airyBi z * deriv airyBi z)) z := by
    convert (((differentiable_airyAi z).hasDerivAt.pow 2).add
      ((differentiable_airyBi z).hasDerivAt.pow 2)) using 1
    ring
  rw [← hd.deriv, ← iteratedDeriv_one, iteratedDeriv_airyAi_sq_add_airyBi_sq_eq_integral]
  norm_num

/-! ### Values at the origin and real-axis positivity -/

/-- The `k`-th derivative of `Ai(z)² + Bi(z)²` at the origin. -/
theorem iteratedDeriv_airyAi_sq_add_airyBi_sq_zero (k : ℕ) :
    iteratedDeriv k (fun w => airyAi w ^ 2 + airyBi w ^ 2) 0 =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ((12 : ℂ) ^ (((k : ℂ) + 1 / 2) / 3) * Gamma (((k : ℂ) + 1 / 2) / 3) / 3) := by
  refine (hasSum_iteratedDeriv_airyAi_sq_add_airyBi_sq k 0).unique ?_
  convert hasSum_single (0 : ℕ) ?_ using 1
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- DLMF 9.11.4 at `z = 0`: `4 Ai(0)² = π^{-3/2} 12^{1/6} Γ(1/6) / 3`. -/
theorem four_mul_airyAi_zero_sq :
    4 * airyAi 0 ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3 := by
  have h := iteratedDeriv_airyAi_sq_add_airyBi_sq_zero 0
  rw [iteratedDeriv_zero, airyAi_zero_sq_add_airyBi_zero_sq] at h
  rw [h]
  norm_num
  ring

/-- On the real axis, `Ai(x)² + Bi(x)²` is the coercion of the real integral
`π^{-3/2} ∫₀^∞ exp(x t - t³ / 12) t^{-1/2} dt`. -/
theorem airyAi_sq_add_airyBi_sq_ofReal_eq_integral (x : ℝ) :
    airyAi x ^ 2 + airyBi x ^ 2 =
      ((Real.pi ^ (-3 / 2 : ℝ) *
        ∫ t in Ioi (0 : ℝ), Real.exp (x * t - t ^ 3 / 12) * t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral, ofReal_mul, ofReal_cpow Real.pi_pos.le,
    ← integral_complex_ofReal]
  congr 1
  · norm_num
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [ofReal_mul, ofReal_exp, ofReal_cpow ht.le]
    push_cast
    rfl

/-- At real arguments, `Ai(x)² + Bi(x)²` is real. -/
theorem airyAi_sq_add_airyBi_sq_ofReal_im (x : ℝ) :
    (airyAi x ^ 2 + airyBi x ^ 2).im = 0 := by
  rw [airyAi_sq_add_airyBi_sq_ofReal_eq_integral, ofReal_im]

/-- On the real axis, `Re(Ai(x)² + Bi(x)²) = π^{-3/2} ∫₀^∞ exp(x t - t³ / 12) t^{-1/2} dt` is
strictly positive. -/
theorem airyAi_sq_add_airyBi_sq_ofReal_re_pos (x : ℝ) :
    0 < (airyAi x ^ 2 + airyBi x ^ 2).re := by
  rw [airyAi_sq_add_airyBi_sq_ofReal_eq_integral, ofReal_re]
  refine mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support
        (fun t : ℝ => Real.exp (x * t - t ^ 3 / 12) * t ^ (-1 / 2 : ℝ)) ∩ Ioi 0 := by
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      exact ⟨(mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht0 _)).ne', ht0⟩
    exact lt_of_lt_of_le (by simp [Real.volume_Ioo]) (measure_mono hsub)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  · exact integrableOn_exp_mul_sub_cube_div_twelve_mul_rpow (by norm_num) x

/-- `Ai(x)² + Bi(x)²` never vanishes on the real axis. -/
theorem airyAi_sq_add_airyBi_sq_ofReal_ne_zero (x : ℝ) :
    airyAi x ^ 2 + airyBi x ^ 2 ≠ 0 := by
  intro h
  have hpos := airyAi_sq_add_airyBi_sq_ofReal_re_pos x
  rw [h, zero_re] at hpos
  exact lt_irrefl 0 hpos

end TauCeti
