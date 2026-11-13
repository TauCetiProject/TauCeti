/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Analysis.SpecialFunctions.Gamma.Multiplication
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Integral representation and Maclaurin series of `Ai(z)² + Bi(z)²`

This file proves the integral representation of `airyAi z ^ 2 + airyBi z ^ 2` (DLMF 9.11.4),

$$
\operatorname{Ai}(z)^2 + \operatorname{Bi}(z)^2 =
  \pi^{-3/2} \int_0^\infty \exp\!\left(z t - \frac{t^3}{12}\right) t^{-1/2}\, dt,
$$

valid for every complex `z` with an absolutely convergent integral on `(0, ∞)`, together with its
Maclaurin series, its evaluation at the origin, and its iterated parametric derivatives.

## Proof strategy

Expanding `airyAi` and `airyBi` into `₀F₁` series separates `airyAi z ^ 2 + airyBi z ^ 2` into
powers congruent to `0`, `1`, and `2` modulo `3`. Bailey's `₀F₁` product identities
(`Complex.regularizedHGFun_zero_singleton_mul_eq` and
`Complex.regularizedHGFun_zero_singleton_sq_eq`, DLMF 16.12.1–16.12.2) express each of the three
pieces as a single hypergeometric series in `4 z ^ 3 / 9`. Simplifying the Gamma factors with
Legendre's duplication formula and Gauss's triplication formula
(`Complex.Gamma_mul_Gamma_add_third`) identifies the `m`-th Maclaurin coefficient of
`airyAi z ^ 2 + airyBi z ^ 2` as `π ^ (-3 / 2) * 12 ^ ((2m + 1) / 6) * Γ((2m + 1) / 6) / (3 * m!)`.
On the integral side, expanding `exp(z t)` and integrating term-by-term against the super-Gaussian
decay `exp(-t³ / 12)` evaluates each moment via `integral_rpow_mul_exp_neg_mul_rpow` to the same
coefficient; grouping the integral series into blocks of length `3` via
`HasSum.sum_fin_add_add_nat` equates the two sides.

## Main results

* `TauCeti.integrableOn_cexp_sub_cubic_mul_cpow`: absolute convergence of
  `∫ t in Ioi 0, exp(z t - b t³) t ^ s` for every `b, z, s : ℂ` with `0 < Re b` and `-1 < Re s`.
* `TauCeti.airyAi_sq_add_airyBi_sq_eq_integral`: DLMF 9.11.4 for every `z : ℂ`.
* `TauCeti.hasSum_airyAi_sq_add_airyBi_sq`: the everywhere-convergent Maclaurin series of
  `airyAi z ^ 2 + airyBi z ^ 2`.
* `TauCeti.airyAi_zero_sq_add_airyBi_zero_sq`, `TauCeti.four_mul_airyAi_zero_sq`: the value
  `airyAi 0 ^ 2 + airyBi 0 ^ 2 = 4 * airyAi 0 ^ 2 = π ^ (-3 / 2) * 12 ^ (1 / 6) * Γ(1 / 6) / 3`.
* `TauCeti.hasDerivAt_integral_cexp_sub_cubic_mul_cpow`,
  `TauCeti.iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral`,
  `TauCeti.airyAi_mul_deriv_add_airyBi_mul_deriv_eq_integral`: parametric derivatives under the
  integral sign and iterated derivatives of the integral representation.

## References

* NIST Digital Library of Mathematical Functions, §§9.11(iii), 16.12,
  <https://dlmf.nist.gov/9.11>, <https://dlmf.nist.gov/16.12>.
-/

public section

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Nat Topology

namespace TauCeti

/-! ### Algebraic and Gamma helpers for the Maclaurin series -/

private theorem airyAi_sq_add_airyBi_sq_hypergeometric (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) ^ 2 +
        4 / 9 * z * (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
          regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) +
        4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
          regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) ^ 2 := by
  have h16 : (3 : ℂ) ^ (-1 / 6 : ℂ) = (3 : ℂ) ^ (1 / 2 : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) := by
    rw [← cpow_add _ _ (by norm_num)]; norm_num
  have h56 : (3 : ℂ) ^ (-5 / 6 : ℂ) = (3 : ℂ) ^ (1 / 2 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    rw [← cpow_add _ _ (by norm_num)]; norm_num
  have hs : ((3 : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = 3 := by
    rw [sq, ← cpow_add _ _ (by norm_num)]; norm_num
  have ha : ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 = (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    rw [sq, ← cpow_add _ _ (by norm_num)]; norm_num
  have hb : ((3 : ℂ) ^ (-4 / 3 : ℂ)) ^ 2 = (3 : ℂ) ^ (-8 / 3 : ℂ) := by
    rw [sq, ← cpow_add _ _ (by norm_num)]; norm_num
  have hab : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) = 1 / 9 := by
    have hexp : (-2 / 3 : ℂ) + (-4 / 3 : ℂ) = -((2 : ℕ) : ℂ) := by norm_num
    rw [← cpow_add _ _ (by norm_num), hexp, cpow_neg, cpow_natCast]
    norm_num
  rw [airyAi_def, airyBi_def, h16, h56]
  set F₂ := regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
  set F₄ := regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)
  linear_combination
    (((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 * F₂ ^ 2 +
      2 * ((3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ)) * z * F₂ * F₄ +
      ((3 : ℂ) ^ (-4 / 3 : ℂ)) ^ 2 * z ^ 2 * F₄ ^ 2) * hs +
      4 * F₂ ^ 2 * ha + 4 * z * F₂ * F₄ * hab + 4 * z ^ 2 * F₄ ^ 2 * hb

private theorem twelve_cpow_add_natCast (c : ℂ) (n : ℕ) :
    (12 : ℂ) ^ (c + n) = (2 : ℂ) ^ (2 * c) * (3 : ℂ) ^ c * (4 ^ n * 3 ^ n) := by
  have h12 : (12 : ℂ) = ((4 : ℝ) : ℂ) * ((3 : ℝ) : ℂ) := by norm_num
  have h4 : ((4 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) := by norm_num
  have h2c : c + c = 2 * c := by ring
  have h12n : (12 : ℂ) ^ (n : ℂ) = 4 ^ n * 3 ^ n := by
    rw [cpow_natCast, ← mul_pow]; norm_num
  rw [cpow_add _ _ (by norm_num), h12n, h12, mul_cpow_ofReal_nonneg (by norm_num) (by norm_num),
    h4, mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]
  simp only [ofReal_ofNat, ← cpow_add _ _ two_ne_zero, h2c]

private theorem three_cpow_sub_three_mul (c : ℂ) (n : ℕ) :
    (3 : ℂ) ^ (c - 3 * (n : ℂ)) = (3 : ℂ) ^ c / (9 ^ n * 3 ^ n) := by
  have hne : (9 : ℂ) ^ n * 3 ^ n ≠ 0 :=
    mul_ne_zero (pow_ne_zero n (by norm_num)) (pow_ne_zero n (by norm_num))
  rw [eq_div_iff hne]
  have h3n : 3 * n = 2 * n + n := by omega
  have hpow : (9 : ℂ) ^ n * 3 ^ n = (3 : ℂ) ^ ((3 * n : ℕ) : ℂ) := by
    rw [cpow_natCast, h3n, pow_add, pow_mul]; norm_num
  rw [hpow, ← cpow_add _ _ (by norm_num)]
  congr 1
  push_cast
  ring

private theorem pi_cpow_neg_three_halves :
    (π : ℂ) ^ (-3 / 2 : ℂ) = (((√π : ℝ) : ℂ) * π)⁻¹ := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexp : (-3 / 2 : ℂ) = -(1 / 2 + 1) := by norm_num
  rw [hexp, cpow_neg, cpow_add _ _ hpi, cpow_one, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
  push_cast
  rfl

private theorem gamma_mul_add_third_nat (r n : ℕ) :
    Gamma (((r + 1 : ℕ) : ℂ) / 3 + n) * Gamma (((r + 2 : ℕ) : ℂ) / 3 + n) *
        Gamma (((r + 3 : ℕ) : ℂ) / 3 + n) =
      2 * π * ((3 : ℂ) ^ (-(2 * (r : ℂ) + 1) / 2) / (9 ^ n * 3 ^ n)) *
        ((3 * n + r)! : ℂ) := by
  have ht := Gamma_mul_Gamma_add_third (((r + 1 : ℕ) : ℂ) / 3 + n)
  have hs1 : ((r + 1 : ℕ) : ℂ) / 3 + n + 1 / 3 = ((r + 2 : ℕ) : ℂ) / 3 + n := by
    push_cast; ring
  have hs2 : ((r + 1 : ℕ) : ℂ) / 3 + n + 2 / 3 = ((r + 3 : ℕ) : ℂ) / 3 + n := by
    push_cast; ring
  have hs3 : 3 * (((r + 1 : ℕ) : ℂ) / 3 + n) = ((3 * n + r : ℕ) : ℂ) + 1 := by
    push_cast; ring
  have he3 : (1 / 2 : ℂ) - (((3 * n + r : ℕ) : ℂ) + 1) =
      -(2 * (r : ℂ) + 1) / 2 - 3 * (n : ℂ) := by push_cast; ring
  rw [hs1, hs2, hs3, Gamma_nat_eq_factorial, he3, three_cpow_sub_three_mul] at ht
  exact ht

private theorem gamma_two_mul_div_gamma_add_half {s : ℂ} (hs : 0 < s.re) :
    Gamma (2 * s) / Gamma (s + 1 / 2) =
      Gamma s / ((2 : ℂ) ^ (1 - 2 * s) * ((√π : ℝ) : ℂ)) := by
  have hs' : 0 < (s + 1 / 2).re := by simp only [add_re, one_re, div_ofNat_re]; linarith
  have hGs : Gamma (s + 1 / 2) ≠ 0 := Gamma_ne_zero (ne_neg_natCast_of_re_pos hs')
  have h20 : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hspi : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  rw [div_eq_div_iff hGs (mul_ne_zero h20 hspi)]
  linear_combination -Gamma_mul_Gamma_add_half s

private theorem four_mul_cube_div_nine_pow (z : ℂ) (n : ℕ) :
    (4 * (z ^ 3 / 9)) ^ n = 4 ^ n * z ^ (3 * n) / 9 ^ n := by
  rw [← mul_div_assoc, div_pow, mul_pow, ← pow_mul]

private def airyProductTerm (z : ℂ) (m : ℕ) : ℂ :=
  (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ ((2 * (m : ℂ) + 1) / 6) *
    Gamma ((2 * (m : ℂ) + 1) / 6) / (3 * m !) * z ^ m

private theorem hasSum_airyProductTerm_sq_piece (r : ℕ)
    (htrip : ∀ n : ℕ,
      (n ! : ℂ) * (Gamma (((r + 2 : ℕ) : ℂ) / 3 + n) *
          Gamma (2 * (((r + 2 : ℕ) : ℂ) / 3) - 1 + n)) =
        2 * π * ((3 : ℂ) ^ (-(2 * (r : ℂ) + 1) / 2) / (9 ^ n * 3 ^ n)) *
          ((3 * n + r)! : ℂ))
    (z : ℂ) :
    HasSum (fun n : ℕ => airyProductTerm z (3 * n + r))
      (4 * (3 : ℂ) ^ (-2 * (((r + 2 : ℕ) : ℂ) / 3)) * z ^ r *
        regularizedHGFun 0 {((r + 2 : ℕ) : ℂ) / 3} (z ^ 3 / 9) ^ 2) := by
  set a : ℂ := ((r + 2 : ℕ) : ℂ) / 3
  set c : ℂ := (2 * (r : ℂ) + 1) / 6
  have hc_re : 0 < c.re := by
    simp only [c, add_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero,
      one_re, div_ofNat_re]
    positivity
  have hac : a - 1 / 2 = c := by simp only [a, c]; push_cast; ring
  have h2ac : 2 * a - 1 = 2 * c := by simp only [a, c]; push_cast; ring
  have hpole : ∀ k : ℕ, 2 * a - 1 ≠ -k := by
    rw [h2ac]
    refine ne_neg_natCast_of_re_pos ?_
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  rw [regularizedHGFun_zero_singleton_sq_eq hpole (z ^ 3 / 9), hac, ← mul_assoc]
  refine ((hasSum_regularizedHGFun (a := {c}) (b := {a, 2 * a - 1}) (by simp)
    (4 * (z ^ 3 / 9))).mul_left
    (4 * (3 : ℂ) ^ (-2 * a) * z ^ r * (Gamma (2 * a - 1) / Gamma a))).congr_fun fun n => ?_
  have hp : (ascPochhammer ℂ n).eval c = Gamma (c + n) / Gamma c :=
    (Gamma_add_nat_div_Gamma_eq c (ne_neg_natCast_of_re_pos hc_re)).symm
  have hGquot : Gamma (2 * a - 1) / Gamma a =
      Gamma c / ((2 : ℂ) ^ (1 - 2 * c) * ((√π : ℝ) : ℂ)) := by
    have hca : c + 1 / 2 = a := by linear_combination -hac
    rw [h2ac, ← hca]
    exact gamma_two_mul_div_gamma_add_half hc_re
  have h20 : (2 : ℂ) ^ (1 - 2 * c) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have h2pow : (2 : ℂ) ^ (2 * c) = 2 / (2 : ℂ) ^ (1 - 2 * c) := by
    rw [eq_div_iff h20, ← cpow_add _ _ two_ne_zero, add_sub_cancel, cpow_one]
  have h3pow : (3 : ℂ) ^ (-2 * a) =
      (3 : ℂ) ^ c * (3 : ℂ) ^ (-(2 * (r : ℂ) + 1) / 2) / 3 := by
    have he : -2 * a = c + -(2 * (r : ℂ) + 1) / 2 - 1 := by simp only [a, c]; push_cast; ring
    rw [he, cpow_sub _ _ (by norm_num), cpow_add _ _ (by norm_num), cpow_one]
  have harg : (2 * ((3 * n + r : ℕ) : ℂ) + 1) / 6 = c + n := by simp only [c]; push_cast; ring
  have hzr : z ^ (3 * n + r) = z ^ r * z ^ (3 * n) := by rw [pow_add, mul_comm]
  simp only [airyProductTerm, regularizedHGFunCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, harg, hp,
    four_mul_cube_div_nine_pow, hzr, twelve_cpow_add_natCast, h2pow, h3pow, hGquot, htrip n,
    pi_cpow_neg_three_halves]
  have : Gamma c ≠ 0 := Gamma_ne_zero (ne_neg_natCast_of_re_pos hc_re)
  have : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : (3 : ℂ) ^ (-(2 * (r : ℂ) + 1) / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have : ((3 * n + r)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (3 * n + r).factorial_ne_zero
  have : (9 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have : (3 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp
  ring

private theorem hasSum_airyProductTerm_mul_three (z : ℂ) :
    HasSum (fun n : ℕ => airyProductTerm z (3 * n))
      (4 * (3 : ℂ) ^ (-4 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) ^ 2) := by
  have h := hasSum_airyProductTerm_sq_piece 0 (fun n => by
    have ht := gamma_mul_add_third_nat 0 n
    have h1 : ((0 + 1 : ℕ) : ℂ) / 3 + n = 2 * (((0 + 2 : ℕ) : ℂ) / 3) - 1 + n := by
      push_cast; ring
    have h3 : ((0 + 3 : ℕ) : ℂ) / 3 + n = (n : ℂ) + 1 := by push_cast; ring
    rw [h1, h3, Gamma_nat_eq_factorial] at ht
    linear_combination ht) z
  have ha : ((0 + 2 : ℕ) : ℂ) / 3 = 2 / 3 := by norm_num
  have he : -2 * (2 / 3 : ℂ) = -4 / 3 := by norm_num
  simpa only [Nat.add_zero, pow_zero, mul_one, ha, he] using h

private theorem hasSum_airyProductTerm_mul_three_add_one (z : ℂ) :
    HasSum (fun n : ℕ => airyProductTerm z (3 * n + 1))
      (4 / 9 * z * (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
        regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))) := by
  have hpole : ∀ k : ℕ, (2 / 3 : ℂ) + 4 / 3 - 1 ≠ -k := ne_neg_natCast_of_re_pos (by norm_num)
  rw [regularizedHGFun_zero_singleton_mul_eq hpole (z ^ 3 / 9)]
  have hs1 : (2 / 3 : ℂ) + 4 / 3 - 1 = 1 := by norm_num
  have hs2 : ((2 / 3 : ℂ) + 4 / 3 - 1) / 2 = 1 / 2 := by norm_num
  have hs3 : ((2 / 3 : ℂ) + 4 / 3) / 2 = 1 := by norm_num
  rw [hs2, hs3, hs1, Gamma_one, one_mul]
  refine ((hasSum_regularizedHGFun (a := {(1 / 2 : ℂ), (1 : ℂ)})
    (b := {(2 / 3 : ℂ), (4 / 3 : ℂ), (1 : ℂ)}) (by simp) (4 * (z ^ 3 / 9))).mul_left
    (4 / 9 * z)).congr_fun fun n => ?_
  have hp2 : (ascPochhammer ℂ n).eval (1 / 2) = Gamma (1 / 2 + n) / ((√π : ℝ) : ℂ) := by
    rw [← Gamma_add_nat_div_Gamma_eq _ (ne_neg_natCast_of_re_pos (by norm_num)),
      Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
    push_cast; rfl
  have htrip : Gamma (2 / 3 + (n : ℂ)) * (Gamma (4 / 3 + n) * Gamma (1 + n)) =
      2 * π * ((3 : ℂ) ^ (-3 / 2 : ℂ) / (9 ^ n * 3 ^ n)) * ((3 * n + 1)! : ℂ) := by
    have ht := gamma_mul_add_third_nat 1 n
    have h2 : ((1 + 2 : ℕ) : ℂ) / 3 + n = 1 + n := by push_cast; ring
    have he : -(2 * ((1 : ℕ) : ℂ) + 1) / 2 = (-3 / 2 : ℂ) := by norm_num
    rw [h2, he] at ht
    simp only [Nat.reduceAdd, Nat.cast_ofNat] at ht
    linear_combination ht
  have h2pow : (2 : ℂ) ^ (2 * (1 / 2 : ℂ)) = 2 := by norm_num
  have h3pow : (3 : ℂ) ^ (-3 / 2 : ℂ) = ((3 : ℂ) ^ (1 / 2 : ℂ) * 3)⁻¹ := by
    have hexp : (-3 / 2 : ℂ) = -(1 / 2 + 1) := by norm_num
    rw [hexp, cpow_neg, cpow_add _ _ (by norm_num), cpow_one]
  have harg : (2 * ((3 * n + 1 : ℕ) : ℂ) + 1) / 6 = (1 / 2 : ℂ) + n := by push_cast; ring
  have hz1 : z ^ (3 * n + 1) = z * z ^ (3 * n) := pow_succ' z (3 * n)
  simp only [airyProductTerm, regularizedHGFunCoeff, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, harg,
    ascPochhammer_eval_one, hp2, four_mul_cube_div_nine_pow, hz1, twelve_cpow_add_natCast, h2pow,
    htrip, h3pow, pi_cpow_neg_three_halves]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have : (3 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have : ((3 * n + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (3 * n + 1).factorial_ne_zero
  have : (9 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have : (3 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp
  ring

private theorem hasSum_airyProductTerm_mul_three_add_two (z : ℂ) :
    HasSum (fun n : ℕ => airyProductTerm z (3 * n + 2))
      (4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
        regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) ^ 2) := by
  have h := hasSum_airyProductTerm_sq_piece 2 (fun n => by
    have ht := gamma_mul_add_third_nat 2 n
    have h1 : ((2 + 1 : ℕ) : ℂ) / 3 + n = (n : ℂ) + 1 := by push_cast; ring
    have h3 : ((2 + 3 : ℕ) : ℂ) / 3 + n = 2 * (((2 + 2 : ℕ) : ℂ) / 3) - 1 + n := by
      push_cast; ring
    rw [h1, h3, Gamma_nat_eq_factorial] at ht
    linear_combination ht) z
  have ha : ((2 + 2 : ℕ) : ℂ) / 3 = 4 / 3 := by norm_num
  have he : -2 * (4 / 3 : ℂ) = -8 / 3 := by norm_num
  simpa only [ha, he] using h

/-! ### Integral representation (DLMF 9.11.4) and Maclaurin series -/

private theorem continuousOn_cexp_sub_cubic_mul_cpow (b z s : ℂ) :
    ContinuousOn (fun t : ℝ => cexp (z * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ s) (Ioi 0) := by
  refine ContinuousOn.mul (by fun_prop) fun t ht => ?_
  exact (continuousAt_ofReal_cpow_const t s (Or.inr (mem_Ioi.mp ht).ne')).continuousWithinAt

private theorem cexp_sub_cubic_re (b z : ℂ) (t : ℝ) :
    (z * t - b * (t : ℂ) ^ 3).re = z.re * t - b.re * t ^ 3 := by
  simp [pow_three]

/-- For every `b : ℂ` with `0 < Re b`, every `z : ℂ`, and every `s : ℂ` with `-1 < Re s`, the
integrand `t ↦ exp(z * t - b * t ^ 3) * t ^ s` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_cexp_sub_cubic_mul_cpow {b : ℂ} (hb : 0 < b.re) (z : ℂ) {s : ℂ}
    (hs : -1 < s.re) :
    IntegrableOn (fun t : ℝ => cexp (z * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ s) (Ioi 0) := by
  set R : ℝ := |z.re| / b.re + 1
  set C : ℝ := b.re * R ^ 3
  have hdom : IntegrableOn
      (fun t : ℝ => Real.exp C * (t ^ s.re * Real.exp (-(b.re / 2) * t ^ (3 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow hs (by norm_num) (half_pos hb)).const_mul (Real.exp C)
  refine hdom.mono' ((continuousOn_cexp_sub_cubic_mul_cpow b z s).aestronglyMeasurable
    measurableSet_Ioi) ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
  replace ht : 0 < t := mem_Ioi.mp ht
  have hR1 : 1 ≤ R := by simp only [R]; linarith [div_nonneg (abs_nonneg z.re) hb.le]
  have hbR : |z.re| + b.re = b.re * R := by simp only [R]; field_simp
  have hbR2 : b.re * R ≤ b.re * R ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hb.le
  have hzR : z.re ≤ 3 / 2 * b.re * R ^ 2 := by
    linarith [le_abs_self z.re, mul_nonneg hb.le (sq_nonneg R)]
  have hsq : 0 ≤ b.re / 2 * (t - R) ^ 2 * (t + 2 * R) := by positivity
  have hbound_exp : z.re * t - b.re * t ^ 3 ≤ C - b.re / 2 * t ^ 3 := by
    have : (C - b.re / 2 * t ^ 3) - (z.re * t - b.re * t ^ 3) =
        b.re / 2 * (t - R) ^ 2 * (t + 2 * R) + (3 / 2 * b.re * R ^ 2 - z.re) * t := by
      simp only [C]; ring
    nlinarith
  rw [norm_mul, norm_exp, cexp_sub_cubic_re, norm_cpow_eq_rpow_re_of_pos ht, Real.rpow_ofNat]
  calc Real.exp (z.re * t - b.re * t ^ 3) * t ^ s.re
      ≤ Real.exp (C - b.re / 2 * t ^ 3) * t ^ s.re := by gcongr
    _ = Real.exp C * (t ^ s.re * Real.exp (-(b.re / 2) * t ^ 3)) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring

private theorem integral_cexp_neg_cubic_mul_cpow {q : ℝ} (hq : -1 < q) :
    ∫ t in Ioi (0 : ℝ), cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (q : ℂ) =
      (12 : ℂ) ^ (((q + 1) / 3 : ℝ) : ℂ) * Gamma (((q + 1) / 3 : ℝ) : ℂ) / 3 := by
  have hcongr : EqOn (fun t : ℝ => cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (q : ℂ))
      (fun t : ℝ => ((t ^ q * Real.exp (-(1 / 12) * t ^ (3 : ℝ)) : ℝ) : ℂ)) (Ioi 0) := by
    intro t ht
    dsimp only
    replace ht : 0 < t := mem_Ioi.mp ht
    have hexp : -((t : ℂ) ^ 3 / 12) = ((-(1 / 12) * t ^ (3 : ℝ) : ℝ) : ℂ) := by
      rw [Real.rpow_ofNat]; push_cast; ring
    rw [hexp, ← ofReal_exp, ← ofReal_cpow ht.le, ← ofReal_mul, mul_comm]
  have hofReal :
      ∫ t in Ioi (0 : ℝ), ((t ^ q * Real.exp (-(1 / 12) * t ^ (3 : ℝ)) : ℝ) : ℂ) =
        ((∫ t in Ioi (0 : ℝ), t ^ q * Real.exp (-(1 / 12) * t ^ (3 : ℝ)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm
      (integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num) (by norm_num))
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hofReal,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num)]
  have h12 : (1 / 12 : ℝ) ^ (-(q + 1) / 3) = (12 : ℝ) ^ ((q + 1) / 3) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  rw [h12, ofReal_mul, ofReal_mul, ofReal_cpow (by norm_num), Gamma_ofReal]
  push_cast
  ring

private theorem hasSum_norm_airyKernel_term {q : ℝ} (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ => (‖z‖ ^ m / m !) * (t ^ (m + q) * Real.exp (-(t ^ 3 / 12))))
      (t ^ q * Real.exp (‖z‖ * t - t ^ 3 / 12)) := by
  have h := (Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)).mul_right
    (t ^ q * Real.exp (-(t ^ 3 / 12)))
  rw [← mul_left_comm, ← Real.exp_add, ← sub_eq_add_neg] at h
  refine h.congr_fun fun m => ?_
  simp only [mul_pow, Real.rpow_add ht, Real.rpow_natCast]
  ring

private theorem hasSum_integral_cexp_sub_cubic_mul_cpow {q : ℝ} (hq : -1 < q) (z : ℂ) :
    HasSum
      (fun m : ℕ =>
        (12 : ℂ) ^ (((m + q + 1) / 3 : ℝ) : ℂ) * Gamma (((m + q + 1) / 3 : ℝ) : ℂ) /
          (3 * m !) * z ^ m)
      (∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (q : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun m t =>
    (z ^ m / m !) * (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ ((m + q : ℝ) : ℂ))
  set bound : ℕ → ℝ → ℝ := fun m t =>
    (‖z‖ ^ m / m !) * (t ^ (m + q) * Real.exp (-(t ^ 3 / 12)))
  have hF_meas (m : ℕ) : AEStronglyMeasurable (F m) (volume.restrict (Ioi 0)) := by
    have h0 (t : ℝ) : -((t : ℂ) ^ 3 / 12) = 0 * t - (1 / 12 : ℂ) * (t : ℂ) ^ 3 := by ring
    simp_rw [F, h0]
    exact ((continuousOn_cexp_sub_cubic_mul_cpow (1 / 12) 0 ((m + q : ℝ) : ℂ)).const_mul
      (z ^ m / m !)).aestronglyMeasurable measurableSet_Ioi
  have h_bound (m : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖F m t‖ ≤ bound m t := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    replace ht : 0 < t := mem_Ioi.mp ht
    have hexp_re : (-((t : ℂ) ^ 3 / 12)).re = -(t ^ 3 / 12) := by simp [pow_three]
    simp only [F, bound, norm_mul, norm_div, norm_pow, Complex.norm_natCast, norm_exp, hexp_re,
      norm_cpow_eq_rpow_re_of_pos ht, ofReal_re]
    exact le_of_eq (by ring)
  have bound_summable : ∀ᵐ t ∂volume.restrict (Ioi 0), Summable fun m => bound m t :=
    (ae_restrict_mem measurableSet_Ioi).mono fun _ ht =>
      (hasSum_norm_airyKernel_term z ht).summable
  have bound_integrable : Integrable (fun t => ∑' m, bound m t) (volume.restrict (Ioi 0)) := by
    refine (integrableOn_cexp_sub_cubic_mul_cpow (b := 1 / 12) (by norm_num) (‖z‖ : ℂ)
      (s := (q : ℂ)) (by simpa using hq)).norm.congr ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    dsimp only
    replace ht : 0 < t := mem_Ioi.mp ht
    rw [(hasSum_norm_airyKernel_term z ht).tsum_eq, norm_mul, norm_exp, cexp_sub_cubic_re,
      ofReal_re, norm_cpow_eq_rpow_re_of_pos ht, ofReal_re, mul_comm]
    congr 2
    norm_num
    ring
  have h_lim : ∀ᵐ t ∂volume.restrict (Ioi 0),
      HasSum (fun m => F m t) (cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (q : ℂ)) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    replace ht : 0 < t := mem_Ioi.mp ht
    have h := (Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp (z * t)).mul_right
      (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (q : ℂ))
    rw [← mul_assoc, ← Complex.exp_add, ← sub_eq_add_neg] at h
    refine h.congr_fun fun m => ?_
    have hcpow : (t : ℂ) ^ ((m + q : ℝ) : ℂ) = (t : ℂ) ^ m * (t : ℂ) ^ (q : ℂ) := by
      push_cast
      rw [cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast]
    simp only [F, mul_pow, hcpow]
    ring
  refine (hasSum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable
    bound_integrable h_lim).congr_fun fun m => ?_
  have hmq : -1 < (m : ℝ) + q := by linarith [m.cast_nonneg (α := ℝ)]
  rw [integral_const_mul, integral_cexp_neg_cubic_mul_cpow hmq]
  ring

private theorem hasSum_airyProductTerm_integral (z : ℂ) :
    HasSum (airyProductTerm z)
      ((π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
  have hint := (hasSum_integral_cexp_sub_cubic_mul_cpow (q := -1 / 2) (by norm_num) z).mul_left
    ((π : ℂ) ^ (-3 / 2 : ℂ))
  have hq : ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) := by norm_num
  rw [hq] at hint
  refine hint.congr_fun fun m => ?_
  have harg : (((m + (-1 / 2 : ℝ) + 1) / 3 : ℝ) : ℂ) = (2 * (m : ℂ) + 1) / 6 := by
    push_cast; ring
  rw [airyProductTerm, harg]
  ring

/-- **Integral representation of `Ai(z)² + Bi(z)²` (DLMF 9.11.4).** For every `z : ℂ`,
`airyAi z ^ 2 + airyBi z ^ 2 = π ^ (-3 / 2) * ∫ t in Ioi 0, exp(z t - t³ / 12) * t ^ (-1 / 2)`. -/
theorem airyAi_sq_add_airyBi_sq_eq_integral (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
  have hblock := HasSum.sum_fin_add_add_nat (hasSum_airyProductTerm_integral z) 3
  have hmod := ((hasSum_airyProductTerm_mul_three z).add
    (hasSum_airyProductTerm_mul_three_add_one z)).add
    (hasSum_airyProductTerm_mul_three_add_two z)
  rw [← airyAi_sq_add_airyBi_sq_hypergeometric z] at hmod
  refine hmod.unique (hblock.congr_fun fun n => ?_)
  simp [Fin.sum_univ_three, Nat.mul_comm n 3]

/-- **Maclaurin series of `Ai(z)² + Bi(z)²`.** For every `z : ℂ`, the power series with `m`-th
coefficient `π ^ (-3 / 2) * 12 ^ ((2m + 1) / 6) * Γ((2m + 1) / 6) / (3 * m!)` converges to
`airyAi z ^ 2 + airyBi z ^ 2`. -/
theorem hasSum_airyAi_sq_add_airyBi_sq (z : ℂ) :
    HasSum
      (fun m : ℕ =>
        (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ ((2 * (m : ℂ) + 1) / 6) *
          Gamma ((2 * (m : ℂ) + 1) / 6) / (3 * m !) * z ^ m)
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral z]
  exact hasSum_airyProductTerm_integral z

/-- At the origin, `Ai(0)² + Bi(0)² = π ^ (-3 / 2) * 12 ^ (1 / 6) * Γ(1 / 6) / 3`. -/
theorem airyAi_zero_sq_add_airyBi_zero_sq :
    airyAi 0 ^ 2 + airyBi 0 ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3 := by
  refine (hasSum_airyAi_sq_add_airyBi_sq 0).unique ?_
  convert hasSum_single (0 : ℕ) fun m hm => ?_ using 1
  · simp
  · simp [zero_pow hm]

/-- At the origin, `4 * Ai(0)² = π ^ (-3 / 2) * 12 ^ (1 / 6) * Γ(1 / 6) / 3` (DLMF 9.11.4 at
`z = 0`). -/
theorem four_mul_airyAi_zero_sq :
    4 * airyAi 0 ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3 := by
  have hbi : airyBi 0 ^ 2 = 3 * airyAi 0 ^ 2 := by
    have h16 : (3 : ℂ) ^ (-1 / 6 : ℂ) = (3 : ℂ) ^ (1 / 2 : ℂ) * (3 : ℂ) ^ (-2 / 3 : ℂ) := by
      rw [← cpow_add _ _ (by norm_num)]; norm_num
    have hs : ((3 : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = 3 := by
      rw [sq, ← cpow_add _ _ (by norm_num)]; norm_num
    rw [airyAi_zero, airyBi_zero, h16]
    linear_combination ((3 : ℂ) ^ (-2 / 3 : ℂ) / Gamma (2 / 3)) ^ 2 * hs
  linear_combination airyAi_zero_sq_add_airyBi_zero_sq - hbi

/-! ### Parametric derivatives of the integral representation -/

/-- Differentiating `z ↦ ∫ t in Ioi 0, exp(z t - b t³) * t ^ s` under the integral sign shifts the
power exponent `s` to `s + 1` whenever `0 < Re b` and `-1 < Re s`. -/
theorem hasDerivAt_integral_cexp_sub_cubic_mul_cpow {b : ℂ} (hb : 0 < b.re) (z : ℂ) {s : ℂ}
    (hs : -1 < s.re) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), cexp (w * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ s)
      (∫ t in Ioi (0 : ℝ), cexp (z * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ (s + 1)) z := by
  have hs1 : -1 < (s + 1).re := by simp; linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (t : ℝ) => cexp (w * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ s)
    (F' := fun (w : ℂ) (t : ℝ) => cexp (w * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ (s + 1))
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := fun t => ‖cexp ((z + 1) * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ (s + 1)‖)
    (Metric.ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall fun w =>
      (continuousOn_cexp_sub_cubic_mul_cpow b w s).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_cexp_sub_cubic_mul_cpow hb z hs)
    ((continuousOn_cexp_sub_cubic_mul_cpow b z (s + 1)).aestronglyMeasurable measurableSet_Ioi)
    ?_ (integrableOn_cexp_sub_cubic_mul_cpow hb (z + 1) hs1).norm ?_).2
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht w hw => ?_
    replace ht : 0 < t := mem_Ioi.mp ht
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw_re : w.re ≤ (z + 1).re := by
      have hdist : (w - z).re ≤ 1 := (re_le_norm (w - z)).trans hw.le
      simp only [sub_re, add_re, one_re] at hdist ⊢
      linarith
    rw [norm_mul, norm_mul, norm_exp, norm_exp, cexp_sub_cubic_re, cexp_sub_cubic_re,
      norm_cpow_eq_rpow_re_of_pos ht]
    gcongr
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht w _ => ?_
    replace ht : 0 < t := mem_Ioi.mp ht
    have hlin : HasDerivAt (fun u : ℂ => u * t - b * (t : ℂ) ^ 3) (t : ℂ) w := by
      simpa using ((hasDerivAt_id w).mul_const (t : ℂ)).sub_const (b * (t : ℂ) ^ 3)
    have hd := (hlin.cexp).mul_const ((t : ℂ) ^ s)
    have hpow : cexp (w * t - b * (t : ℂ) ^ 3) * (t : ℂ) * (t : ℂ) ^ s =
        cexp (w * t - b * (t : ℂ) ^ 3) * (t : ℂ) ^ (s + 1) := by
      rw [mul_assoc, cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_one, mul_comm (t : ℂ)]
    rwa [hpow] at hd

/-- **Iterated derivatives of DLMF 9.11.4.** For every `k : ℕ` and `z : ℂ`,
`deriv^[k] (fun w => airyAi w ^ 2 + airyBi w ^ 2) z` equals
`π ^ (-3 / 2) * ∫ t in Ioi 0, exp(z t - t³ / 12) * t ^ (k - 1 / 2)`. -/
theorem iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral (k : ℕ) (z : ℂ) :
    deriv^[k] (fun w => airyAi w ^ 2 + airyBi w ^ 2) z =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ ((k : ℂ) - 1 / 2) := by
  induction k generalizing z with
  | zero =>
    simpa [zero_sub, neg_div] using airyAi_sq_add_airyBi_sq_eq_integral z
  | succ k ih =>
    have hdiv (u : ℂ) (t : ℝ) : u * t - (t : ℂ) ^ 3 / 12 = u * t - (1 / 12 : ℂ) * (t : ℂ) ^ 3 := by
      ring
    rw [Function.iterate_succ_apply', funext ih]
    simp_rw [hdiv]
    have hk : -1 < ((k : ℂ) - 1 / 2).re := by
      simp only [sub_re, natCast_re, one_re, div_ofNat_re]
      linarith [k.cast_nonneg (α := ℝ)]
    have hd := (hasDerivAt_integral_cexp_sub_cubic_mul_cpow (b := 1 / 12) (by norm_num) z
      hk).const_mul ((π : ℂ) ^ (-3 / 2 : ℂ))
    have hshift : ((k : ℂ) - 1 / 2) + 1 = ((k + 1 : ℕ) : ℂ) - 1 / 2 := by push_cast; ring
    rw [hshift] at hd
    exact hd.deriv

/-- **First derivative of DLMF 9.11.4.** For every `z : ℂ`,
`airyAi z * deriv airyAi z + airyBi z * deriv airyBi z =
  (π ^ (-3 / 2) / 2) * ∫ t in Ioi 0, exp(z t - t³ / 12) * t ^ (1 / 2)`. -/
theorem airyAi_mul_deriv_add_airyBi_mul_deriv_eq_integral (z : ℂ) :
    airyAi z * deriv airyAi z + airyBi z * deriv airyBi z =
      (π : ℂ) ^ (-3 / 2 : ℂ) / 2 *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (1 / 2 : ℂ) := by
  have hdAi := (differentiable_airyAi z).hasDerivAt
  have hdBi := (differentiable_airyBi z).hasDerivAt
  have hd : HasDerivAt (fun w => airyAi w ^ 2 + airyBi w ^ 2)
      (2 * airyAi z * deriv airyAi z + 2 * airyBi z * deriv airyBi z) z := by
    have h := (hdAi.pow 2).add (hdBi.pow 2)
    rw [Pi.add_def, Pi.pow_def, Pi.pow_def] at h
    simpa [pow_one] using h
  have h1 := iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral 1 z
  have hhalf : ((1 : ℕ) : ℂ) - 1 / 2 = (1 / 2 : ℂ) := by norm_num
  rw [Function.iterate_one, hhalf, hd.deriv] at h1
  linear_combination h1 / 2

end TauCeti
