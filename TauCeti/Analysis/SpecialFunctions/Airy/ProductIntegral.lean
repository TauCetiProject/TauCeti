/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.SpecialFunctions.Gamma.Multiplication
import TauCeti.MeasureTheory.Integral.Exp.PowerLaplace
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Integral representation of `Ai(z)² + Bi(z)²`

This file proves the integral representation (DLMF 9.11.4)

`Ai(z)² + Bi(z)² = π ^ (-3 / 2) * ∫ t in Ioi (0 : ℝ), exp (z * t - t ^ 3 / 12) * t ^ (-1 / 2)`

for every complex `z`, together with the absolute convergence of the integral, the everywhere
convergent Maclaurin series of `Ai(z)² + Bi(z)²`, the origin evaluation
`4 * Ai(0)² = π ^ (-3 / 2) * 12 ^ (1 / 6) * Γ(1 / 6) / 3`, and positivity on the real line.

Expanding `Ai(z)² + Bi(z)²` from the defining `₀F₁` representations splits it into three products
of regularized hypergeometric functions. Applying
`Complex.hasSum_regularizedHGFun_zero_singleton_mul` yields the residue classes modulo `3` of the
Maclaurin series; Legendre's duplication formula and Gauss's triplication formula identify all
three classes uniformly with the Gamma coefficients of the cubic-exponential Laplace integral.

## Main results

* `TauCeti.integrableOn_airyAi_sq_add_airyBi_sq_integrand`: the integrand
  `t ↦ exp (z * t - t ^ 3 / 12) * t ^ (-1 / 2)` is integrable on `(0, ∞)` for every `z : ℂ`.
* `TauCeti.airyAi_sq_add_airyBi_sq_eq_integral`: DLMF 9.11.4 for every `z : ℂ`.
* `TauCeti.hasSum_airyAi_sq_add_airyBi_sq`: the everywhere convergent Maclaurin series of
  `Ai(z)² + Bi(z)²`.
* `TauCeti.airyAi_sq_add_airyBi_sq_zero`, `TauCeti.four_mul_airyAi_zero_sq`: evaluation at `z = 0`.
* `TauCeti.airyAi_sq_add_airyBi_sq_ofReal`, `TauCeti.airyAi_sq_add_airyBi_sq_ofReal_re_pos`,
  `TauCeti.airyAi_sq_add_airyBi_sq_ofReal_ne_zero`: real integral form and strict positivity on `ℝ`.

## References

* *NIST Digital Library of Mathematical Functions*, §9.11(i),
  <https://dlmf.nist.gov/9.11.i>.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Nat Real

namespace TauCeti

/-- Expanding `Ai(z)² + Bi(z)²` in terms of the two defining `₀F₁` hypergeometric functions. -/
private theorem airyAi_sq_add_airyBi_sq_eq_hgFun (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) *
          (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
            regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) +
        4 * (3 : ℂ) ^ (-2 : ℂ) * z *
          (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
            regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) +
        4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
          (regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) *
            regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hcomb (a b c d e : ℂ) (hab : a + b = e) (hcd : c + d = e + 1) :
      (3 : ℂ) ^ a * (3 : ℂ) ^ b + (3 : ℂ) ^ c * (3 : ℂ) ^ d = 4 * (3 : ℂ) ^ e := by
    rw [← cpow_add _ _ h3, ← cpow_add _ _ h3, hab, hcd, cpow_add _ _ h3, cpow_one]
    ring
  have h1 : ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 + ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    rw [sq, sq]
    exact hcomb _ _ _ _ _ (by ring) (by ring)
  have h2 : -2 * (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) +
      2 * (3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-5 / 6 : ℂ) = 4 * (3 : ℂ) ^ (-2 : ℂ) := by
    have h12 : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) = (3 : ℂ) ^ (-2 : ℂ) := by
      rw [← cpow_add _ _ h3]; congr 1; ring
    have h34 : (3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-5 / 6 : ℂ) = 3 * (3 : ℂ) ^ (-2 : ℂ) := by
      have he : (-1 / 6 : ℂ) + -5 / 6 = -2 + 1 := by ring
      rw [← cpow_add _ _ h3, he, cpow_add _ _ h3, cpow_one]; ring
    linear_combination -2 * h12 + 2 * h34
  have h3' : ((3 : ℂ) ^ (-4 / 3 : ℂ)) ^ 2 + ((3 : ℂ) ^ (-5 / 6 : ℂ)) ^ 2 =
      4 * (3 : ℂ) ^ (-8 / 3 : ℂ) := by
    rw [sq, sq]
    exact hcomb _ _ _ _ _ (by ring) (by ring)
  set F₀ := regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
  set F₁ := regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)
  rw [airyAi_def, airyBi_def]
  linear_combination F₀ ^ 2 * h1 + F₀ * F₁ * z * h2 + F₁ ^ 2 * z ^ 2 * h3'

/-- Gauss's triplication formula instantiated at `m + (r + 1) / 3`. -/
private theorem airy_product_gamma_triplication (m r : ℕ) :
    Gamma ((m : ℂ) + ((r : ℂ) + 1) / 3) * Gamma ((m : ℂ) + ((r : ℂ) + 2) / 3) *
        Gamma ((m : ℂ) + ((r : ℂ) + 3) / 3) =
      2 * (π : ℂ) * (3 : ℂ) ^ (1 / 2 - (3 * (m : ℂ) + r + 1)) * ((3 * m + r)! : ℂ) := by
  have h := Gamma_mul_Gamma_add_third ((m : ℂ) + ((r : ℂ) + 1) / 3)
  have h1 : (m : ℂ) + ((r : ℂ) + 1) / 3 + 1 / 3 = m + (r + 2) / 3 := by ring
  have h2 : (m : ℂ) + ((r : ℂ) + 1) / 3 + 2 / 3 = m + (r + 3) / 3 := by ring
  have h3 : 3 * ((m : ℂ) + ((r : ℂ) + 1) / 3) = ((3 * m + r : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [h1, h2, h3, Gamma_nat_eq_factorial] at h
  simpa [Nat.cast_add, Nat.cast_mul] using h

/-- Legendre's duplication formula instantiated at `m + (2r + 1) / 6`. -/
private theorem airy_product_gamma_duplication (m r : ℕ) :
    Gamma ((2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6) * Gamma ((m : ℂ) + ((r : ℂ) + 2) / 3) =
      Gamma (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3) *
        (2 : ℂ) ^ (1 - (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3)) * (π : ℂ) ^ (1 / 2 : ℂ) := by
  have h := Gamma_mul_Gamma_add_half ((m : ℂ) + (2 * (r : ℂ) + 1) / 6)
  have h0 : (m : ℂ) + (2 * (r : ℂ) + 1) / 6 = (2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6 := by
    push_cast; ring
  have h1 : (m : ℂ) + (2 * (r : ℂ) + 1) / 6 + 1 / 2 = m + (r + 2) / 3 := by ring
  have h2 : 2 * ((m : ℂ) + (2 * (r : ℂ) + 1) / 6) = 2 * m + (2 * r + 1) / 3 := by ring
  have hsqrt : ((√π : ℝ) : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; norm_num
  rwa [h1, h2, h0, hsqrt] at h

/-- Unified Gamma-function identity matching all three residue classes modulo `3` of the
hypergeometric product series for `Ai(z)² + Bi(z)²` with the coefficients of the cubic-exponential
Laplace integral, via Gauss's triplication formula and Legendre's duplication formula. -/
private theorem airy_product_coeff_gamma (m r : ℕ) :
    4 * (3 : ℂ) ^ (-(2 * (m : ℂ)) - (4 + 2 * (r : ℂ)) / 3) *
        Gamma (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3) /
      (Gamma ((m : ℂ) + ((r : ℂ) + 1) / 3) * Gamma ((m : ℂ) + ((r : ℂ) + 2) / 3) ^ 2 *
        Gamma ((m : ℂ) + ((r : ℂ) + 3) / 3)) =
      (π : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((12 : ℂ) ^ ((2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6) / 3 *
          Gamma ((2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6) / ((3 * m + r)! : ℂ)) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set e : ℂ := (2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6
  set e₂ : ℂ := 1 - (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3)
  set e₃ : ℂ := 1 / 2 - (3 * (m : ℂ) + r + 1)
  set G₂ : ℂ := Gamma ((m : ℂ) + ((r : ℂ) + 2) / 3)
  set F : ℂ := ((3 * m + r)! : ℂ)
  have h12 : (12 : ℂ) ^ e = (2 : ℂ) ^ (2 * e) * (3 : ℂ) ^ e := by
    have h12_eq : (12 : ℂ) = ((4 : ℝ) : ℂ) * ((3 : ℝ) : ℂ) := by norm_num
    have h4_eq : ((4 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) := by norm_num
    rw [h12_eq, mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), h4_eq,
      mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), ← cpow_add _ _ (by norm_num)]
    norm_num [two_mul]
  have hpow2 : (2 : ℂ) ^ (2 * e) * (2 : ℂ) ^ e₂ = 2 := by
    rw [← cpow_add _ _ h2]
    convert cpow_one (2 : ℂ) using 2
    simp only [e, e₂]; push_cast; ring
  have hpow3 : (3 : ℂ) ^ e * (3 : ℂ) ^ e₃ =
      3 * (3 : ℂ) ^ (-(2 * (m : ℂ)) - (4 + 2 * (r : ℂ)) / 3) := by
    have he : e + e₃ = 1 + (-(2 * (m : ℂ)) - (4 + 2 * (r : ℂ)) / 3) := by
      simp only [e, e₃]; push_cast; ring
    rw [← cpow_add _ _ h3, he, cpow_add _ _ h3, cpow_one]
  have hpowπ : (π : ℂ) ^ (-(3 / 2 : ℂ)) * (π : ℂ) ^ (1 / 2 : ℂ) * (π : ℂ) = 1 := by
    have he : -(3 / 2 : ℂ) + 1 / 2 = -1 := by ring
    rw [← cpow_add _ _ hπ, he, cpow_neg_one, inv_mul_cancel₀ hπ]
  have hG2 : G₂ ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re, natCast_re, div_ofNat_re, re_ofNat]; positivity)
  have hfac : F ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3pow_ne : (3 : ℂ) ^ e₃ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl h3)
  have hdenom : Gamma ((m : ℂ) + ((r : ℂ) + 1) / 3) * G₂ ^ 2 *
      Gamma ((m : ℂ) + ((r : ℂ) + 3) / 3) = (2 * (π : ℂ) * (3 : ℂ) ^ e₃ * F) * G₂ := by
    linear_combination G₂ * airy_product_gamma_triplication m r
  rw [hdenom, h12, div_mul_eq_mul_div, div_div, mul_div_assoc',
    div_eq_div_iff (by positivity) (mul_ne_zero h3 hfac)]
  symm
  calc (π : ℂ) ^ (-(3 / 2 : ℂ)) * ((2 : ℂ) ^ (2 * e) * (3 : ℂ) ^ e * Gamma e) *
        (2 * (π : ℂ) * (3 : ℂ) ^ e₃ * F * G₂)
      = 2 * F * ((π : ℂ) ^ (-(3 / 2 : ℂ)) * (π : ℂ)) * (2 : ℂ) ^ (2 * e) *
          ((3 : ℂ) ^ e * (3 : ℂ) ^ e₃) * (Gamma e * G₂) := by ring
    _ = 2 * F * ((π : ℂ) ^ (-(3 / 2 : ℂ)) * (π : ℂ) ^ (1 / 2 : ℂ) * (π : ℂ)) *
          ((2 : ℂ) ^ (2 * e) * (2 : ℂ) ^ e₂) * ((3 : ℂ) ^ e * (3 : ℂ) ^ e₃) *
          Gamma (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3) := by
        rw [airy_product_gamma_duplication m r]; ring
    _ = _ := by rw [hpowπ, hpow2, hpow3]; ring

/-- Rewriting the `m`-th term of each of the three `₀F₁ · ₀F₁` product series at `z³ / 9` into the
unified `n = 3m + r` coefficient form. -/
private theorem airy_product_term_eq (b c : ℂ) (r : ℕ) (m : ℕ) (z : ℂ)
    (hbc : b + c - 1 = (2 * (r : ℂ) + 1) / 3)
    (hre : 0 < ((m : ℂ) + (2 * (r : ℂ) + 1) / 3).re)
    (hden : Gamma ((m : ℂ) + (2 * (r : ℂ) + 1) / 3) * (m ! : ℂ) * Gamma (b + m) * Gamma (c + m) =
      Gamma ((m : ℂ) + ((r : ℂ) + 1) / 3) * Gamma ((m : ℂ) + ((r : ℂ) + 2) / 3) ^ 2 *
        Gamma ((m : ℂ) + ((r : ℂ) + 3) / 3)) :
    4 * (3 : ℂ) ^ (-(4 + 2 * (r : ℂ)) / 3) * z ^ r *
        ((ascPochhammer ℂ m).eval (b + c + m - 1) /
          (m ! * Gamma (b + m) * Gamma (c + m)) * (z ^ 3 / 9) ^ m) =
      (π : ℂ) ^ (-(3 / 2 : ℂ)) *
        (z ^ (3 * m + r) / ((3 * m + r)! : ℂ) *
          ((12 : ℂ) ^ ((2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6) / 3 *
            Gamma ((2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6))) := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have harg : b + c + (m : ℂ) - 1 = (m : ℂ) + (2 * (r : ℂ) + 1) / 3 := by linear_combination hbc
  have hpoch : (ascPochhammer ℂ m).eval ((m : ℂ) + (2 * (r : ℂ) + 1) / 3) =
      Gamma (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3) /
        Gamma ((m : ℂ) + (2 * (r : ℂ) + 1) / 3) := by
    rw [← Gamma_add_nat_div_Gamma_eq _ (ne_neg_natCast_of_re_pos hre)]
    congr 2
    ring
  have h9 : (9 : ℂ) ^ m = (3 : ℂ) ^ (2 * (m : ℂ)) := by
    have h9_eq : (9 : ℂ) = (3 : ℂ) ^ (2 : ℕ) := by norm_num
    rw [h9_eq, ← pow_mul, ← cpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have h3pow : (3 : ℂ) ^ (-(4 + 2 * (r : ℂ)) / 3) / (3 : ℂ) ^ (2 * (m : ℂ)) =
      (3 : ℂ) ^ (-(2 * (m : ℂ)) - (4 + 2 * (r : ℂ)) / 3) := by
    rw [← cpow_sub _ _ h3]
    congr 1
    ring
  have hcoeff := airy_product_coeff_gamma m r
  rw [harg, hpoch, div_pow, ← pow_mul, h9]
  calc 4 * (3 : ℂ) ^ (-(4 + 2 * (r : ℂ)) / 3) * z ^ r *
        (Gamma (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3) / Gamma ((m : ℂ) + (2 * (r : ℂ) + 1) / 3) /
          (m ! * Gamma (b + m) * Gamma (c + m)) * (z ^ (3 * m) / (3 : ℂ) ^ (2 * (m : ℂ))))
      = (4 * ((3 : ℂ) ^ (-(4 + 2 * (r : ℂ)) / 3) / (3 : ℂ) ^ (2 * (m : ℂ))) *
          Gamma (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3) /
          (Gamma ((m : ℂ) + (2 * (r : ℂ) + 1) / 3) * (m ! : ℂ) * Gamma (b + m) * Gamma (c + m))) *
          (z ^ (3 * m) * z ^ r) := by ring
    _ = (4 * (3 : ℂ) ^ (-(2 * (m : ℂ)) - (4 + 2 * (r : ℂ)) / 3) *
          Gamma (2 * (m : ℂ) + (2 * (r : ℂ) + 1) / 3) /
          (Gamma ((m : ℂ) + ((r : ℂ) + 1) / 3) * Gamma ((m : ℂ) + ((r : ℂ) + 2) / 3) ^ 2 *
            Gamma ((m : ℂ) + ((r : ℂ) + 3) / 3))) * z ^ (3 * m + r) := by
          rw [h3pow, hden, ← pow_add]
    _ = _ := by rw [hcoeff]; ring

/-- Residue class `n = 3m + r` of the Maclaurin series of `Ai(z)² + Bi(z)²` summed as a product of
regularized `₀F₁` functions. -/
private theorem hasSum_airyProduct_residue (b c : ℂ) (r : ℕ) (z : ℂ)
    (hbc : b + c - 1 = (2 * (r : ℂ) + 1) / 3)
    (hden : ∀ m : ℕ,
      Gamma ((m : ℂ) + (2 * (r : ℂ) + 1) / 3) * (m ! : ℂ) * Gamma (b + m) * Gamma (c + m) =
        Gamma ((m : ℂ) + ((r : ℂ) + 1) / 3) * Gamma ((m : ℂ) + ((r : ℂ) + 2) / 3) ^ 2 *
          Gamma ((m : ℂ) + ((r : ℂ) + 3) / 3)) :
    HasSum
      (fun m : ℕ =>
        (π : ℂ) ^ (-(3 / 2 : ℂ)) *
          (z ^ (3 * m + r) / ((3 * m + r)! : ℂ) *
            ((12 : ℂ) ^ ((2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6) / 3 *
              Gamma ((2 * ((3 * m + r : ℕ) : ℂ) + 1) / 6))))
      (4 * (3 : ℂ) ^ (-(4 + 2 * (r : ℂ)) / 3) * z ^ r *
        (regularizedHGFun 0 {b} (z ^ 3 / 9) * regularizedHGFun 0 {c} (z ^ 3 / 9))) :=
  ((hasSum_regularizedHGFun_zero_singleton_mul b c (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-(4 + 2 * (r : ℂ)) / 3) * z ^ r)).congr_fun fun m =>
    (airy_product_term_eq b c r m z hbc
      (by
        simp only [add_re, natCast_re, div_ofNat_re, mul_re, re_ofNat, im_ofNat, zero_mul,
          sub_zero, one_re]
        positivity)
      (hden m)).symm

/-- The cubic-exponential Laplace integrand `t ↦ exp (z * t - t ^ 3 / 12) * t ^ (-1 / 2)` is
integrable on `(0, ∞)` for every `z : ℂ`. -/
theorem integrableOn_airyAi_sq_add_airyBi_sq_integrand (z : ℂ) :
    IntegrableOn (fun t : ℝ => cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-(1 / 2 : ℂ)))
      (Ioi 0) := by
  have h := integrableOn_cpow_mul_cexp_mul_sub_mul_cpow_Ioi (p := 3) (by norm_num)
    (b := (1 / 12 : ℂ)) (by norm_num) (s := -(1 / 2 : ℂ)) (by norm_num) z
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  have h3 : ((3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ) := by norm_num
  dsimp only
  rw [mul_comm, h3, cpow_natCast]
  congr 2
  ring

/-- The scaled cubic-exponential Laplace integral in DLMF 9.11.4 equals the sum of its Maclaurin
series. -/
private theorem hasSum_airyProduct_integral (z : ℂ) :
    HasSum
      (fun n : ℕ =>
        (π : ℂ) ^ (-(3 / 2 : ℂ)) *
          (z ^ n / (n ! : ℂ) *
            ((12 : ℂ) ^ ((2 * (n : ℂ) + 1) / 6) / 3 * Gamma ((2 * (n : ℂ) + 1) / 6))))
      ((π : ℂ) ^ (-(3 / 2 : ℂ)) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-(1 / 2 : ℂ))) := by
  have h := (hasSum_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi (p := 3) (by norm_num)
    (b := (1 / 12 : ℂ)) (by norm_num) (s := -(1 / 2 : ℂ)) (by norm_num) z).mul_left
    ((π : ℂ) ^ (-(3 / 2 : ℂ)))
  have h12 (w : ℂ) : (1 / 12 : ℂ) ^ (-w) = (12 : ℂ) ^ w := by
    have harg : arg (12 : ℂ) ≠ Real.pi := by
      rw [← ofReal_ofNat, arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_pos.ne
    rw [one_div, inv_cpow _ _ harg, cpow_neg, inv_inv]
  convert h using 1
  · ext n
    have hexp : (-(1 / 2 : ℂ) + (n : ℂ) + 1) / ((3 : ℝ) : ℂ) = (2 * (n : ℂ) + 1) / 6 := by
      push_cast; ring
    have hneg : -(-(1 / 2 : ℂ) + (n : ℂ) + 1) / ((3 : ℝ) : ℂ) = -((2 * (n : ℂ) + 1) / 6) := by
      push_cast; ring
    rw [hexp, hneg, h12]
    push_cast
    ring
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have h3 : ((3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ) := by norm_num
    rw [mul_comm, h3, cpow_natCast]
    congr 2
    ring

/-- **DLMF 9.11.4.** For every complex `z`,
`Ai(z)² + Bi(z)² = π ^ (-3 / 2) * ∫ t in Ioi 0, exp (z * t - t ^ 3 / 12) * t ^ (-1 / 2)`. -/
theorem airyAi_sq_add_airyBi_sq_eq_integral (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      (π : ℂ) ^ (-(3 / 2 : ℂ)) *
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hr0 := hasSum_airyProduct_residue (2 / 3) (2 / 3) 0 z (by norm_num) fun m => by
    have h1 : (2 / 3 : ℂ) + m = m + ((0 : ℕ) + 2) / 3 := by push_cast; ring
    have h2 : (m : ℂ) + (2 * (0 : ℕ) + 1) / 3 = m + ((0 : ℕ) + 1) / 3 := by push_cast; ring
    have h3 : (m : ℂ) + 1 = m + ((0 : ℕ) + 3) / 3 := by push_cast; ring
    rw [← Gamma_nat_eq_factorial, h1, h2, h3]
    ring
  have hr1 := hasSum_airyProduct_residue (2 / 3) (4 / 3) 1 z (by norm_num) fun m => by
    have h1 : (2 / 3 : ℂ) + m = m + ((1 : ℕ) + 1) / 3 := by push_cast; ring
    have h2 : (m : ℂ) + (2 * (1 : ℕ) + 1) / 3 = m + ((1 : ℕ) + 2) / 3 := by push_cast; ring
    have h3 : (m : ℂ) + 1 = m + ((1 : ℕ) + 2) / 3 := by push_cast; ring
    have h4 : (4 / 3 : ℂ) + m = m + ((1 : ℕ) + 3) / 3 := by push_cast; ring
    rw [← Gamma_nat_eq_factorial, h1, h2, h3, h4]
    ring
  have hr2 := hasSum_airyProduct_residue (4 / 3) (4 / 3) 2 z (by norm_num) fun m => by
    have h1 : (m : ℂ) + 1 = m + ((2 : ℕ) + 1) / 3 := by push_cast; ring
    have h2 : (4 / 3 : ℂ) + m = m + ((2 : ℕ) + 2) / 3 := by push_cast; ring
    have h3 : (m : ℂ) + (2 * (2 : ℕ) + 1) / 3 = m + ((2 : ℕ) + 3) / 3 := by push_cast; ring
    rw [← Gamma_nat_eq_factorial, h1, h2, h3]
    ring
  have hAiry : HasSum
      (fun m : ℕ =>
        ∑ r : Fin 3,
          (π : ℂ) ^ (-(3 / 2 : ℂ)) *
            (z ^ (m * 3 + r) / ((m * 3 + r)! : ℂ) *
              ((12 : ℂ) ^ ((2 * ((m * 3 + r : ℕ) : ℂ) + 1) / 6) / 3 *
                Gamma ((2 * ((m * 3 + r : ℕ) : ℂ) + 1) / 6))))
      (airyAi z ^ 2 + airyBi z ^ 2) := by
    rw [airyAi_sq_add_airyBi_sq_eq_hgFun]
    convert (hr0.add hr1).add hr2 using 1
    · ext m
      simp [Fin.sum_univ_three, mul_comm m 3]
    · norm_num
  exact hAiry.unique ((hasSum_airyProduct_integral z).sum_fin_add_add_nat 3)

/-- The everywhere convergent Maclaurin series of `Ai(z)² + Bi(z)²`:
`Ai(z)² + Bi(z)² = π ^ (-3 / 2) * ∑' n, z ^ n / n! * (12 ^ ((2n + 1) / 6) / 3 * Γ ((2n + 1) / 6))`.
-/
theorem hasSum_airyAi_sq_add_airyBi_sq (z : ℂ) :
    HasSum
      (fun n : ℕ =>
        (π : ℂ) ^ (-(3 / 2 : ℂ)) *
          (z ^ n / (n ! : ℂ) *
            ((12 : ℂ) ^ ((2 * (n : ℂ) + 1) / 6) / 3 * Gamma ((2 * (n : ℂ) + 1) / 6))))
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral]
  exact hasSum_airyProduct_integral z

/-- At the origin, `Ai(0)² + Bi(0)² = 4 * Ai(0)²`, since `Bi(0) = √3 * Ai(0)`. -/
theorem airyAi_sq_add_airyBi_sq_zero : airyAi 0 ^ 2 + airyBi 0 ^ 2 = 4 * airyAi 0 ^ 2 := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hpow : ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 = 3 * ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 := by
    have he : (-1 / 6 : ℂ) + -1 / 6 = 1 + ((-2 / 3 : ℂ) + -2 / 3) := by ring
    rw [sq, sq, ← cpow_add _ _ h3, ← cpow_add _ _ h3, he, cpow_add _ _ h3, cpow_one]
  simp only [airyAi_zero, airyBi_zero, div_pow, hpow]
  ring

/-- DLMF 9.11.4 at `z = 0`: `4 * Ai(0)² = π ^ (-3 / 2) * 12 ^ (1 / 6) * Γ(1 / 6) / 3`. -/
theorem four_mul_airyAi_zero_sq :
    4 * airyAi 0 ^ 2 =
      (π : ℂ) ^ (-(3 / 2 : ℂ)) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3 := by
  have h0 := hasSum_airyAi_sq_add_airyBi_sq 0
  have hsingle : HasSum
      (fun n : ℕ =>
        (π : ℂ) ^ (-(3 / 2 : ℂ)) *
          ((0 : ℂ) ^ n / (n ! : ℂ) *
            ((12 : ℂ) ^ ((2 * (n : ℂ) + 1) / 6) / 3 * Gamma ((2 * (n : ℂ) + 1) / 6))))
      ((π : ℂ) ^ (-(3 / 2 : ℂ)) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3) := by
    have hs := hasSum_single (0 : ℕ) (f := fun n : ℕ =>
      (π : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((0 : ℂ) ^ n / (n ! : ℂ) *
          ((12 : ℂ) ^ ((2 * (n : ℂ) + 1) / 6) / 3 * Gamma ((2 * (n : ℂ) + 1) / 6))))
      (fun n hn => by simp [zero_pow hn])
    convert hs using 1
    simp only [Nat.cast_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      mul_zero, zero_add]
    ring
  rw [← airyAi_sq_add_airyBi_sq_zero]
  exact h0.unique hsingle

/-- On the real line, `Ai(x)² + Bi(x)²` equals the real cubic-exponential Laplace integral
`π ^ (-3 / 2) * ∫ t in Ioi 0, exp (x * t - t ^ 3 / 12) * t ^ (-1 / 2)`. -/
theorem airyAi_sq_add_airyBi_sq_ofReal (x : ℝ) :
    airyAi x ^ 2 + airyBi x ^ 2 =
      (((π : ℝ) ^ (-(3 / 2 : ℝ)) *
        ∫ t in Ioi (0 : ℝ), Real.exp (x * t - t ^ 3 / 12) * t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral, ofReal_mul, ofReal_cpow Real.pi_pos.le,
    ← integral_complex_ofReal]
  congr 1
  · push_cast
    rfl
  · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [ofReal_mul, ofReal_exp, ofReal_cpow ht.le]
    push_cast
    ring_nf

/-- On the real line, `(Ai(x)² + Bi(x)²).re` is strictly positive. -/
theorem airyAi_sq_add_airyBi_sq_ofReal_re_pos (x : ℝ) :
    0 < (airyAi x ^ 2 + airyBi x ^ 2).re := by
  rw [airyAi_sq_add_airyBi_sq_ofReal, ofReal_re]
  refine mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) ?_
  have hint : IntegrableOn (fun t : ℝ => Real.exp (x * t - t ^ 3 / 12) * t ^ (-(1 / 2 : ℝ)))
      (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_mul_sub_mul_rpow_Ioi (p := 3) (b := 1 / 12)
      (by norm_num) (by norm_num) (s := -(1 / 2 : ℝ)) (by norm_num) x
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    dsimp only
    rw [mul_comm, h3, Real.rpow_natCast]
    congr 2
    ring
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hint).2 ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    positivity
  · have hsupp : Function.support
        (fun t : ℝ => Real.exp (x * t - t ^ 3 / 12) * t ^ (-(1 / 2 : ℝ))) ∩ Ioi 0 = Ioi 0 := by
      ext t
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
      intro ht
      positivity
    rw [hsupp, Real.volume_Ioi]
    simp

/-- On the real line, `Ai(x)² + Bi(x)²` never vanishes. -/
theorem airyAi_sq_add_airyBi_sq_ofReal_ne_zero (x : ℝ) :
    airyAi x ^ 2 + airyBi x ^ 2 ≠ 0 := fun h =>
  (airyAi_sq_add_airyBi_sq_ofReal_re_pos x).ne' (by simp [h])

end TauCeti
