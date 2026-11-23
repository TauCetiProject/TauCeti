/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Derivatives of the Bessel function of the first kind and Bessel's equation

Mathlib defines the Bessel function of the first kind as
`Complex.besselJ ν z = (z / 2) ^ ν ₀F₁(; ν + 1; -(z / 2) ^ 2)`, with the principal complex power
and the regularized hypergeometric function, and proves that it is holomorphic in `z` on the slit
plane. This file differentiates it there. The derivative of `₀F₁(; b; ·)` is `₀F₁(; b + 1; ·)`,
which gives `J_ν′(z) = (ν / z) J_ν(z) − J_{ν+1}(z)`; Mathlib's three-term recurrence
`2ν J_ν(z) = z J_{ν−1}(z) + z J_{ν+1}(z)` converts it into the other forms. Together they show
that `J_ν` solves Bessel's equation `z² w'' + z w′ + (z² − ν²) w = 0` on the slit plane, for every
complex order `ν`, and they express every iterated derivative of `J_ν` through the `J_μ` with
`μ − ν` an integer.

The ladder relations `(z⁻¹ d/dz)ᵏ (z^ν J_ν(z)) = z^{ν−k} J_{ν−k}(z)` and
`(z⁻¹ d/dz)ᵏ (z^{−ν} J_ν(z)) = (−1)ᵏ z^{−ν−k} J_{ν+k}(z)` are the form of the recurrences used for
the spherical Bessel functions. The operator `z⁻¹ d/dz` is written
`fun f w => w⁻¹ * deriv f w` and its `k`-th power is a `Nat.iterate`.

## Main results

* `Complex.hasDerivAt_besselJ`: `J_ν′(z) = (ν / z) J_ν(z) − J_{ν+1}(z)` on the slit plane, and
  `Complex.hasDerivAt_besselJ'`: `J_ν′(z) = J_{ν−1}(z) − (ν / z) J_ν(z)` (DLMF 10.6.2).
* `Complex.besselJ_sub_one_sub_besselJ_add_one`: `J_{ν−1}(z) − J_{ν+1}(z) = 2 J_ν′(z)`
  (the second identity of DLMF 10.6.1).
* `Complex.besselJ_ode`: Bessel's equation `z² J_ν''(z) + z J_ν′(z) + (z² − ν²) J_ν(z) = 0` on the
  slit plane (DLMF 10.2.1).
* `Complex.iteratedDeriv_besselJ`: `J_ν⁽ᵏ⁾(z) = 2⁻ᵏ ∑ₙ₌₀ᵏ (−1)ⁿ (k choose n) J_{ν−k+2n}(z)`
  (DLMF 10.6.7).
* `Complex.hasDerivAt_cpow_mul_besselJ`, `Complex.hasDerivAt_cpow_neg_mul_besselJ`: the
  derivatives of `z^ν J_ν(z)` and `z^{−ν} J_ν(z)`.
* `Complex.iterate_inv_mul_deriv_cpow_mul_besselJ`,
  `Complex.iterate_inv_mul_deriv_cpow_neg_mul_besselJ`: the ladder relations (DLMF 10.6.6).

## References

* *NIST Digital Library of Mathematical Functions*, §10.2 (Bessel's equation) and §10.6
  (recurrence relations and derivatives).
* N. M. Temme, *Special Functions: An Introduction to the Classical Functions of Mathematical
  Physics*, Wiley, 1996, (9.1) and (9.16)–(9.18).
* G. E. Andrews, R. Askey and R. Roy, *Special Functions*, Cambridge University Press, 1999,
  (4.6.1)–(4.6.8).
-/

public section

noncomputable section

open scoped Topology

namespace Complex

/-- The derivative of the Bessel function of the first kind on the slit plane:
`J_ν′(z) = (ν / z) J_ν(z) − J_{ν+1}(z)`. -/
theorem hasDerivAt_besselJ (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ ν) (ν / z * besselJ ν z - besselJ (ν + 1) z) z := by
  have hz2 : z / 2 ∈ slitPlane := by simpa [slitPlane] using hz
  have hz0 : z / 2 ≠ 0 := slitPlane_ne_zero hz2
  have hd : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) z := (hasDerivAt_id' z).div_const 2
  have hpow : HasDerivAt (fun w : ℂ => (w / 2) ^ ν) (ν * (z / 2) ^ (ν - 1) * (1 / 2)) z :=
    hd.cpow_const hz2
  have hg : HasDerivAt (fun w : ℂ => -(w / 2) ^ 2) (-(2 * (z / 2) ^ 1 * (1 / 2))) z :=
    (hd.pow 2).neg
  have hF : HasDerivAt (fun w : ℂ => regularizedHGFun 0 {ν + 1} (-(w / 2) ^ 2))
      (regularizedHGFun 0 {ν + 1 + 1} (-(z / 2) ^ 2) * -(2 * (z / 2) ^ 1 * (1 / 2))) z :=
    (hasDerivAt_regularizedHGFun_zero_singleton (ν + 1) (-(z / 2) ^ 2)).comp z hg
  refine (hpow.mul hF).congr_deriv ?_
  simp only [besselJ, cpow_sub _ _ hz0, cpow_add _ _ hz0, cpow_one]
  field_simp
  ring

/-- The derivative of the Bessel function of the first kind on the slit plane, in the form
`J_ν′(z) = J_{ν−1}(z) − (ν / z) J_ν(z)`. -/
theorem hasDerivAt_besselJ' (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ ν) (besselJ (ν - 1) z - ν / z * besselJ ν z) z := by
  have hz0 := slitPlane_ne_zero hz
  refine (hasDerivAt_besselJ ν hz).congr_deriv ?_
  have h := two_mul_self_mul_besselJ ν z
  field_simp
  linear_combination h

/-- The derivative of the Bessel function of the first kind on the slit plane, as a value of
`deriv`: `J_ν′(z) = (ν / z) J_ν(z) − J_{ν+1}(z)`. -/
theorem deriv_besselJ (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (besselJ ν) z = ν / z * besselJ ν z - besselJ (ν + 1) z :=
  (hasDerivAt_besselJ ν hz).deriv

/-- The second identity of DLMF 10.6.1 for `J_ν`: `J_{ν−1}(z) − J_{ν+1}(z) = 2 J_ν′(z)` on the
slit plane. -/
theorem besselJ_sub_one_sub_besselJ_add_one (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselJ (ν - 1) z - besselJ (ν + 1) z = 2 * deriv (besselJ ν) z := by
  rw [deriv_besselJ ν hz]
  have hz0 := slitPlane_ne_zero hz
  have h := two_mul_self_mul_besselJ ν z
  field_simp
  linear_combination -h

/-- Bessel's equation (DLMF 10.2.1): on the slit plane, `J_ν` satisfies
`z² J_ν''(z) + z J_ν′(z) + (z² − ν²) J_ν(z) = 0`, for every complex order `ν`. -/
theorem besselJ_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * deriv^[2] (besselJ ν) z + z * deriv (besselJ ν) z + (z ^ 2 - ν ^ 2) * besselJ ν z =
      0 := by
  have hz0 := slitPlane_ne_zero hz
  have hd : deriv (besselJ ν) =ᶠ[𝓝 z] fun w => ν / w * besselJ ν w - besselJ (ν + 1) w := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    exact deriv_besselJ ν hw
  have hJ₁ := hasDerivAt_besselJ' (ν + 1) hz
  rw [add_sub_cancel_right] at hJ₁
  have h2 : HasDerivAt (fun w => ν / w * besselJ ν w - besselJ (ν + 1) w)
      ((0 * z - ν * 1) / z ^ 2 * besselJ ν z + ν / z * (ν / z * besselJ ν z - besselJ (ν + 1) z) -
        (besselJ ν z - (ν + 1) / z * besselJ (ν + 1) z)) z :=
    (((hasDerivAt_const z ν).div (hasDerivAt_id' z) hz0).mul (hasDerivAt_besselJ ν hz)).sub hJ₁
  rw [Function.iterate_succ_apply', Function.iterate_one, hd.deriv_eq, h2.deriv,
    deriv_besselJ ν hz]
  field_simp
  ring

/-- The iterated derivatives of the Bessel function of the first kind on the slit plane
(DLMF 10.6.7): `J_ν⁽ᵏ⁾(z) = 2⁻ᵏ ∑ₙ₌₀ᵏ (−1)ⁿ (k choose n) J_{ν−k+2n}(z)`. -/
theorem iteratedDeriv_besselJ (ν : ℂ) (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv k (besselJ ν) z =
      (2 ^ k)⁻¹ * ∑ n ∈ Finset.range (k + 1), (-1) ^ n * (k.choose n : ℂ) *
        besselJ (ν - k + 2 * n) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have heq : iteratedDeriv k (besselJ ν) =ᶠ[𝓝 z] fun w => (2 ^ k)⁻¹ *
        ∑ n ∈ Finset.range (k + 1), (-1) ^ n * (k.choose n : ℂ) * besselJ (ν - k + 2 * n) w := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have hJ (μ : ℂ) : HasDerivAt (besselJ μ) ((besselJ (μ - 1) z - besselJ (μ + 1) z) / 2) z := by
      rw [besselJ_sub_one_sub_besselJ_add_one μ hz, mul_div_cancel_left₀ _ two_ne_zero]
      exact (analyticAt_besselJ μ hz).differentiableAt.hasDerivAt
    have hsum := (HasDerivAt.fun_sum fun n (_ : n ∈ Finset.range (k + 1)) =>
      (hJ (ν - k + 2 * n)).const_mul ((-1) ^ n * (k.choose n : ℂ))).const_mul (2 ^ k)⁻¹
    rw [iteratedDeriv_succ, heq.deriv_eq, hsum.deriv]
    -- the Pascal rule `C(k + 1, n) = C(k, n) + C(k, n - 1)` for the alternating binomial sum
    have hpascal (a : ℕ → ℂ) :
        ∑ n ∈ Finset.range (k + 1 + 1), (-1) ^ n * ((k + 1).choose n : ℂ) * a n =
          ∑ n ∈ Finset.range (k + 1), (-1) ^ n * (k.choose n : ℂ) * (a n - a (n + 1)) := by
      calc _ = ∑ n ∈ Finset.range (k + 2), ((k + 1).choose n : ℂ) * ((-1) ^ n * a n) :=
            Finset.sum_congr rfl fun n _ => by ring
        _ = _ := Finset.sum_choose_succ_mul (fun n _ => (-1) ^ n * a n) k
        _ = _ := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun n _ => by ring
    have h₁ (n : ℕ) : besselJ (ν - k + 2 * n - 1) z = besselJ (ν - (k + 1 : ℕ) + 2 * n) z := by
      congr 1; push_cast; ring
    have h₂ (n : ℕ) :
        besselJ (ν - k + 2 * n + 1) z = besselJ (ν - (k + 1 : ℕ) + 2 * (n + 1 : ℕ)) z := by
      congr 1; push_cast; ring
    have h := hpascal fun n => besselJ (ν - (k + 1 : ℕ) + 2 * n) z
    simp only [h₁, h₂]
    rw [h, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring

/-- The derivative of `z^ν J_ν(z)` on the slit plane is `z^ν J_{ν−1}(z)`. -/
theorem hasDerivAt_cpow_mul_besselJ (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => w ^ ν * besselJ ν w) (z ^ ν * besselJ (ν - 1) z) z := by
  have hz0 := slitPlane_ne_zero hz
  refine (((hasDerivAt_id' z).cpow_const (c := ν) hz).mul (hasDerivAt_besselJ' ν hz)).congr_deriv
    ?_
  rw [cpow_sub _ _ hz0, cpow_one]
  field_simp
  ring

/-- The derivative of `z^{−ν} J_ν(z)` on the slit plane is `−z^{−ν} J_{ν+1}(z)`. -/
theorem hasDerivAt_cpow_neg_mul_besselJ (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => w ^ (-ν) * besselJ ν w) (-(z ^ (-ν) * besselJ (ν + 1) z)) z := by
  have hz0 := slitPlane_ne_zero hz
  refine (((hasDerivAt_id' z).cpow_const (c := -ν) hz).mul (hasDerivAt_besselJ ν hz)).congr_deriv
    ?_
  rw [cpow_sub _ _ hz0, cpow_one]
  field_simp
  ring

/-- The ladder relation of DLMF 10.6.6 for `z^ν J_ν(z)`: on the slit plane,
`(z⁻¹ d/dz)ᵏ (z^ν J_ν(z)) = z^{ν−k} J_{ν−k}(z)`. -/
theorem iterate_inv_mul_deriv_cpow_mul_besselJ (ν : ℂ) (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    (fun (f : ℂ → ℂ) (w : ℂ) => w⁻¹ * deriv f w)^[k] (fun w => w ^ ν * besselJ ν w) z =
      z ^ (ν - k) * besselJ (ν - k) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have heq : (fun (f : ℂ → ℂ) (w : ℂ) => w⁻¹ * deriv f w)^[k] (fun w => w ^ ν * besselJ ν w)
        =ᶠ[𝓝 z] fun w => w ^ (ν - k) * besselJ (ν - k) w := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have hk : ν - (k + 1 : ℕ) = ν - k - 1 := by push_cast; ring
    rw [Function.iterate_succ_apply', heq.deriv_eq,
      (hasDerivAt_cpow_mul_besselJ (ν - k) hz).deriv, hk,
      cpow_sub (ν - k) 1 (slitPlane_ne_zero hz), cpow_one]
    ring

/-- The ladder relation of DLMF 10.6.6 for `z^{−ν} J_ν(z)`: on the slit plane,
`(z⁻¹ d/dz)ᵏ (z^{−ν} J_ν(z)) = (−1)ᵏ z^{−ν−k} J_{ν+k}(z)`. -/
theorem iterate_inv_mul_deriv_cpow_neg_mul_besselJ (ν : ℂ) (k : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    (fun (f : ℂ → ℂ) (w : ℂ) => w⁻¹ * deriv f w)^[k] (fun w => w ^ (-ν) * besselJ ν w) z =
      (-1) ^ k * z ^ (-ν - k) * besselJ (ν + k) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have heq : (fun (f : ℂ → ℂ) (w : ℂ) => w⁻¹ * deriv f w)^[k] (fun w => w ^ (-ν) * besselJ ν w)
        =ᶠ[𝓝 z] fun w => (-1) ^ k * (w ^ (-(ν + k)) * besselJ (ν + k) w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, neg_add', mul_assoc]
    have hk₁ : -ν - (k + 1 : ℕ) = -(ν + k) - 1 := by push_cast; ring
    have hk₂ : ν + (k + 1 : ℕ) = ν + k + 1 := by push_cast; ring
    rw [Function.iterate_succ_apply', heq.deriv_eq,
      ((hasDerivAt_cpow_neg_mul_besselJ (ν + k) hz).const_mul _).deriv, hk₁, hk₂,
      cpow_sub (-(ν + k)) 1 (slitPlane_ne_zero hz), cpow_one, pow_succ]
    ring

end Complex
