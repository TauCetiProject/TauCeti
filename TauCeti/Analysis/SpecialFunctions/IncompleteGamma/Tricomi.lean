/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.EulerIntegral
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Parameters
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Transformation

/-!
# Tricomi's entire incomplete Gamma function

Tricomi's function `γ*(a, z) = e^{−z} 𝐌(1, a + 1, z)` (DLMF 8.5.2), where
`𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)` is Mathlib's regularized Kummer function
`Complex.regularizedHGFun {1} {b}`, is the normalization of the lower incomplete Gamma function
that is entire in both the parameter `a` and the argument `z`: classically
`γ(a, z) = Γ(a) z^a γ*(a, z)`, and `γ*` absorbs both the branch of `z^a` and the poles of `Γ`.
It is the base from which the complex incomplete Gamma functions, the exponential integrals and
the error function (`erf z = z γ*(1/2, z²)`) are built.

## Main definitions

* `Complex.tricomiIncompleteGamma a z` — Tricomi's function `γ*(a, z)`.

## Main results

* `Complex.hasSum_tricomiIncompleteGamma` — the series
  `γ*(a, z) = e^{−z} ∑ zᵏ / Γ(a + k + 1)` (DLMF 8.7.1), for all `a` and `z`;
* `Complex.tricomiIncompleteGamma_eq_regularizedHGFun` — the Kummer representation
  `γ*(a, z) = 𝐌(a, a + 1, −z)` (DLMF 8.5.2), for all `a` and `z`;
* `Complex.hasSum_tricomiIncompleteGamma_of_ne_neg_natCast` — the series
  `γ*(a, z) = Γ(a)⁻¹ ∑ (−z)ᵏ / (k! (a + k))` (DLMF 8.7.1), for `a ∉ −ℕ`, and its real form
  `Complex.hasSum_Gamma_mul_re_tricomiIncompleteGamma_ofReal`;
* `Complex.ofReal_tricomiIncompleteGamma_ofReal_re`, `Complex.tricomiIncompleteGamma_ofReal_im` —
  `γ*(a, x)` is real for real `a` and `x`;
* `Complex.tricomiIncompleteGamma_eq_integral` — the integral
  `γ*(a, z) = Γ(a)⁻¹ ∫₀¹ t^{a−1} e^{−zt} dt` (DLMF 8.2.7), for `0 < Re a`;
* `Complex.tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one` — the
  recurrence `γ*(a, z) = z γ*(a + 1, z) + e^{−z} / Γ(a + 1)` in the parameter (DLMF §8.8);
* `Complex.tricomiIncompleteGamma_zero_right`, `tricomiIncompleteGamma_neg_natCast`,
  `tricomiIncompleteGamma_zero_left`, `tricomiIncompleteGamma_one_left` — the special values
  `γ*(a, 0) = 1 / Γ(a + 1)` (DLMF 8.4.2), `γ*(−n, z) = zⁿ` (DLMF 8.4.12), `γ*(0, z) = 1` and
  `γ*(1, z) = (1 − e^{−z}) / z` for `z ≠ 0`;
* `Complex.hasDerivAt_tricomiIncompleteGamma` — `∂γ*(a, z)/∂z = −a γ*(a + 1, z)`, so that
  `γ*(a, ·)` is entire (`differentiable_tricomiIncompleteGamma`);
* `Complex.iteratedDeriv_tricomiIncompleteGamma` — the `n`th derivative
  `∂ⁿγ*(a, z)/∂zⁿ = (−1)ⁿ (a)ₙ γ*(a + n, z)`;
* `Complex.hasSum_tricomiIncompleteGamma_add` — the addition theorem, the Taylor expansion
  `γ*(a, z + h) = ∑ₖ (−1)ᵏ (a)ₖ γ*(a + k, z) hᵏ / k!`, for every `a`, `z` and `h`;
* `Complex.hasSum_tricomiIncompleteGamma_mul` — the multiplication theorem for `γ*`,
  `γ*(a, tz) = ∑ₖ (a)ₖ γ*(a + k, z) zᵏ (1 − t)ᵏ / k!`, for every `a`, `z` and `t` (DLMF 8.15.1 in
  terms of `γ*`, with DLMF's `λ` written `t`);
* `Complex.differentiable_tricomiIncompleteGamma_left` — `γ*(·, z)` is entire;
* `Complex.tricomiIncompleteGamma_ode` — the differential equation
  `z w'' + (a + 1 + z) w' + a w = 0` (DLMF 8.2.14).

## Implementation

Mathlib's convention `Γ(−n) = 0` makes `1 / Γ` entire, so the series 8.7.1 in its first form holds
for every `a` with no case split.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.2](https://dlmf.nist.gov/8.2),
  [§8.4](https://dlmf.nist.gov/8.4), [§8.5](https://dlmf.nist.gov/8.5),
  [§8.7](https://dlmf.nist.gov/8.7), [§8.8](https://dlmf.nist.gov/8.8) and
  [§8.15](https://dlmf.nist.gov/8.15).
* F. G. Tricomi, *Sulla funzione gamma incompleta*, Ann. Mat. Pura Appl. (4) 31 (1950).
-/

public section

noncomputable section

open Complex Filter Finset Set
open scoped Nat Topology Interval

namespace Complex

/-- Tricomi's entire incomplete Gamma function `γ*(a, z) = e^{−z} 𝐌(1, a + 1, z)` (DLMF 8.5.2),
written through Mathlib's regularized Kummer function `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)`. It is
entire in each of `a` and `z`; for `a ∉ −ℕ` and `z` off the cut, the lower incomplete Gamma
function is `γ(a, z) = Γ(a) z^a γ*(a, z)`. -/
def tricomiIncompleteGamma (a z : ℂ) : ℂ :=
  cexp (-z) * regularizedHGFun {1} {a + 1} z

/-- Unfolding `tricomiIncompleteGamma` to Mathlib's regularized Kummer function. -/
theorem tricomiIncompleteGamma_def (a z : ℂ) :
    tricomiIncompleteGamma a z = cexp (-z) * regularizedHGFun {1} {a + 1} z := (rfl)

/-- The power series of Tricomi's function (DLMF 8.7.1):
`γ*(a, z) = e^{−z} ∑ zᵏ / Γ(a + k + 1)`, for all `a` and `z`. -/
theorem hasSum_tricomiIncompleteGamma (a z : ℂ) :
    HasSum (fun k : ℕ => cexp (-z) * z ^ k / Gamma (a + k + 1)) (tricomiIncompleteGamma a z) := by
  rw [tricomiIncompleteGamma_def]
  refine ((hasSum_regularizedHGFun (a := {1}) (b := {a + 1}) (by simp) z).mul_left
    (cexp (-z))).congr_fun fun k => ?_
  rw [regularizedHGFunCoeff_one_singleton, add_right_comm, div_eq_mul_inv]
  ring

/-- Tricomi's function is real for real `a` and `x`: the terms `e^{−x} xᵏ / Γ(a + k + 1)` of its
series (DLMF 8.7.1) are real. -/
@[simp]
theorem ofReal_tricomiIncompleteGamma_ofReal_re (a x : ℝ) :
    ((tricomiIncompleteGamma a x).re : ℂ) = tricomiIncompleteGamma a x := by
  have h : HasSum (fun k : ℕ => ((Real.exp (-x) * x ^ k / Real.Gamma (a + k + 1) : ℝ) : ℂ))
      (tricomiIncompleteGamma a x) := by
    refine (hasSum_tricomiIncompleteGamma a x).congr_fun fun k => ?_
    simp [← Gamma_ofReal]
  rw [← (hasSum_ofReal.mpr (summable_ofReal.mp h.summable).hasSum).unique h, ofReal_re]

/-- Tricomi's function has vanishing imaginary part for real `a` and `x`. -/
@[simp]
theorem tricomiIncompleteGamma_ofReal_im (a x : ℝ) : (tricomiIncompleteGamma a x).im = 0 := by
  rw [← ofReal_tricomiIncompleteGamma_ofReal_re, ofReal_im]

/-- The recurrence of Tricomi's function in its parameter (DLMF §8.8):
`γ*(a, z) = z γ*(a + 1, z) + e^{−z} / Γ(a + 1)`. -/
theorem tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a z : ℂ) :
    tricomiIncompleteGamma a z =
      z * tricomiIncompleteGamma (a + 1) z + cexp (-z) / Gamma (a + 1) := by
  rw [tricomiIncompleteGamma_def, tricomiIncompleteGamma_def,
    regularizedHGFun_one_singleton_eq_inv_Gamma_add_mul (a + 1) z, div_eq_mul_inv]
  ring

/-- The value of Tricomi's function at `z = 0` (DLMF 8.4.2): `γ*(a, 0) = 1 / Γ(a + 1)`. This is
`0` at `a ∈ {−1, −2, …}`. -/
@[simp]
theorem tricomiIncompleteGamma_zero_right (a : ℂ) :
    tricomiIncompleteGamma a 0 = (Gamma (a + 1))⁻¹ := by
  simp [tricomiIncompleteGamma_def]

/-- At `a = 0`, Tricomi's function is identically `1`. -/
@[simp]
theorem tricomiIncompleteGamma_zero_left (z : ℂ) : tricomiIncompleteGamma 0 z = 1 := by
  have hexp : HasSum (fun k : ℕ => z ^ k / k !) (cexp z) :=
    Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp z
  refine (hasSum_tricomiIncompleteGamma 0 z).unique ?_
  have h := hexp.mul_left (cexp (-z))
  rw [← Complex.exp_add, neg_add_cancel, exp_zero] at h
  refine h.congr_fun fun k => ?_
  rw [zero_add, Gamma_nat_eq_factorial, mul_div_assoc]

/-- At a nonpositive integer parameter, Tricomi's function is a monomial (DLMF 8.4.12):
`γ*(−n, z) = zⁿ`. -/
@[simp]
theorem tricomiIncompleteGamma_neg_natCast (n : ℕ) (z : ℂ) :
    tricomiIncompleteGamma (-n) z = z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one]
    have h : -((n + 1 : ℕ) : ℂ) + 1 = -n := by push_cast; ring
    rw [h, ih, Gamma_neg_nat_eq_zero, div_zero, add_zero, pow_succ']

/-- At `a = 1`, Tricomi's function is `γ*(1, z) = (1 − e^{−z}) / z` for `z ≠ 0`; at `z = 0` it
is `γ*(1, 0) = 1` by `tricomiIncompleteGamma_zero_right`. -/
theorem tricomiIncompleteGamma_one_left {z : ℂ} (hz : z ≠ 0) :
    tricomiIncompleteGamma 1 z = (1 - cexp (-z)) / z := by
  have h := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one 0 z
  rw [tricomiIncompleteGamma_zero_left, zero_add, Gamma_one, div_one] at h
  rw [eq_div_iff hz]
  linear_combination -h

/-! ### Differentiability in the argument -/

/-- The derivative of Tricomi's function in its argument:
`∂γ*(a, z)/∂z = −a γ*(a + 1, z)`. -/
theorem hasDerivAt_tricomiIncompleteGamma (a z : ℂ) :
    HasDerivAt (tricomiIncompleteGamma a) (-a * tricomiIncompleteGamma (a + 1) z) z := by
  have hd := hasDerivAt_regularizedHGFun_singleton 1 (a + 1) z
  have hrel := regularizedHGFun_singleton_eq_sub_mul_add_mul 1 (a + 1) z
  convert ((hasDerivAt_neg z).cexp).mul hd using 1
  · exact funext (tricomiIncompleteGamma_def a)
  · rw [tricomiIncompleteGamma_def]
    linear_combination cexp (-z) * hrel

/-- The derivative of Tricomi's function in its argument, as a function:
`∂γ*(a, ·)/∂z = −a γ*(a + 1, ·)`. -/
@[simp]
theorem deriv_tricomiIncompleteGamma (a : ℂ) :
    deriv (tricomiIncompleteGamma a) = fun z => -a * tricomiIncompleteGamma (a + 1) z :=
  funext fun z => (hasDerivAt_tricomiIncompleteGamma a z).deriv

/-- Tricomi's function is entire in its argument. -/
theorem differentiable_tricomiIncompleteGamma (a : ℂ) :
    Differentiable ℂ (tricomiIncompleteGamma a) :=
  fun z => (hasDerivAt_tricomiIncompleteGamma a z).differentiableAt

/-- The `n`th derivative of Tricomi's function in its argument:
`∂ⁿγ*(a, z)/∂zⁿ = (−1)ⁿ (a)ₙ γ*(a + n, z)`. -/
theorem iteratedDeriv_tricomiIncompleteGamma (n : ℕ) (a : ℂ) :
    iteratedDeriv n (tricomiIncompleteGamma a) =
      fun z => (-1) ^ n * (ascPochhammer ℂ n).eval a * tricomiIncompleteGamma (a + n) z := by
  induction n with
  | zero => funext z; simp
  | succ n ih =>
    funext z
    rw [iteratedDeriv_succ, ih]
    have h := ((hasDerivAt_tricomiIncompleteGamma (a + n) z).const_mul
      ((-1) ^ n * (ascPochhammer ℂ n).eval a)).deriv
    rw [h, ascPochhammer_succ_eval, Nat.cast_succ, ← add_assoc]
    ring

/-- **The addition theorem** for Tricomi's function, its Taylor expansion about `z`:
`γ*(a, z + h) = ∑ₖ (−1)ᵏ (a)ₖ γ*(a + k, z) hᵏ / k!` for every `a`, `z` and `h`. -/
theorem hasSum_tricomiIncompleteGamma_add (a z h : ℂ) :
    HasSum (fun k : ℕ => (-1) ^ k * (ascPochhammer ℂ k).eval a *
        tricomiIncompleteGamma (a + k) z * h ^ k / k !)
      (tricomiIncompleteGamma a (z + h)) := by
  have ht := hasSum_taylorSeries_of_entire (differentiable_tricomiIncompleteGamma a) z (z + h)
  refine ht.congr_fun fun k => ?_
  rw [iteratedDeriv_tricomiIncompleteGamma, add_sub_cancel_left, smul_eq_mul, smul_eq_mul]
  ring

/-- **The multiplication theorem** for Tricomi's function (DLMF 8.15.1 in terms of `γ*`):
`γ*(a, tz) = ∑ₖ (a)ₖ γ*(a + k, z) zᵏ (1 − t)ᵏ / k!` for every `a`, `z` and `t`. -/
theorem hasSum_tricomiIncompleteGamma_mul (a z t : ℂ) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * tricomiIncompleteGamma (a + k) z *
        z ^ k * (1 - t) ^ k / k !)
      (tricomiIncompleteGamma a (t * z)) := by
  -- The Taylor expansion about `z` with increment `(t - 1) z` evaluates `γ*(a, ·)` at `t z`.
  have hzt : z + (t - 1) * z = t * z := by ring
  have h := hasSum_tricomiIncompleteGamma_add a z ((t - 1) * z)
  rw [hzt] at h
  refine h.congr_fun fun k => ?_
  -- Writing `(t - 1) z = (−1) ((1 − t) z)` turns `((t - 1) z)ᵏ` into `(−1)ᵏ (1 − t)ᵏ zᵏ`, whose
  -- sign cancels the `(−1)ᵏ` of the addition theorem.
  have hneg : (t - 1) * z = -1 * ((1 - t) * z) := by ring
  have h1 : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [hneg, mul_pow, mul_pow]
  linear_combination (-((ascPochhammer ℂ k).eval a * tricomiIncompleteGamma (a + k) z *
    z ^ k * (1 - t) ^ k / k !)) * h1

/-- The differential equation of Tricomi's function (DLMF 8.2.14):
`z w'' + (a + 1 + z) w' + a w = 0` for `w = γ*(a, ·)`. -/
theorem tricomiIncompleteGamma_ode (a z : ℂ) :
    z * deriv (deriv (tricomiIncompleteGamma a)) z +
      (a + 1 + z) * deriv (tricomiIncompleteGamma a) z + a * tricomiIncompleteGamma a z = 0 := by
  have h2 : deriv (deriv (tricomiIncompleteGamma a)) z =
      -a * (-(a + 1) * tricomiIncompleteGamma (a + 1 + 1) z) := by
    rw [deriv_tricomiIncompleteGamma]
    exact ((hasDerivAt_tricomiIncompleteGamma (a + 1) z).const_mul (-a)).deriv
  have h₀ := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one a z
  have h₁ := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a + 1) z
  have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + 1)
  rw [h2, deriv_tricomiIncompleteGamma]
  simp only [div_eq_mul_inv] at h₀ h₁
  linear_combination a * h₀ - a * (a + 1) * h₁ + a * cexp (-z) * hΓ

/-! ### Entirety in the parameter -/

/-- Tricomi's function is entire in its parameter, since the regularized Kummer function
`𝐌(1, a + 1, z)` is entire in `a` (`Differentiable.regularizedHGFun_singleton`). -/
theorem differentiable_tricomiIncompleteGamma_left (z : ℂ) :
    Differentiable ℂ fun a => tricomiIncompleteGamma a z := by
  simp only [tricomiIncompleteGamma_def]
  fun_prop

/-! ### The series in powers of `−z` and the integral -/

/- By Kummer's transformation, `γ*(a, z) = e^{−z} 𝐌(1, a + 1, z) = 𝐌(a, a + 1, −z)`, whose series
is the second form of 8.7.1; the integral 8.2.7 is Kummer's integral for `𝐌(1, a + 1, z)`. -/

/-- **Kummer representation** of Tricomi's function (DLMF 8.5.2):
`γ*(a, z) = 𝐌(a, a + 1, −z)` for all `a` and `z`. The other form of 8.5.2,
`γ*(a, z) = e^{−z} 𝐌(1, a + 1, z)`, is `tricomiIncompleteGamma_def`.

Adapted from `tricomiIncompleteGamma_regularized_pair` of the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/IncompleteGamma/SpecialValues.lean`. -/
theorem tricomiIncompleteGamma_eq_regularizedHGFun (a z : ℂ) :
    tricomiIncompleteGamma a z = regularizedHGFun {a} {a + 1} (-z) := by
  rw [regularizedHGFun_singleton_eq_exp_mul, add_sub_cancel_left, neg_neg,
    tricomiIncompleteGamma_def]

/-- The power series of Tricomi's function in `−z` (DLMF 8.7.1): for `a ∉ −ℕ`,
`γ*(a, z) = Γ(a)⁻¹ ∑ (−z)ᵏ / (k! (a + k))`. -/
theorem hasSum_tricomiIncompleteGamma_of_ne_neg_natCast {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n)
    (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma a)⁻¹ * ((-z) ^ k / (k ! * (a + k))))
      (tricomiIncompleteGamma a z) := by
  rw [tricomiIncompleteGamma_eq_regularizedHGFun]
  refine (hasSum_regularizedHGFun (a := {a}) (b := {a + 1}) (by simp) (-z)).congr_fun fun k => ?_
  have hak : a + k ≠ 0 := fun h => ha k (by linear_combination h)
  have hΓk : Gamma (a + k) ≠ 0 :=
    Gamma_ne_zero fun n h => ha (n + k) (by push_cast; linear_combination h)
  -- `(a)ₖ / Γ(a + k + 1) = 1 / (Γ(a) (a + k))`, by `Γ(a + k + 1) = (a + k) Γ(a + k)`.
  rw [regularizedHGFunCoeff_singleton, add_right_comm, Gamma_add_one _ hak,
    inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast a k]
  field_simp

/-- The real form of the series DLMF 8.7.1 in powers of `−x`: for real `a ∉ −ℕ` and real `x`,
`∑ (−x)ᵏ / (k! (a + k)) = Γ(a) γ*(a, x)`, where `γ*(a, x)` is real
(`ofReal_tricomiIncompleteGamma_ofReal_re`). -/
theorem hasSum_Gamma_mul_re_tricomiIncompleteGamma_ofReal {a : ℝ} (ha : ∀ n : ℕ, a ≠ -n)
    (x : ℝ) : HasSum (fun k : ℕ => (-x) ^ k / (k ! * (a + k)))
      (Real.Gamma a * (tricomiIncompleteGamma a x).re) := by
  have ha' : ∀ n : ℕ, (a : ℂ) ≠ -n := fun n h => ha n (by exact_mod_cast h)
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero ha'
  have h : HasSum (fun k : ℕ => (((-x) ^ k / (k ! * (a + k)) : ℝ) : ℂ))
      (Gamma a * tricomiIncompleteGamma a x) := by
    convert (hasSum_tricomiIncompleteGamma_of_ne_neg_natCast ha' x).mul_left (Gamma a) using 1
    ext k
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]
  rw [← ofReal_tricomiIncompleteGamma_ofReal_re, Gamma_ofReal, ← ofReal_mul] at h
  exact hasSum_ofReal.mp h

/-- Tricomi's integral (DLMF 8.2.7): for `0 < Re a`,
`γ*(a, z) = Γ(a)⁻¹ ∫₀¹ t^{a−1} e^{−zt} dt`. It is Kummer's integral for `𝐌(1, a + 1, z)` after
the substitution `t ↦ 1 − t`. -/
theorem tricomiIncompleteGamma_eq_integral {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    tricomiIncompleteGamma a z =
      (Gamma a)⁻¹ * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * cexp (-(z * t)) := by
  have h1 : (1 : ℂ).re < (a + 1).re := by simpa using ha
  rw [tricomiIncompleteGamma_def, regularizedHGFun_singleton_eq_exp_mul_integral (by simp) h1]
  simp only [add_sub_cancel_right, sub_self, cpow_zero, mul_one, Gamma_one, one_mul]
  rw [Complex.exp_neg]
  field_simp

end Complex
