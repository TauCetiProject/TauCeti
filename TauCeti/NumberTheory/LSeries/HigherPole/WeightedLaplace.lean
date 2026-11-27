/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.NumberTheory.LSeries.HigherPole.DelangeWeight
public import TauCeti.NumberTheory.LSeries.HigherPole.Regularized
public import TauCeti.NumberTheory.LSeries.HigherPole.SquaredSinc
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Weighted and smoothed Laplace transforms in Delange's Tauberian theorem

Let `f` have one-sided Laplace transform `G(s)` on the half-plane `Re s > a`. Multiplying `f` by
Delange's weight `w_k(t) = t * ∫ u in 0..1, exp (-u * t) * u ^ k / k!` gives a function whose
transform is again defined on `Re s > a`, namely

`∫₀^∞ exp (-s t) w_k(t) f(t) dt = -∫ u in 0..1, G'(s + u) * u ^ k / k!`.

Indeed `G'(s + u)` is the transform of `-t f(t)` at `s + u`, and integrating `exp (-u t) u ^ k / k!`
over `u ∈ [0, 1]` reproduces `w_k(t) / t`.

Applied to a function `α` with transform `F` and to the model `(A / k!) exp (a t) t ^ k`, whose
transform is `A / (s - a) ^ (k + 1)`, this identifies Delange's regularised remainder
`TauCeti.HigherPoleTauberian.regularizedRemainder`,

`H(s) = -∫ u in 0..1, R'(s + u) * u ^ k / k!`,  `R(s) = F(s) - A / (s - a) ^ (k + 1)`,

on `Re s > a` as the Laplace transform of `w_k(t) (α(t) - (A / k!) exp (a t) t ^ k)`.

Second, the squared-sinc kernel `K_λ` of `TauCeti.HigherPoleTauberian.squaredSinc` has the
triangle function on `[-2λ, 2λ]` as its Fourier transform. Smoothing a damped function against
`K_λ(t - T)` therefore only sees its Laplace transform on a compact segment of a vertical line:

`∫₀^∞ exp (-s t) g(t) K_λ(t - T) dt = (1 / 2π) ∫ y in -2λ..2λ, G(s + i y) (1 - |y| / 2λ) e^(i y T)`.

For `g = w_k (α - (A / k!) exp (a t) t ^ k)` and `s = a + ε` with `ε > 0`, the right-hand side
involves `H` only at the points `a + ε + i y`, whose boundary behaviour as `ε → 0⁺` is controlled by
`TauCeti.HigherPoleTauberian.regularizedBoundaryL1`. This is the damped identity from which the
smoothed limit of Delange's Tauberian theorem is derived.

## Main results

* `TauCeti.HigherPoleTauberian.hasLaplace_delangeWeight_mul`: the transform of `w_k f` is
  `-∫ u in 0..1, G'(s + u) * u ^ k / k!` on `Re s > a`.
* `TauCeti.HigherPoleTauberian.hasLaplace_delangeWeight_mul_sub_exp_mul_pow`: the transform of
  `w_k(t) (α(t) - (A / k!) exp (a t) t ^ k)` is Delange's regularised remainder on `Re s > a`.
* `TauCeti.HigherPoleTauberian.integral_cexp_mul_squaredSinc_sub`: smoothing against
  `K_λ(t - T)` is an integral of the transform over the segment `s + i [-2λ, 2λ]`.
* `TauCeti.HigherPoleTauberian.integral_exp_mul_delangeWeight_mul_squaredSinc_sub`: the damped
  identity for the regularised remainder.
* `TauCeti.HigherPoleTauberian.integrableOn_cexp_mul_squaredSinc_sub`,
  `TauCeti.HigherPoleTauberian.intervalIntegrable_mul_one_sub_abs_div_mul_cexp` and their damped
  specialisations: both sides of the smoothing identities are integrable, so they can be split and
  subtracted in the boundary limit.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) 71 (1954),
  213–242, §3.3.1–3.3.3, pp. 221–224 (differentiation of the Laplace integral, integration against
  the weight, and the identity with a kernel whose Fourier transform is supported on `[-2λ, 2λ]`).
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Nat Real Topology

namespace TauCeti.HigherPoleTauberian

/-! ### Multiplication by Delange's weight -/

/-- The `u`-integral defining Delange's weight, cast to `ℂ` and multiplied by `t`, is the weight:
`t * ∫ u in 0..1, exp (-u t) * (u ^ k / k!) = w_k(t)`. -/
private theorem mul_intervalIntegral_cexp_mul_eq_delangeWeight (k : ℕ) (t : ℝ) :
    (t : ℂ) * ∫ u in (0 : ℝ)..1, cexp (-(u : ℂ) * t) * ((u ^ k / k ! : ℝ) : ℂ) =
      delangeWeight k t := by
  have h (u : ℝ) : cexp (-(u : ℂ) * t) * ((u ^ k / k ! : ℝ) : ℂ) =
      ((Real.exp (-u * t) * u ^ k / k ! : ℝ) : ℂ) := by
    push_cast
    ring
  simp_rw [h, intervalIntegral.integral_ofReal, delangeWeight_def, ofReal_mul]

/-- **Weighting by Delange's weight on the Laplace side.** If `G` is the one-sided Laplace
transform of `f` on the half-plane `Re s > a`, then so is
`s ↦ -∫ u in 0..1, G'(s + u) * u ^ k / k!` the transform of `t ↦ w_k(t) * f t`, where `w_k` is
`TauCeti.HigherPoleTauberian.delangeWeight k`. -/
theorem hasLaplace_delangeWeight_mul {f : ℝ → ℂ} {G : ℂ → ℂ} {a : ℝ}
    (hG : ∀ s : ℂ, a < s.re → HasLaplace f s (G s)) (k : ℕ) {s : ℂ} (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ (delangeWeight k t : ℂ) * f t) s
      (-∫ u in (0 : ℝ)..1, deriv G (s + u) * ((u ^ k / k ! : ℝ) : ℂ)) := by
  -- `h t = exp (-s t) * (-t * f t)` is the integrand of the transform of `-t f` at `s`, and
  -- `Φ u t = exp (-u t) * (u ^ k / k!) * h t` is the integrand of the double integral over
  -- `(u, t) ∈ (0, 1] × (0, ∞)`.
  set h : ℝ → ℂ := fun t ↦ cexp (-s * t) * (-(t : ℂ) * f t) with h_def
  have hh : Integrable h (volume.restrict (Ioi 0)) :=
    (hasLaplace_neg_smul_deriv_of_re_gt hG hs).integrable
  set Φ : ℝ → ℝ → ℂ := fun u t ↦ cexp (-(u : ℂ) * t) * ((u ^ k / k ! : ℝ) : ℂ) * h t with Φ_def
  have hΦ : Integrable (Function.uncurry Φ)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi 0))) := by
    refine integrable_uncurry_mul_of_norm_le (C := 1) measurableSet_uIoc measurableSet_Ioi
      measure_Ioc_lt_top.ne (Continuous.aestronglyMeasurable (by fun_prop)) (fun u hu t ht ↦ ?_) hh
    rw [uIoc_of_le zero_le_one] at hu
    have hw : 0 ≤ u ^ k / k ! := div_nonneg (pow_nonneg hu.1.le k) k.factorial.cast_nonneg
    rw [← ofReal_neg, ← ofReal_mul, ← ofReal_exp, ← ofReal_mul, norm_real,
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hw), neg_mul]
    exact exp_neg_mul_mul_pow_div_factorial_le_one hu.1.le hu.2 (mem_Ioi.mp ht).le k
  -- For each `t`, the `u`-integral of `Φ` is `-exp (-s t) * (w_k(t) * f t)`.
  have hinner (t : ℝ) : ∫ u in (0 : ℝ)..1, Φ u t =
      -(cexp (-s * t) * ((delangeWeight k t : ℂ) * f t)) := by
    simp_rw [Φ_def, intervalIntegral.integral_mul_const,
      ← mul_intervalIntegral_cexp_mul_eq_delangeWeight k t, h_def]
    ring
  -- For each `u ∈ (0, 1]`, the `t`-integral of `Φ` is `G'(s + u) * (u ^ k / k!)`.
  have houter : ∫ u in (0 : ℝ)..1, ∫ t in Ioi 0, Φ u t =
      ∫ u in (0 : ℝ)..1, deriv G (s + u) * ((u ^ k / k ! : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_ae (.of_forall fun u hu ↦ ?_)
    rw [uIoc_of_le zero_le_one] at hu
    have hsu : a < (s + u).re := by
      rw [add_re, ofReal_re]
      linarith [hu.1]
    have hD := (hasLaplace_neg_smul_deriv_of_re_gt hG hsu).integral_eq
    simp only [smul_eq_mul] at hD
    have hΦ_shift (t : ℝ) : Φ u t = cexp (-(s + u) * t) * (-(t : ℂ) * f t) *
        ((u ^ k / k ! : ℝ) : ℂ) := by
      rw [Φ_def, h_def, neg_add, add_mul, Complex.exp_add]
      ring
    simp_rw [hΦ_shift, integral_mul_const, hD]
  refine HasLaplace.intro ?_ ?_
  · refine (hΦ.integral_prod_right.neg).congr (.of_forall fun t ↦ ?_)
    simp only [Function.uncurry_apply_pair, uIoc_of_le zero_le_one,
      ← intervalIntegral.integral_of_le zero_le_one, hinner, Pi.neg_apply, neg_neg, smul_eq_mul]
  · simp only [smul_eq_mul]
    rw [← houter, intervalIntegral_integral_swap hΦ, ← integral_neg]
    exact integral_congr_ae (.of_forall fun t ↦ by simp only [hinner, neg_neg])

/-- **Delange's regularised remainder as a Laplace transform.** Let `α` have transform `F` on the
half-plane `Re s > a`, and write `R(s) = F(s) - A / (s - a) ^ (k + 1)`. Then on `Re s > a`, the
regularised remainder `-∫ u in 0..1, R'(s + u) * u ^ k / k!` is the Laplace transform of
`t ↦ w_k(t) * (α(t) - (A / k!) * exp (a t) * t ^ k)`, where `w_k` is
`TauCeti.HigherPoleTauberian.delangeWeight k`; this remainder is
`TauCeti.HigherPoleTauberian.regularizedRemainder F a k A`. No positivity, monotonicity or boundary
hypothesis is needed. -/
theorem hasLaplace_delangeWeight_mul_sub_exp_mul_pow {α : ℝ → ℝ} {F : ℂ → ℂ} {a A : ℝ} (k : ℕ)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun t ↦ (α t : ℂ)) s (F s)) {s : ℂ} (hs : a < s.re) :
    HasLaplace
      (fun t : ℝ ↦ ((delangeWeight k t * (α t - A / k ! * (Real.exp (a * t) * t ^ k)) : ℝ) : ℂ))
      s (regularizedRemainder F a k A s) := by
  have hR (w : ℂ) (hw : a < w.re) : HasLaplace
      (fun t : ℝ ↦ ((α t - A / k ! * (Real.exp (a * t) * t ^ k) : ℝ) : ℂ)) w
      (F w - (A : ℂ) / (w - a) ^ (k + 1)) := by
    have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hmodel := (hasLaplace_exp_mul_pow k hw).const_smul ((A : ℂ) / k !)
    rw [smul_eq_mul, mul_div_assoc', div_mul_cancel₀ _ hk] at hmodel
    refine ((hF w hw).sub hmodel).congr_ae (.of_forall fun t ↦ ?_)
    push_cast
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [regularizedRemainder_apply]
  simpa only [ofReal_mul] using hasLaplace_delangeWeight_mul hR k hs

/-! ### Smoothing against the squared-sinc kernel -/

/-- **Integrability of the smoothed Laplace integrand.** If `g` has a one-sided Laplace transform
at `s`, then `t ↦ exp (-s t) g(t) K_λ(t - T)` is integrable on `(0, ∞)` for every bandwidth `λ` and
every real `T`, where `K_λ` is `TauCeti.HigherPoleTauberian.squaredSinc λ`. -/
theorem integrableOn_cexp_mul_squaredSinc_sub {g : ℝ → ℂ} {s z : ℂ} (hg : HasLaplace g s z)
    (ell T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ cexp (-s * t) * g t * (squaredSinc ell (t - T) : ℂ)) (Ioi 0) := by
  refine (hg.integrable.mul_bdd (g := fun t ↦ (squaredSinc ell (t - T) : ℂ)) (c := |ell| / π)
    (Continuous.aestronglyMeasurable (by fun_prop [continuous_squaredSinc]))
    (.of_forall fun t ↦ ?_)).congr
    (.of_forall fun t ↦ by simp only [smul_eq_mul])
  rw [norm_real, Real.norm_eq_abs, squaredSinc_def, abs_mul, abs_div, abs_of_pos Real.pi_pos,
    abs_pow]
  exact mul_le_of_le_one_right (div_nonneg (abs_nonneg _) Real.pi_pos.le)
    (pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _))

/-- The Fubini step behind `integral_cexp_mul_squaredSinc_sub`: the integrand
`(y, t) ↦ (1 - |y| / 2λ) e^(i y (T - t)) exp (-s t) g(t)` is integrable on
`(-2λ, 2λ] × (0, ∞)`, and its `t`-integral at each `y ∈ (-2λ, 2λ]` is
`G(s + i y) (1 - |y| / 2λ) e^(i y T)`. -/
private theorem integrable_uncurry_and_setIntegral_eq {g : ℝ → ℂ} {G : ℂ → ℂ} {s : ℂ} {ell : ℝ}
    (hell : 0 ≤ ell)
    (hG : ∀ y ∈ Icc (-(2 * ell)) (2 * ell), HasLaplace g (s + y * I) (G (s + y * I))) (T : ℝ) :
    Integrable (Function.uncurry fun (y t : ℝ) ↦
        ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * ((T - t : ℝ) : ℂ)) * (cexp (-s * t) * g t))
        ((volume.restrict (uIoc (-(2 * ell)) (2 * ell))).prod (volume.restrict (Ioi 0))) ∧
      ∀ y ∈ uIoc (-(2 * ell)) (2 * ell),
        ∫ t in Ioi (0 : ℝ), ((1 - |y| / (2 * ell) : ℝ) : ℂ) *
            cexp (I * y * ((T - t : ℝ) : ℂ)) * (cexp (-s * t) * g t) =
          G (s + y * I) * ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T) := by
  have hq : Integrable (fun t : ℝ ↦ cexp (-s * t) * g t) (volume.restrict (Ioi 0)) := by
    have h0 := (hG 0 ⟨by linarith, by linarith⟩).integrable
    simpa only [ofReal_zero, zero_mul, add_zero, smul_eq_mul] using h0
  refine ⟨?_, fun y hy ↦ ?_⟩
  · refine integrable_uncurry_mul_of_norm_le (C := 1) measurableSet_uIoc measurableSet_Ioi
      measure_Ioc_lt_top.ne (Continuous.aestronglyMeasurable (by fun_prop)) (fun y hy t _ ↦ ?_) hq
    have hphase : I * y * ((T - t : ℝ) : ℂ) = ((y * (T - t) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [uIoc_of_le (by linarith)] at hy
    rw [norm_mul, hphase, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs]
    exact abs_one_sub_abs_div_le_one (abs_le.mpr ⟨hy.1.le, hy.2⟩)
  · rw [uIoc_of_le (by linarith)] at hy
    have hD := (hG y ⟨hy.1.le, hy.2⟩).integral_eq
    simp only [smul_eq_mul] at hD
    have hshift (t : ℝ) : ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * ((T - t : ℝ) : ℂ)) *
        (cexp (-s * t) * g t) = cexp (-(s + y * I) * t) * g t *
          (((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T)) := by
      have hexp : cexp (I * y * ((T - t : ℝ) : ℂ)) * cexp (-s * t) =
          cexp (-(s + y * I) * t) * cexp (I * y * T) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      linear_combination (((1 - |y| / (2 * ell) : ℝ) : ℂ) * g t) * hexp
    simp_rw [hshift, integral_mul_const, hD]
    ring

/-- **Smoothing a Laplace integrand against the squared-sinc kernel.** Let `λ ≥ 0` and let `G` be
the one-sided Laplace transform of `g` at every point `s + i y` with `y ∈ [-2λ, 2λ]`. Then for
every real `T`,

`∫₀^∞ exp (-s t) g(t) K_λ(t - T) dt = (1 / 2π) ∫ y in -2λ..2λ, G(s + i y) (1 - |y| / 2λ) e^(i y T)`,

where `K_λ` is `TauCeti.HigherPoleTauberian.squaredSinc λ`. Both integrands are integrable:
see `TauCeti.HigherPoleTauberian.integrableOn_cexp_mul_squaredSinc_sub` and
`TauCeti.HigherPoleTauberian.intervalIntegrable_mul_one_sub_abs_div_mul_cexp`. -/
theorem integral_cexp_mul_squaredSinc_sub {g : ℝ → ℂ} {G : ℂ → ℂ} {s : ℂ} {ell : ℝ}
    (hell : 0 ≤ ell)
    (hG : ∀ y ∈ Icc (-(2 * ell)) (2 * ell), HasLaplace g (s + y * I) (G (s + y * I))) (T : ℝ) :
    ∫ t in Ioi (0 : ℝ), cexp (-s * t) * g t * (squaredSinc ell (t - T) : ℂ) =
      1 / (2 * π) * ∫ y in (-(2 * ell))..(2 * ell),
        G (s + y * I) * ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T) := by
  obtain ⟨hΨ, hD⟩ := integrable_uncurry_and_setIntegral_eq hell hG T
  -- The `y`-integral of `(1 - |y| / 2λ) e^(i y (T - t)) exp (-s t) g(t)` is
  -- `2π K_λ(t - T) exp (-s t) g(t)`.
  have hinner (t : ℝ) : cexp (-s * t) * g t * (squaredSinc ell (t - T) : ℂ) =
      1 / (2 * π) * ∫ y in (-(2 * ell))..(2 * ell), ((1 - |y| / (2 * ell) : ℝ) : ℂ) *
        cexp (I * y * ((T - t : ℝ) : ℂ)) * (cexp (-s * t) * g t) := by
    simp only [intervalIntegral.integral_mul_const]
    rw [← squaredSinc_neg_right, neg_sub, squaredSinc_fourier hell]
    ring
  simp_rw [hinner]
  rw [integral_const_mul, ← intervalIntegral_integral_swap hΨ,
    intervalIntegral.integral_congr_ae (.of_forall fun y hy ↦ hD y hy)]

/-- **Integrability of the frequency-side integrand.** Under the hypotheses of
`TauCeti.HigherPoleTauberian.integral_cexp_mul_squaredSinc_sub`, the function
`y ↦ G(s + i y) (1 - |y| / 2λ) e^(i y T)` is interval integrable on `[-2λ, 2λ]`. -/
theorem intervalIntegrable_mul_one_sub_abs_div_mul_cexp {g : ℝ → ℂ} {G : ℂ → ℂ} {s : ℂ}
    {ell : ℝ} (hell : 0 ≤ ell)
    (hG : ∀ y ∈ Icc (-(2 * ell)) (2 * ell), HasLaplace g (s + y * I) (G (s + y * I))) (T : ℝ) :
    IntervalIntegrable (fun y : ℝ ↦ G (s + y * I) * ((1 - |y| / (2 * ell) : ℝ) : ℂ) *
      cexp (I * y * T)) volume (-(2 * ell)) (2 * ell) := by
  obtain ⟨hΨ, hD⟩ := integrable_uncurry_and_setIntegral_eq hell hG T
  rw [intervalIntegrable_iff]
  exact hΨ.integral_prod_left.congr ((ae_restrict_iff' measurableSet_uIoc).mpr (.of_forall hD))

/-- **The damped identity for Delange's regularised remainder.** Let `α` have transform `F` on the
half-plane `Re s > a`, let `ε > 0` and `λ ≥ 0`, and write `H` for
`TauCeti.HigherPoleTauberian.regularizedRemainder F a k A`, that is,
`H(s) = -∫ u in 0..1, R'(s + u) * u ^ k / k!` with `R(s) = F(s) - A / (s - a) ^ (k + 1)`. Then for
every real `T`,

`∫₀^∞ e^(-(a + ε) t) w_k(t) (α(t) - (A / k!) e^(a t) t ^ k) K_λ(t - T) dt`
`  = (1 / 2π) ∫ y in -2λ..2λ, H(a + ε + i y) (1 - |y| / 2λ) e^(i y T)`,

where `w_k` is `TauCeti.HigherPoleTauberian.delangeWeight k` and `K_λ` is
`TauCeti.HigherPoleTauberian.squaredSinc λ`. Both integrands are integrable: see
`TauCeti.HigherPoleTauberian.integrableOn_exp_mul_delangeWeight_mul_squaredSinc_sub` and
`TauCeti.HigherPoleTauberian.intervalIntegrable_regularizedRemainder_mul_one_sub_abs_div_mul_cexp`.
-/
theorem integral_exp_mul_delangeWeight_mul_squaredSinc_sub {α : ℝ → ℝ} {F : ℂ → ℂ}
    {a A ε ell : ℝ} (k : ℕ)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun t ↦ (α t : ℂ)) s (F s)) (hε : 0 < ε)
    (hell : 0 ≤ ell) (T : ℝ) :
    ((∫ t in Ioi 0, Real.exp (-(a + ε) * t) *
        (delangeWeight k t * (α t - A / k ! * (Real.exp (a * t) * t ^ k))) *
          squaredSinc ell (t - T) : ℝ) : ℂ) =
      1 / (2 * π) * ∫ y in (-(2 * ell))..(2 * ell),
        regularizedRemainder F a k A ((a : ℂ) + ε + y * I) *
          ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T) := by
  have h := integral_cexp_mul_squaredSinc_sub (s := (a : ℂ) + ε)
    (G := regularizedRemainder F a k A) hell
    (fun y _ ↦ hasLaplace_delangeWeight_mul_sub_exp_mul_pow (A := A) k hF
      (s := (a : ℂ) + ε + y * I) (by simp [hε])) T
  rw [← h, ← integral_complex_ofReal]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  push_cast
  ring

/-- **Integrability of the damped smoothed integrand.** Let `α` have transform `F` on the half-plane
`Re s > a` and let `ε > 0`. Then for every bandwidth `λ` and every real `T`, the time-side integrand
`t ↦ e^(-(a + ε) t) w_k(t) (α(t) - (A / k!) e^(a t) t ^ k) K_λ(t - T)` of
`TauCeti.HigherPoleTauberian.integral_exp_mul_delangeWeight_mul_squaredSinc_sub` is integrable on
`(0, ∞)`, where `w_k` is `TauCeti.HigherPoleTauberian.delangeWeight k` and `K_λ` is
`TauCeti.HigherPoleTauberian.squaredSinc λ`. -/
theorem integrableOn_exp_mul_delangeWeight_mul_squaredSinc_sub {α : ℝ → ℝ} {F : ℂ → ℂ}
    {a A ε : ℝ} (k : ℕ) (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun t ↦ (α t : ℂ)) s (F s))
    (hε : 0 < ε) (ell T : ℝ) :
    IntegrableOn (fun t ↦ Real.exp (-(a + ε) * t) *
        (delangeWeight k t * (α t - A / k ! * (Real.exp (a * t) * t ^ k))) *
          squaredSinc ell (t - T)) (Ioi 0) := by
  have h := integrableOn_cexp_mul_squaredSinc_sub
    (hasLaplace_delangeWeight_mul_sub_exp_mul_pow (A := A) k hF (s := (a : ℂ) + ε)
      (by simp [hε])) ell T
  rw [IntegrableOn, Integrable.iff_ofReal (𝕜 := ℂ), RCLike.ofReal_eq_complex_ofReal]
  refine h.congr (.of_forall fun t ↦ ?_)
  push_cast
  ring

/-- **Integrability of the damped frequency-side integrand.** Under the hypotheses of
`TauCeti.HigherPoleTauberian.integral_exp_mul_delangeWeight_mul_squaredSinc_sub`, the function
`y ↦ H(a + ε + i y) (1 - |y| / 2λ) e^(i y T)` is interval integrable on `[-2λ, 2λ]`, where `H` is
`TauCeti.HigherPoleTauberian.regularizedRemainder F a k A`. -/
theorem intervalIntegrable_regularizedRemainder_mul_one_sub_abs_div_mul_cexp {α : ℝ → ℝ}
    {F : ℂ → ℂ} {a A ε ell : ℝ} (k : ℕ)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun t ↦ (α t : ℂ)) s (F s)) (hε : 0 < ε)
    (hell : 0 ≤ ell) (T : ℝ) :
    IntervalIntegrable (fun y : ℝ ↦ regularizedRemainder F a k A ((a : ℂ) + ε + y * I) *
      ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T)) volume (-(2 * ell)) (2 * ell) :=
  intervalIntegrable_mul_one_sub_abs_div_mul_cexp (s := (a : ℂ) + ε)
    (G := regularizedRemainder F a k A) hell
    (fun y _ ↦ hasLaplace_delangeWeight_mul_sub_exp_mul_pow (A := A) k hF
      (s := (a : ℂ) + ε + y * I) (by simp [hε])) T

end TauCeti.HigherPoleTauberian
