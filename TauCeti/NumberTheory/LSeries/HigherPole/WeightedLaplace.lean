/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.NumberTheory.LSeries.HigherPole.DelangeWeight
public import TauCeti.NumberTheory.LSeries.HigherPole.SquaredSinc
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.LaplaceTransform.Elementary

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

/-- Fubini domination used twice below: if `P` is continuous and bounded by `1` on
`uIoc b c × (0, ∞)` and `h` is integrable on `(0, ∞)`, then `(u, t) ↦ P u t * h t` is integrable
on the product. -/
private theorem integrable_uncurry_mul_of_norm_le_one {P : ℝ → ℝ → ℂ} {h : ℝ → ℂ} {b c : ℝ}
    (hP : Continuous (Function.uncurry P))
    (hP_le : ∀ u ∈ uIoc b c, ∀ t ∈ Ioi (0 : ℝ), ‖P u t‖ ≤ 1)
    (hh : Integrable h (volume.restrict (Ioi 0))) :
    Integrable (Function.uncurry fun u t ↦ P u t * h t)
      ((volume.restrict (uIoc b c)).prod (volume.restrict (Ioi 0))) := by
  have : IsFiniteMeasure (volume.restrict (uIoc b c)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  refine Integrable.mono' (hh.norm.comp_snd _)
    (hP.aestronglyMeasurable.mul hh.aestronglyMeasurable.comp_snd) ?_
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_Ioi)]
  refine .of_forall fun ⟨u, t⟩ hp ↦ ?_
  obtain ⟨hu, ht⟩ := mem_prod.mp hp
  simp only [Function.uncurry_apply_pair, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hP_le u hu t ht)

/-! ### Multiplication by Delange's weight -/

/-- On the open half-plane `Re s > a` where `G` is the transform of `f`, the derivative of `G` is
the transform of `t ↦ -t * f t`. -/
private theorem hasLaplace_neg_mul_deriv {f : ℝ → ℂ} {G : ℂ → ℂ} {a : ℝ}
    (hG : ∀ s : ℂ, a < s.re → HasLaplace f s (G s)) {s : ℂ} (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ -(t : ℂ) * f t) s (deriv G s) := by
  have hev : ∀ᶠ w in 𝓝 s, HasLaplace f w (G w) :=
    ((isOpen_lt continuous_const continuous_re).eventually_mem hs).mono fun w hw ↦ hG w hw
  simpa only [pow_one, iteratedDeriv_one, smul_eq_mul] using
    hasLaplace_neg_pow_smul_iteratedDeriv hev 1

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

/-- For `u ∈ (0, 1]` and `t > 0`, the factor `exp (-u t) * (u ^ k / k!)` has norm at most `1`. -/
private theorem norm_cexp_mul_pow_div_factorial_le_one (k : ℕ) {u t : ℝ}
    (hu : u ∈ uIoc (0 : ℝ) 1) (ht : t ∈ Ioi (0 : ℝ)) :
    ‖cexp (-(u : ℂ) * t) * ((u ^ k / k ! : ℝ) : ℂ)‖ ≤ 1 := by
  rw [uIoc_of_le zero_le_one] at hu
  have hw0 : 0 ≤ u ^ k / k ! := div_nonneg (pow_nonneg hu.1.le k) k.factorial.cast_nonneg
  have hw1 : u ^ k / k ! ≤ 1 :=
    div_le_one_of_le₀ ((pow_le_one₀ hu.1.le hu.2).trans (by exact_mod_cast k.factorial_pos))
      k.factorial.cast_nonneg
  have hexp : Real.exp (-u * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1, mem_Ioi.mp ht])
  rw [norm_mul, ← ofReal_neg, ← ofReal_mul, norm_exp_ofReal, norm_real, Real.norm_of_nonneg hw0]
  calc Real.exp (-u * t) * (u ^ k / k !) ≤ 1 * 1 :=
        mul_le_mul hexp hw1 hw0 zero_le_one
    _ = 1 := one_mul 1

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
  have hh : Integrable h (volume.restrict (Ioi 0)) := (hasLaplace_neg_mul_deriv hG hs).integrable
  set Φ : ℝ → ℝ → ℂ := fun u t ↦ cexp (-(u : ℂ) * t) * ((u ^ k / k ! : ℝ) : ℂ) * h t with Φ_def
  have hΦ : Integrable (Function.uncurry Φ)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi 0))) :=
    integrable_uncurry_mul_of_norm_le_one (by fun_prop)
      (fun _ hu _ ht ↦ norm_cexp_mul_pow_div_factorial_le_one k hu ht) hh
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
    have hD := (hasLaplace_neg_mul_deriv hG hsu).integral_eq
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
`TauCeti.HigherPoleTauberian.delangeWeight k`. No positivity, monotonicity or boundary hypothesis
is needed. -/
theorem hasLaplace_delangeWeight_mul_sub_exp_mul_pow {α : ℝ → ℝ} {F : ℂ → ℂ} {a A : ℝ} (k : ℕ)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun t ↦ (α t : ℂ)) s (F s)) {s : ℂ} (hs : a < s.re) :
    HasLaplace
      (fun t : ℝ ↦ ((delangeWeight k t * (α t - A / k ! * (Real.exp (a * t) * t ^ k)) : ℝ) : ℂ))
      s (-∫ u in (0 : ℝ)..1, deriv (fun w : ℂ ↦ F w - (A : ℂ) / (w - a) ^ (k + 1)) (s + u) *
        ((u ^ k / k ! : ℝ) : ℂ)) := by
  have hR (w : ℂ) (hw : a < w.re) : HasLaplace
      (fun t : ℝ ↦ ((α t - A / k ! * (Real.exp (a * t) * t ^ k) : ℝ) : ℂ)) w
      (F w - (A : ℂ) / (w - a) ^ (k + 1)) := by
    have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hmodel := (hasLaplace_exp_mul_pow k hw).const_smul ((A : ℂ) / k !)
    rw [smul_eq_mul, mul_div_assoc', div_mul_cancel₀ _ hk] at hmodel
    refine ((hF w hw).sub hmodel).congr_ae (.of_forall fun t ↦ ?_)
    push_cast
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [ofReal_mul] using hasLaplace_delangeWeight_mul hR k hs

/-! ### Smoothing against the squared-sinc kernel -/

/-- On `[-2λ, 2λ]` with `λ ≥ 0`, the triangle function `1 - |y| / (2λ)` lies in `[0, 1]`. -/
private theorem norm_triangle_le_one {ell y : ℝ} (hell : 0 ≤ ell)
    (hy : y ∈ uIoc (-(2 * ell)) (2 * ell)) :
    ‖((1 - |y| / (2 * ell) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [uIoc_of_le (by linarith)] at hy
  have hy' : |y| ≤ 2 * ell := abs_le.mpr ⟨hy.1.le, hy.2⟩
  have hdiv : |y| / (2 * ell) ≤ 1 := div_le_one_of_le₀ hy' (by positivity)
  rw [norm_real, Real.norm_of_nonneg (by linarith)]
  linarith [div_nonneg (abs_nonneg y) (by positivity : (0 : ℝ) ≤ 2 * ell)]

/-- **Smoothing a Laplace integrand against the squared-sinc kernel.** Let `λ ≥ 0` and let `G` be
the one-sided Laplace transform of `g` at every point `s + i y` with `y ∈ [-2λ, 2λ]`. Then for
every real `T`,

`∫₀^∞ exp (-s t) g(t) K_λ(t - T) dt = (1 / 2π) ∫ y in -2λ..2λ, G(s + i y) (1 - |y| / 2λ) e^(i y T)`,

where `K_λ` is `TauCeti.HigherPoleTauberian.squaredSinc λ`. -/
theorem integral_cexp_mul_squaredSinc_sub {g : ℝ → ℂ} {G : ℂ → ℂ} {s : ℂ} {ell : ℝ}
    (hell : 0 ≤ ell)
    (hG : ∀ y ∈ Icc (-(2 * ell)) (2 * ell), HasLaplace g (s + y * I) (G (s + y * I))) (T : ℝ) :
    ∫ t in Ioi (0 : ℝ), cexp (-s * t) * g t * (squaredSinc ell (t - T) : ℂ) =
      1 / (2 * π) * ∫ y in (-(2 * ell))..(2 * ell),
        G (s + y * I) * ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T) := by
  set q : ℝ → ℂ := fun t ↦ cexp (-s * t) * g t with q_def
  have hq : Integrable q (volume.restrict (Ioi 0)) := by
    have h0 := (hG 0 ⟨by linarith, by linarith⟩).integrable
    simpa only [ofReal_zero, zero_mul, add_zero, smul_eq_mul] using h0
  -- `Ψ y t = (1 - |y| / 2λ) * e^(i y (T - t)) * q t`; its `y`-integral is `2π K_λ(t - T) q t`.
  set Ψ : ℝ → ℝ → ℂ := fun y t ↦
    ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * ((T - t : ℝ) : ℂ)) * q t with Ψ_def
  have hΨ : Integrable (Function.uncurry Ψ)
      ((volume.restrict (uIoc (-(2 * ell)) (2 * ell))).prod (volume.restrict (Ioi 0))) := by
    refine integrable_uncurry_mul_of_norm_le_one (by fun_prop) (fun y hy t _ ↦ ?_) hq
    have hphase : I * y * ((T - t : ℝ) : ℂ) = ((y * (T - t) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [norm_mul, hphase, norm_exp_ofReal_mul_I, mul_one]
    exact norm_triangle_le_one hell hy
  have hinner (t : ℝ) : cexp (-s * t) * g t * (squaredSinc ell (t - T) : ℂ) =
      1 / (2 * π) * ∫ y in (-(2 * ell))..(2 * ell), Ψ y t := by
    simp only [Ψ_def, q_def, intervalIntegral.integral_mul_const]
    rw [← squaredSinc_neg_right, neg_sub, squaredSinc_fourier hell]
    ring
  have houter : ∫ y in (-(2 * ell))..(2 * ell), ∫ t in Ioi 0, Ψ y t =
      ∫ y in (-(2 * ell))..(2 * ell),
        G (s + y * I) * ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T) := by
    refine intervalIntegral.integral_congr_ae (.of_forall fun y hy ↦ ?_)
    rw [uIoc_of_le (by linarith)] at hy
    have hD := (hG y ⟨hy.1.le, hy.2⟩).integral_eq
    simp only [smul_eq_mul] at hD
    have hΨ_shift (t : ℝ) : Ψ y t = cexp (-(s + y * I) * t) * g t *
        (((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T)) := by
      have hexp : cexp (I * y * ((T - t : ℝ) : ℂ)) * cexp (-s * t) =
          cexp (-(s + y * I) * t) * cexp (I * y * T) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [Ψ_def, q_def]
      linear_combination (((1 - |y| / (2 * ell) : ℝ) : ℂ) * g t) * hexp
    simp_rw [hΨ_shift, integral_mul_const, hD]
    ring
  simp_rw [hinner]
  rw [integral_const_mul, ← intervalIntegral_integral_swap hΨ, houter]

/-- **The damped identity for Delange's regularised remainder.** Let `α` have transform `F` on the
half-plane `Re s > a`, let `ε > 0` and `λ ≥ 0`, and write
`H(s) = -∫ u in 0..1, R'(s + u) * u ^ k / k!` with `R(s) = F(s) - A / (s - a) ^ (k + 1)`. Then for
every real `T`,

`∫₀^∞ e^(-(a + ε) t) w_k(t) (α(t) - (A / k!) e^(a t) t ^ k) K_λ(t - T) dt`
`  = (1 / 2π) ∫ y in -2λ..2λ, H(a + ε + i y) (1 - |y| / 2λ) e^(i y T)`,

where `w_k` is `TauCeti.HigherPoleTauberian.delangeWeight k` and `K_λ` is
`TauCeti.HigherPoleTauberian.squaredSinc λ`. -/
theorem integral_exp_mul_delangeWeight_mul_squaredSinc_sub {α : ℝ → ℝ} {F : ℂ → ℂ}
    {a A ε ell : ℝ} (k : ℕ)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun t ↦ (α t : ℂ)) s (F s)) (hε : 0 < ε)
    (hell : 0 ≤ ell) (T : ℝ) :
    ((∫ t in Ioi 0, Real.exp (-(a + ε) * t) *
        (delangeWeight k t * (α t - A / k ! * (Real.exp (a * t) * t ^ k))) *
          squaredSinc ell (t - T) : ℝ) : ℂ) =
      1 / (2 * π) * ∫ y in (-(2 * ell))..(2 * ell),
        (-∫ u in (0 : ℝ)..1,
          deriv (fun w : ℂ ↦ F w - (A : ℂ) / (w - a) ^ (k + 1)) ((a + ε : ℂ) + y * I + u) *
            ((u ^ k / k ! : ℝ) : ℂ)) *
          ((1 - |y| / (2 * ell) : ℝ) : ℂ) * cexp (I * y * T) := by
  have h := integral_cexp_mul_squaredSinc_sub (s := (a + ε : ℂ))
    (G := fun w ↦ -∫ u in (0 : ℝ)..1,
      deriv (fun w : ℂ ↦ F w - (A : ℂ) / (w - a) ^ (k + 1)) (w + u) * ((u ^ k / k ! : ℝ) : ℂ)) hell
    (fun y _ ↦ hasLaplace_delangeWeight_mul_sub_exp_mul_pow (A := A) k hF
      (s := (a + ε : ℂ) + y * I) (by simp [hε])) T
  rw [← h, ← integral_complex_ofReal]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  push_cast
  ring

end TauCeti.HigherPoleTauberian
