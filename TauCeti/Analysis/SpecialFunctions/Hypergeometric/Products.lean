/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Bilinear product identities for Gauss hypergeometric series

Two classical bilinear combinations of Gauss hypergeometric functions collapse to constant multiples
of reciprocal Gamma products — Wronskian-type identities for contiguous solutions of the
hypergeometric differential equation. Because `Complex.regularizedGaussHGFun` divides by `Γ(c)`,
each identity holds in regularized form for all complex parameters without pole exclusions, and
dividing by the Gamma prefactors recovers the normalized identity for `ordinaryHypergeometric`
away from the poles.

The first identity (DLMF 15.16.4) pairs opposite parameters `(a, b, c)` and `(-a, -b, -c)` at the
same argument `z` in the open unit disk:
`𝐅(a, b; c; z) 𝐅(-a, -b; -c; z)`
`- a b (a - c)(b - c) z² 𝐅(1 + a, 1 + b; 2 + c; z) 𝐅(1 - a, 1 - b; 2 - c; z)`
`= (Γ(c) Γ(-c))⁻¹ = -c sin(π c) / π`,
giving the normalized identity equal to `1` whenever `c` is not an integer.

The second identity is Elliott's generalized Legendre relation (DLMF 15.16.5; note that DLMF prints
`Γ(1/2 + ν)` in the denominator where the true factor is `Γ(1/2 + μ)`), which pairs series at
complementary arguments `z` and `1 - z` on the open lens `{z | ‖z‖ < 1 ∧ ‖1 - z‖ < 1}`:
`𝐅(1/2 + λ, -1/2 - ν; 1 + λ + μ; z) 𝐅(1/2 - λ, 1/2 + ν; 1 + ν + μ; 1 - z)`
`+ 𝐅(1/2 + λ, 1/2 - ν; 1 + λ + μ; z) 𝐅(-1/2 - λ, 1/2 + ν; 1 + ν + μ; 1 - z)`
`- 𝐅(1/2 + λ, 1/2 - ν; 1 + λ + μ; z) 𝐅(1/2 - λ, 1/2 + ν; 1 + ν + μ; 1 - z)`
`= (Γ(λ + μ + ν + 3/2) Γ(1/2 + μ))⁻¹`.
At `λ = μ = ν = 0` this specializes to Legendre's classical relation `2 / π` for the complete
elliptic hypergeometric series at `z` and `1 - z`.

## Main results

* `Complex.regularizedGaussHGFun_mul_neg_sub_eq_inv_Gamma_mul`,
  `Complex.regularizedGaussHGFun_mul_neg_sub_eq_neg_mul_sin_div_pi` — regularized forms of
  DLMF 15.16.4 on `‖z‖ < 1`, valid without pole exclusions on `a, b, c`.
* `Complex.ordinaryHypergeometric_mul_neg_add_eq_one` — DLMF 15.16.4 for `ordinaryHypergeometric`
  on `‖z‖ < 1` when `c` is not an integer.
* `Complex.regularizedGaussHGFun_legendreRelation` — regularized form of Elliott's generalized
  Legendre relation (DLMF 15.16.5) on `‖z‖ < 1` and `‖1 - z‖ < 1`, valid for all `lam, mu, nu : ℂ`.
* `Complex.ordinaryHypergeometric_legendreRelation` — Elliott's generalized Legendre relation for
  `ordinaryHypergeometric` when `1 + lam + mu` and `1 + nu + mu` avoid nonpositive integers.
* `Complex.ordinaryHypergeometric_legendreRelation_zero` — the `lam = mu = nu = 0` elliptic
  specialization with right-hand side `2 / π`.

## References

* E. B. Elliott, *A formula including Legendre's $EK' + KE' - KK' = \frac{1}{2}\pi$*, Messenger of
  Mathematics **33** (1904), 31–32.
* A. Erdélyi, W. Magnus, F. Oberhettinger, and F. G. Tricomi, *Higher Transcendental Functions*,
  Vol. I, McGraw–Hill, 1953, §2.1.4 and §2.4.
* NIST *Digital Library of Mathematical Functions*, §15.16, equations 15.16.4 and 15.16.5,
  <https://dlmf.nist.gov/15.16>.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Nat Real Topology

namespace Complex

/-! ### Bilinear product at opposite parameters (DLMF 15.16.4) -/

private theorem mul_regularizedGaussHGFun_eq (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    a * regularizedGaussHGFun a b c z =
      a * (c * (1 - z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z +
        (a - c) * (b - c) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z) := by
  have h₂ := regularizedGaussHGFun_eq_sub_mul_add_mul b a c hz
  rw [regularizedGaussHGFun_symm b a, regularizedGaussHGFun_symm b a,
    regularizedGaussHGFun_symm (b + 1) a] at h₂
  have h₅ := regularizedGaussHGFun_eq_sub_mul_mul a b c hz
  have h₇ := regularizedGaussHGFun_eq_sub_mul_mul a b (c + 1) hz
  have hc2 : c + 1 + 1 = c + 2 := by ring
  rw [hc2] at h₇
  have h₉ := regularizedGaussHGFun_eq_sub_mul_add_mul a (b + 1) c hz
  linear_combination -(c - a) * h₂ - (c - a) * (c - b) * h₇ + c * h₅ + c * h₉

private theorem regularizedGaussHGFun_apply_zero (a b c : ℂ) :
    regularizedGaussHGFun a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHGFun_eq_tsum_coeff_mul_pow,
    tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
  simp [coeff_regularizedGaussHGFunSeries]

private theorem hasDerivAt_regularizedGaussHGFun_mul_neg_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w =>
      regularizedGaussHGFun a b c w * regularizedGaussHGFun (-a) (-b) (-c) w -
        a * b * (a - c) * (b - c) * w ^ 2 *
          regularizedGaussHGFun (1 + a) (1 + b) (2 + c) w *
            regularizedGaussHGFun (1 - a) (1 - b) (2 - c) w) 0 z := by
  have hdf₀ := hasDerivAt_regularizedGaussHGFun a b c hz
  have hdg₀ := hasDerivAt_regularizedGaussHGFun (-a) (-b) (-c) hz
  have hs₁ := mul_regularizedGaussHGFun_eq a b c hz
  have hs₂ := mul_regularizedGaussHGFun_eq (-a) (-b) (-c) hz
  have hn1 (s : ℂ) : -s + 1 = 1 - s := by ring
  have hn2 (s : ℂ) : -s + 2 = 2 - s := by ring
  have hp2 : c + 2 = 2 + c := add_comm c 2
  simp only [hn1, hn2, hp2, add_comm a 1, add_comm b 1, add_comm c 1] at hdf₀ hdg₀ hs₁ hs₂
  have hdf₂ :=
    (analyticAt_regularizedGaussHGFun (1 + a) (1 + b) (2 + c) hz).differentiableAt.hasDerivAt
  have hdg₂ :=
    (analyticAt_regularizedGaussHGFun (1 - a) (1 - b) (2 - c) hz).differentiableAt.hasDerivAt
  have hsq : HasDerivAt (fun w : ℂ => a * b * (a - c) * (b - c) * w ^ 2)
      (a * b * (a - c) * (b - c) * (2 * z)) z := by
    simpa [pow_one] using ((hasDerivAt_pow 2 z).const_mul (a * b * (a - c) * (b - c)))
  refine ((hdf₀.mul hdg₀).sub ((hsq.mul hdf₂).mul hdg₂)).congr_deriv ?_
  dsimp only [Pi.mul_apply]
  have hc₁ := mul_deriv_regularizedGaussHGFun_add_mul_eq (1 + a) (1 + b) (1 + c) hz
  have hc₂ := mul_deriv_regularizedGaussHGFun_add_mul_eq (1 - a) (1 - b) (1 - c) hz
  have h1c : (1 : ℂ) + c + 1 = 2 + c := by ring
  have h2c : (1 : ℂ) - c + 1 = 2 - c := by ring
  rw [h1c] at hc₁
  rw [h2c] at hc₂
  linear_combination
    b * regularizedGaussHGFun (1 - a) (1 - b) (1 - c) z * hs₁ -
      b * regularizedGaussHGFun (1 + a) (1 + b) (1 + c) z * hs₂ -
      a * b * (a - c) * (b - c) * z *
        regularizedGaussHGFun (1 - a) (1 - b) (2 - c) z * hc₁ -
      a * b * (a - c) * (b - c) * z *
        regularizedGaussHGFun (1 + a) (1 + b) (2 + c) z * hc₂

/-- Regularized bilinear product identity at opposite parameters on the open unit disk
(DLMF 15.16.4, reciprocal-Gamma form), valid for all complex `a`, `b`, `c`. -/
theorem regularizedGaussHGFun_mul_neg_sub_eq_inv_Gamma_mul (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z * regularizedGaussHGFun (-a) (-b) (-c) z -
      a * b * (a - c) * (b - c) * z ^ 2 *
        regularizedGaussHGFun (1 + a) (1 + b) (2 + c) z *
          regularizedGaussHGFun (1 - a) (1 - b) (2 - c) z =
      (Gamma c * Gamma (-c))⁻¹ := by
  let Φ : ℂ → ℂ := fun w =>
    regularizedGaussHGFun a b c w * regularizedGaussHGFun (-a) (-b) (-c) w -
      a * b * (a - c) * (b - c) * w ^ 2 *
        regularizedGaussHGFun (1 + a) (1 + b) (2 + c) w *
          regularizedGaussHGFun (1 - a) (1 - b) (2 - c) w
  have hconst : Φ z = Φ 0 := by
    refine Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun w hw => ?_) (fun w hw => ?_) (by simpa using hz) (Metric.mem_ball_self zero_lt_one)
    · exact (hasDerivAt_regularizedGaussHGFun_mul_neg_sub a b c
        (by simpa using hw)).differentiableAt.differentiableWithinAt
    · exact (hasDerivAt_regularizedGaussHGFun_mul_neg_sub a b c (by simpa using hw)).deriv
  have hΦ₀ : Φ 0 = (Gamma c * Gamma (-c))⁻¹ := by
    simp [Φ, regularizedGaussHGFun_apply_zero, mul_comm]
  exact hconst.trans hΦ₀

/-- Regularized bilinear product identity at opposite parameters on the open unit disk
(DLMF 15.16.4, reflection form), valid for all complex `a`, `b`, `c`. -/
theorem regularizedGaussHGFun_mul_neg_sub_eq_neg_mul_sin_div_pi (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z * regularizedGaussHGFun (-a) (-b) (-c) z -
      a * b * (a - c) * (b - c) * z ^ 2 *
        regularizedGaussHGFun (1 + a) (1 + b) (2 + c) z *
          regularizedGaussHGFun (1 - a) (1 - b) (2 - c) z =
      -c * sin (π * c) / π := by
  rw [regularizedGaussHGFun_mul_neg_sub_eq_inv_Gamma_mul a b c hz]
  have h₁ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (-c)
  have hsub : -c + 1 = 1 - c := by ring
  rw [hsub] at h₁
  calc (Gamma c * Gamma (-c))⁻¹
      = (Gamma c)⁻¹ * (Gamma (-c))⁻¹ := mul_inv _ _
    _ = (Gamma c)⁻¹ * (-c * (Gamma (1 - c))⁻¹) := by rw [h₁]
    _ = -c * (Gamma c * Gamma (1 - c))⁻¹ := by rw [mul_inv]; ring
    _ = -c * (π / sin (π * c))⁻¹ := by rw [Gamma_mul_Gamma_one_sub]
    _ = -c * sin (π * c) / π := by rw [inv_div, mul_div_assoc]

/-- Bilinear product identity for the ordinary Gauss hypergeometric series on the open unit disk
(DLMF 15.16.4), valid whenever `c` is not an integer. -/
theorem ordinaryHypergeometric_mul_neg_add_eq_one {a b c z : ℂ} (hc : ∀ n : ℤ, c ≠ n)
    (hz : ‖z‖ < 1) :
    ordinaryHypergeometric a b c z * ordinaryHypergeometric (-a) (-b) (-c) z +
      a * b * (a - c) * (b - c) / (c ^ 2 * (1 - c ^ 2)) * z ^ 2 *
        ordinaryHypergeometric (1 + a) (1 + b) (2 + c) z *
          ordinaryHypergeometric (1 - a) (1 - b) (2 - c) z = 1 := by
  have hc₀ : c ≠ 0 := by simpa using hc 0
  have hc₁ : c ≠ 1 := by simpa using hc 1
  have hc_neg₁ : c ≠ -1 := by simpa using hc (-1)
  have h1pc : 1 + c ≠ 0 := fun h => hc_neg₁ (by linear_combination h)
  have h1mc : 1 - c ≠ 0 := sub_ne_zero.mpr hc₁.symm
  have h1c2 : 1 - c ^ 2 ≠ 0 := by
    have hfac : (1 : ℂ) - c ^ 2 = (1 - c) * (1 + c) := by ring
    rw [hfac]
    exact mul_ne_zero h1mc h1pc
  have np_c : ∀ k : ℕ, c ≠ -k := fun k => by simpa using hc (-k)
  have np_mc : ∀ k : ℕ, -c ≠ -k := fun k h => hc k (by linear_combination -h)
  have np_2pc : ∀ k : ℕ, 2 + c ≠ -k := fun k h =>
    hc (-(k + 2 : ℕ)) (by push_cast; linear_combination h)
  have np_2mc : ∀ k : ℕ, 2 - c ≠ -k := fun k h =>
    hc (k + 2 : ℕ) (by push_cast; linear_combination -h)
  have hΓp : Gamma (2 + c) = (1 + c) * c * Gamma c := by
    have h2p : (2 : ℂ) + c = c + 1 + 1 := by ring
    rw [h2p, Gamma_add_one (c + 1) (fun h => hc_neg₁ (by linear_combination h)),
      Gamma_add_one c hc₀]
    ring
  have hΓm : Gamma (2 - c) = (1 - c) * (-c) * Gamma (-c) := by
    have h2m : (2 : ℂ) - c = -c + 1 + 1 := by ring
    rw [h2m, Gamma_add_one (-c + 1) (fun h => hc₁ (by linear_combination -h)),
      Gamma_add_one (-c) (neg_ne_zero.mpr hc₀)]
    ring
  have hreg := regularizedGaussHGFun_mul_neg_sub_eq_inv_Gamma_mul a b c hz
  rw [← ordinaryHypergeometric_div_Gamma_eq np_c, ← ordinaryHypergeometric_div_Gamma_eq np_mc,
    ← ordinaryHypergeometric_div_Gamma_eq np_2pc, ← ordinaryHypergeometric_div_Gamma_eq np_2mc,
    hΓp, hΓm] at hreg
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero np_c
  have hΓmc : Gamma (-c) ≠ 0 := Gamma_ne_zero np_mc
  have hmul := congrArg (fun x => Gamma c * Gamma (-c) * x) hreg
  field_simp [hΓc, hΓmc, hc₀, h1c2, h1pc, h1mc] at hmul ⊢
  linear_combination hmul

/-! ### Elliott's generalized Legendre relation (DLMF 15.16.5) -/

private def legendreCombination (lam mu nu z : ℂ) : ℂ :=
  regularizedGaussHGFun (1 / 2 + lam) (-1 / 2 - nu) (1 + lam + mu) z *
      regularizedGaussHGFun (1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) +
    regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu) (1 + lam + mu) z *
      regularizedGaussHGFun (-1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) -
    regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu) (1 + lam + mu) z *
      regularizedGaussHGFun (1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z)

private theorem deriv_legendreCombination_eq_zero (lam mu nu : ℂ) {z : ℂ}
    (hz₀ : ‖z‖ < 1) (hz₁ : ‖1 - z‖ < 1) :
    deriv (legendreCombination lam mu nu) z = 0 := by
  have hz_ne : z ≠ 0 := by intro rfl; norm_num at hz₁
  have h1z_ne : 1 - z ≠ 0 := sub_ne_zero.mpr fun h => by rw [← h] at hz₀; norm_num at hz₀
  let u₀ := regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu) (1 + lam + mu)
  let um := regularizedGaussHGFun (1 / 2 + lam) (-1 / 2 - nu) (1 + lam + mu)
  let v₀ := regularizedGaussHGFun (1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu)
  let vm := regularizedGaussHGFun (-1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu)
  have hu₀ := (analyticAt_regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu)
    (1 + lam + mu) hz₀).differentiableAt.hasDerivAt
  have hum := (analyticAt_regularizedGaussHGFun (1 / 2 + lam) (-1 / 2 - nu)
    (1 + lam + mu) hz₀).differentiableAt.hasDerivAt
  have hv₀ := ((analyticAt_regularizedGaussHGFun (1 / 2 - lam) (1 / 2 + nu)
    (1 + nu + mu) hz₁).differentiableAt.hasDerivAt).comp z ((hasDerivAt_id z).const_sub 1)
  have hvm := ((analyticAt_regularizedGaussHGFun (-1 / 2 - lam) (1 / 2 + nu)
    (1 + nu + mu) hz₁).differentiableAt.hasDerivAt).comp z ((hasDerivAt_id z).const_sub 1)
  have hd : deriv (legendreCombination lam mu nu) z =
      deriv um z * v₀ (1 - z) + um z * (deriv v₀ (1 - z) * -1) +
        (deriv u₀ z * vm (1 - z) + u₀ z * (deriv vm (1 - z) * -1)) -
        (deriv u₀ z * v₀ (1 - z) + u₀ z * (deriv v₀ (1 - z) * -1)) :=
    (((hum.mul hv₀).add (hu₀.mul hvm)).sub (hu₀.mul hv₀)).deriv
  have eq1 := mul_deriv_regularizedGaussHGFun_add_right (1 / 2 + lam) (-1 / 2 - nu)
    (1 + lam + mu) hz₀
  have eq2 := mul_one_sub_mul_deriv_regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu)
    (1 + lam + mu) hz₀
  have eq3 := mul_deriv_regularizedGaussHGFun_add_right (1 / 2 + nu) (-1 / 2 - lam)
    (1 + nu + mu) hz₁
  have eq4 := mul_one_sub_mul_deriv_regularizedGaussHGFun (1 / 2 + nu) (1 / 2 - lam)
    (1 + nu + mu) hz₁
  rw [regularizedGaussHGFun_symm (1 / 2 + nu) (-1 / 2 - lam),
    regularizedGaussHGFun_symm (1 / 2 + nu) (-1 / 2 - lam + 1)] at eq3
  rw [regularizedGaussHGFun_symm (1 / 2 + nu) (1 / 2 - lam),
    regularizedGaussHGFun_symm (1 / 2 + nu) (1 / 2 - lam - 1)] at eq4
  have h_add (s : ℂ) : (-1 : ℂ) / 2 - s + 1 = 1 / 2 - s := by ring
  have h_sub (s : ℂ) : (1 : ℂ) / 2 - s - 1 = -1 / 2 - s := by ring
  simp only [h_add, h_sub] at eq1 eq2 eq3 eq4
  have hmul : z * (1 - z) * deriv (legendreCombination lam mu nu) z = 0 := by
    rw [hd]
    linear_combination
      (1 - z) * v₀ (1 - z) * eq1 + (vm (1 - z) - v₀ (1 - z)) * eq2 -
        z * u₀ z * eq3 + (u₀ z - um z) * eq4
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hz_ne h1z_ne)

private theorem legendreCombination_eq_at_half (lam mu nu : ℂ) {z : ℂ}
    (hz₀ : ‖z‖ < 1) (hz₁ : ‖1 - z‖ < 1) :
    legendreCombination lam mu nu z = legendreCombination lam mu nu (1 / 2) := by
  let L : Set ℂ := Metric.ball 0 1 ∩ Metric.ball 1 1
  have hmem (w : ℂ) : w ∈ L ↔ ‖w‖ < 1 ∧ ‖1 - w‖ < 1 := by
    simp [L, Metric.mem_ball, dist_eq_norm, norm_sub_rev]
  have hhalf : (1 / 2 : ℂ) ∈ L := by
    rw [hmem]
    constructor <;> norm_num
  refine (Metric.isOpen_ball.inter Metric.isOpen_ball).is_const_of_deriv_eq_zero
    ((convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)).isPreconnected
    (fun w hw => ?_) (fun w hw => ?_) ((hmem z).mpr ⟨hz₀, hz₁⟩) hhalf
  · obtain ⟨hw₀, hw₁⟩ := (hmem w).mp hw
    have ha0 := (analyticAt_regularizedGaussHGFun (1 / 2 + lam) (-1 / 2 - nu)
      (1 + lam + mu) hw₀).differentiableAt
    have ha1 := (analyticAt_regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu)
      (1 + lam + mu) hw₀).differentiableAt
    have hb0 := ((analyticAt_regularizedGaussHGFun (1 / 2 - lam) (1 / 2 + nu)
      (1 + nu + mu) hw₁).differentiableAt).comp w (differentiableAt_id.const_sub 1)
    have hb1 := ((analyticAt_regularizedGaussHGFun (-1 / 2 - lam) (1 / 2 + nu)
      (1 + nu + mu) hw₁).differentiableAt).comp w (differentiableAt_id.const_sub 1)
    exact (((ha0.mul hb0).add (ha1.mul hb1)).sub (ha1.mul hb0)).differentiableWithinAt
  · obtain ⟨hw₀, hw₁⟩ := (hmem w).mp hw
    exact deriv_legendreCombination_eq_zero lam mu nu hw₀ hw₁

private theorem inv_Gamma_mul_integral_term {a b c w : ℝ} (hb : 1 < b) (hcb : 1 < c - b)
    (n : ℕ) :
    (Real.Gamma b * Real.Gamma (c - b))⁻¹ *
        (∫ t in (0 : ℝ)..1,
          t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (Ring.multichoose a n * (w * t) ^ n)) =
      (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b /
        (n ! * Real.Gamma (c + n)) * w ^ n := by
  have hint :
      (∫ t in (0 : ℝ)..1,
        t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (Ring.multichoose a n * (w * t) ^ n)) =
      Ring.multichoose a n * w ^ n *
        ∫ t in (0 : ℝ)..1, t ^ (b + n - 1) * (1 - t) ^ (c - b - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have hpow : t ^ (b - 1) * t ^ n = t ^ (b + n - 1) := by
      rw [← Real.rpow_natCast t n, ← Real.rpow_add ht.1, sub_add_eq_add_sub]
    rw [mul_pow]
    linear_combination Ring.multichoose a n * w ^ n * (1 - t) ^ (c - b - 1) * hpow
  have hmc : Ring.multichoose a n = (ascPochhammer ℝ n).eval a / n ! := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    rw [← h]
    field_simp
  have hbn : ∀ k : ℕ, b ≠ -k := fun k => by linarith [k.cast_nonneg (α := ℝ)]
  have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hΓcb : Real.Gamma (c - b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hpoch := Real.Gamma_add_nat_div_Gamma_eq (n := n) b hbn
  have hbnc : b + (n : ℝ) + (c - b) = c + n := by ring
  rw [hint, TauCeti.integral_rpow_mul_one_sub_rpow (by linarith) (by linarith),
    ProbabilityTheory.beta, hbnc, hmc, ← hpoch]
  field_simp [hΓb, hΓcb]

private theorem regularizedGaussHGFun_ofReal_eq_integral {a b c w : ℝ}
    (hb : 1 < b) (hcb : 1 < c - b) (hw : w ∈ Ioo (0 : ℝ) 1) :
    regularizedGaussHGFun a b c w =
      (((Real.Gamma b * Real.Gamma (c - b))⁻¹ *
        ∫ t in (0 : ℝ)..1,
          t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - w * t) ^ (-a) : ℝ) : ℂ) := by
  have hsum : Summable fun n : ℕ => ‖Ring.multichoose a n‖ * w ^ n := by
    have hs := (TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := a)
      (by rw [abs_of_pos hw.1]; exact hw.2)).summable.norm
    exact hs.congr fun n => by rw [norm_mul, norm_pow, Real.norm_of_nonneg hw.1.le]
  have hcont (n : ℕ) : Continuous fun t : ℝ =>
      t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (Ring.multichoose a n * (w * t) ^ n) :=
    ((Real.continuous_rpow_const (by linarith)).mul
      ((Real.continuous_rpow_const (by linarith)).comp (continuous_const.sub continuous_id))).mul
        (continuous_const.mul ((continuous_const.mul continuous_id).pow n))
  have hdct := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun n t => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (Ring.multichoose a n * (w * t) ^ n))
    (f := fun t => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - w * t) ^ (-a))
    (μ := volume) (a := 0) (b := 1) (fun n _ => ‖Ring.multichoose a n‖ * w ^ n)
    (fun n => (hcont n).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      obtain ⟨ht₀, ht₁⟩ := ht
      have htb : t ^ (b - 1) ≤ 1 := Real.rpow_le_one ht₀.le ht₁ (by linarith)
      have htcb : (1 - t) ^ (c - b - 1) ≤ 1 :=
        Real.rpow_le_one (by linarith) (by linarith) (by linarith)
      have hwt : ‖w * t‖ ≤ w := by
        rw [norm_mul, Real.norm_of_nonneg hw.1.le, Real.norm_of_nonneg ht₀.le]
        exact mul_le_of_le_one_right hw.1.le ht₁
      rw [norm_mul, norm_mul, norm_mul, norm_pow,
        Real.norm_of_nonneg (Real.rpow_nonneg ht₀.le _),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      calc t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (‖Ring.multichoose a n‖ * ‖w * t‖ ^ n)
          ≤ 1 * 1 * (‖Ring.multichoose a n‖ * w ^ n) := by gcongr
        _ = ‖Ring.multichoose a n‖ * w ^ n := by ring)
    (ae_of_all _ fun _ _ => hsum) intervalIntegrable_const
    (ae_of_all _ fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have hwt : |w * t| < 1 := by
        rw [abs_of_nonneg (mul_nonneg hw.1.le ht.1.le)]
        exact (mul_le_of_le_one_right hw.1.le ht.2).trans_lt hw.2
      have h := TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := a) hwt
      rw [one_div, ← Real.rpow_neg (by nlinarith [hw.1, hw.2, ht.1, ht.2])] at h
      exact h.mul_left _)
  have hreal := (hdct.mul_left (Real.Gamma b * Real.Gamma (c - b))⁻¹).congr_fun
    fun n => (inv_Gamma_mul_integral_term hb hcb n).symm
  refine (regularizedGaussHGFun_eq_tsum_coeff_mul_pow _ _ _ _).trans (HasSum.tsum_eq ?_)
  have hp (r : ℝ) (n : ℕ) :
      (ascPochhammer ℂ n).eval (r : ℂ) = (((ascPochhammer ℝ n).eval r : ℝ) : ℂ) := by
    induction n with
    | zero => simp
    | succ n ih => simp [ascPochhammer_succ_eval, ih]
  refine (hasSum_ofReal.mpr hreal).congr_fun fun n => ?_
  rw [coeff_regularizedGaussHGFunSeries, hp a n, hp b n, ← ofReal_natCast n, ← ofReal_add c n,
    Gamma_ofReal]
  push_cast
  rfl

private theorem tendsto_beta_euler_nhdsGE {a b c : ℝ} (ha : a < 0) (hb : 1 < b)
    (hcb : 1 < c - b) :
    Tendsto (fun x : ℝ =>
      ∫ t in (0 : ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - (1 - x) * t) ^ (-a))
      (𝓝[≥] 0) (𝓝 (ProbabilityTheory.beta b (c - b - a))) := by
  let F : ℝ → ℝ → ℝ := fun x t =>
    t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - (1 - x) * t) ^ (-a)
  have hcont_F (x : ℝ) : Continuous (F x) :=
    ((Real.continuous_rpow_const (by linarith)).mul
      ((Real.continuous_rpow_const (by linarith)).comp (continuous_const.sub continuous_id))).mul
        ((Real.continuous_rpow_const (by linarith)).comp
          (continuous_const.sub (continuous_const.mul continuous_id)))
  have hIco : Ico (0 : ℝ) 1 ∈ 𝓝[≥] (0 : ℝ) :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))
  have hcwa : ContinuousWithinAt (fun x : ℝ => ∫ t in (0 : ℝ)..1, F x t) (Ici 0) 0 :=
    intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => (1 : ℝ))
      (Eventually.of_forall fun x => (hcont_F x).aestronglyMeasurable)
      (Filter.eventually_of_mem hIco fun x hx => ae_of_all _ fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        obtain ⟨ht₀, ht₁⟩ := ht
        have h1 : 0 ≤ 1 - (1 - x) * t := by nlinarith [hx.1, hx.2, ht₀, ht₁]
        have h2 : 1 - (1 - x) * t ≤ 1 := by nlinarith [hx.1, hx.2, ht₀, ht₁]
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht₀.le _)
          (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg h1 _))]
        calc F x t ≤ 1 * 1 * 1 := by
              refine mul_le_mul (mul_le_mul (Real.rpow_le_one ht₀.le ht₁ (by linarith))
                (Real.rpow_le_one (by linarith) (by linarith) (by linarith))
                (Real.rpow_nonneg (by linarith) _) zero_le_one)
                (Real.rpow_le_one h1 h2 (by linarith)) (Real.rpow_nonneg h1 _) (by positivity)
          _ = 1 := by ring)
      intervalIntegrable_const
      (ae_of_all _ fun t _ => (Continuous.continuousWithinAt
        (by
          dsimp only [F]
          exact (continuous_const.mul
            ((Real.continuous_rpow_const (by linarith)).comp
              (continuous_const.sub ((continuous_const.sub continuous_id).mul
                continuous_const)))))))
  have hI₀ : (∫ t in (0 : ℝ)..1, F 0 t) = ProbabilityTheory.beta b (c - b - a) := by
    rw [← TauCeti.integral_rpow_mul_one_sub_rpow (by linarith) (by linarith)]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le zero_le_one] at ht
    dsimp only [F]
    rw [sub_zero, one_mul, mul_assoc]
    congr 1
    rcases eq_or_lt_of_le ht.2 with rfl | hlt
    · simp [Real.zero_rpow (by linarith : c - b - 1 ≠ 0),
        Real.zero_rpow (by linarith : c - b - a - 1 ≠ 0)]
    · rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
  exact hI₀ ▸ hcwa.tendsto

private theorem tendsto_regularizedGaussHGFun_one_sub_nhdsGT {a b c : ℝ}
    (ha : a < 0) (hb : 1 < b) (hcb : 1 < c - b) :
    Tendsto (fun x : ℝ => regularizedGaussHGFun a b c ((1 - x : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (((Real.Gamma (c - b - a) / (Real.Gamma (c - b) * Real.Gamma (c - a)) : ℝ) : ℂ))) := by
  have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hΓcb : Real.Gamma (c - b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hΓca : Real.Gamma (c - a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hval : (Real.Gamma b * Real.Gamma (c - b))⁻¹ * ProbabilityTheory.beta b (c - b - a) =
      Real.Gamma (c - b - a) / (Real.Gamma (c - b) * Real.Gamma (c - a)) := by
    have hca : b + (c - b - a) = c - a := by ring
    rw [ProbabilityTheory.beta, hca]
    field_simp [hΓb, hΓcb, hΓca]
  have hint := ((tendsto_beta_euler_nhdsGE ha hb hcb).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)).const_mul (Real.Gamma b * Real.Gamma (c - b))⁻¹
  rw [hval] at hint
  refine (continuous_ofReal.continuousAt.tendsto.comp hint).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  exact (regularizedGaussHGFun_ofReal_eq_integral hb hcb
    ⟨by linarith [hx.2], by linarith [hx.1]⟩).symm

private theorem legendreCombination_half_ofReal {lam mu nu : ℝ}
    (hlam : 1 < lam) (hmu : 1 < mu) (hnu : 1 < nu) :
    legendreCombination lam mu nu (1 / 2) =
      (Gamma ((lam : ℂ) + mu + nu + 3 / 2) * Gamma (1 / 2 + mu))⁻¹ := by
  have hcont_u (β : ℂ) : Tendsto (fun x : ℝ =>
      regularizedGaussHGFun (1 / 2 + (lam : ℂ)) β (1 + lam + mu) (x : ℂ)) (𝓝[>] 0)
      (𝓝 ((Gamma (1 + (lam : ℂ) + mu))⁻¹)) := by
    have hc : ContinuousAt (fun x : ℝ =>
        regularizedGaussHGFun (1 / 2 + (lam : ℂ)) β (1 + lam + mu) (x : ℂ)) 0 :=
      (analyticAt_regularizedGaussHGFun _ _ _ (by simp : ‖((0 : ℝ) : ℂ)‖ < 1)).continuousAt.comp
        continuous_ofReal.continuousAt
    rw [← regularizedGaussHGFun_apply_zero (1 / 2 + (lam : ℂ)) β (1 + lam + mu), ← ofReal_zero]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hv₀ := tendsto_regularizedGaussHGFun_one_sub_nhdsGT
    (a := 1 / 2 - lam) (b := 1 / 2 + nu) (c := 1 + nu + mu)
    (by linarith) (by linarith) (by linarith)
  have hvm := tendsto_regularizedGaussHGFun_one_sub_nhdsGT
    (a := -1 / 2 - lam) (b := 1 / 2 + nu) (c := 1 + nu + mu)
    (by linarith) (by linarith) (by linarith)
  have hcomb := (((hcont_u (-1 / 2 - nu)).sub (hcont_u (1 / 2 - nu))).mul hv₀).add
    ((hcont_u (1 / 2 - nu)).mul hvm)
  have hconst :
      (fun x : ℝ =>
        (regularizedGaussHGFun (1 / 2 + (lam : ℂ)) (-1 / 2 - nu) (1 + lam + mu) x -
            regularizedGaussHGFun (1 / 2 + (lam : ℂ)) (1 / 2 - nu) (1 + lam + mu) x) *
          regularizedGaussHGFun ((1 / 2 - lam : ℝ) : ℂ) ((1 / 2 + nu : ℝ) : ℂ)
            ((1 + nu + mu : ℝ) : ℂ) ((1 - x : ℝ) : ℂ) +
        regularizedGaussHGFun (1 / 2 + (lam : ℂ)) (1 / 2 - nu) (1 + lam + mu) x *
          regularizedGaussHGFun ((-1 / 2 - lam : ℝ) : ℂ) ((1 / 2 + nu : ℝ) : ℂ)
            ((1 + nu + mu : ℝ) : ℂ) ((1 - x : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      fun _ => legendreCombination lam mu nu (1 / 2) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    have hx₀ : ‖(x : ℂ)‖ < 1 := by simp [Real.norm_eq_abs, abs_of_pos hx.1, hx.2]
    have hx₁ : ‖(1 : ℂ) - (x : ℂ)‖ < 1 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.2])]
      linarith [hx.1]
    rw [← legendreCombination_eq_at_half (lam : ℂ) mu nu hx₀ hx₁, legendreCombination]
    push_cast; ring
  rw [tendsto_nhds_unique tendsto_const_nhds (hcomb.congr' hconst), sub_self, zero_mul, zero_add]
  have hΓpos : Real.Gamma (1 + lam + mu) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hc1 : (1 : ℂ) + lam + mu = ((1 + lam + mu : ℝ) : ℂ) := by push_cast; ring
  have hc2 : (lam : ℂ) + mu + nu + 3 / 2 = ((lam + mu + nu + 3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hc3 : (1 : ℂ) / 2 + mu = ((1 / 2 + mu : ℝ) : ℂ) := by push_cast; ring
  rw [hc1, hc2, hc3, Gamma_ofReal, Gamma_ofReal, Gamma_ofReal, ← ofReal_inv, ← ofReal_mul,
    ← ofReal_mul, ← ofReal_inv]
  congr 1
  have hr1 : 1 + nu + mu - (1 / 2 + nu) - (-1 / 2 - lam) = 1 + lam + mu := by ring
  have hr2 : 1 + nu + mu - (1 / 2 + nu) = 1 / 2 + mu := by ring
  have hr3 : 1 + nu + mu - (-1 / 2 - lam) = lam + mu + nu + 3 / 2 := by ring
  rw [hr1, hr2, hr3]
  field_simp [hΓpos]

private theorem differentiable_legendreCombination_half {fl fm fn : ℂ → ℂ}
    (hl : Differentiable ℂ fl) (hm : Differentiable ℂ fm) (hn : Differentiable ℂ fn) :
    Differentiable ℂ fun w => legendreCombination (fl w) (fm w) (fn w) (1 / 2) := by
  have hhalf : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hhalf' : ‖(1 : ℂ) - 1 / 2‖ < 1 := by norm_num
  have dc (c : ℂ) : Differentiable ℂ fun _ : ℂ => c := differentiable_const c
  have hu_m := Differentiable.regularizedGaussHGFun ((dc (1 / 2)).add hl)
    ((dc (-1 / 2)).sub hn) (((dc 1).add hl).add hm) hhalf
  have hu_0 := Differentiable.regularizedGaussHGFun ((dc (1 / 2)).add hl)
    ((dc (1 / 2)).sub hn) (((dc 1).add hl).add hm) hhalf
  have hv_0 := Differentiable.regularizedGaussHGFun ((dc (1 / 2)).sub hl)
    ((dc (1 / 2)).add hn) (((dc 1).add hn).add hm) hhalf'
  have hv_m := Differentiable.regularizedGaussHGFun ((dc (-1 / 2)).sub hl)
    ((dc (1 / 2)).add hn) (((dc 1).add hn).add hm) hhalf'
  exact ((hu_m.mul hv_0).add (hu_0.mul hv_m)).sub (hu_0.mul hv_0)

/-- Regularized form of Elliott's generalized Legendre relation (DLMF 15.16.5) on the open lens
`{z | ‖z‖ < 1 ∧ ‖1 - z‖ < 1}`, valid for all complex parameters `lam`, `mu`, `nu`. -/
theorem regularizedGaussHGFun_legendreRelation (lam mu nu : ℂ) {z : ℂ}
    (hz₀ : ‖z‖ < 1) (hz₁ : ‖1 - z‖ < 1) :
    regularizedGaussHGFun (1 / 2 + lam) (-1 / 2 - nu) (1 + lam + mu) z *
        regularizedGaussHGFun (1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) +
      regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu) (1 + lam + mu) z *
        regularizedGaussHGFun (-1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) -
      regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu) (1 + lam + mu) z *
        regularizedGaussHGFun (1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) =
      (Gamma (lam + mu + nu + 3 / 2) * Gamma (1 / 2 + mu))⁻¹ := by
  have hz_half := legendreCombination_eq_at_half lam mu nu hz₀ hz₁
  dsimp only [legendreCombination] at hz_half
  rw [hz_half]
  have h_id {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
      (h : ∀ r : ℝ, 1 < r → f r = g r) : f = g := by
    have hslit := AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq
      (f := fun w => f (w + 1)) (g := fun w => g (w + 1))
      (fun w _ => (hf.comp (differentiable_id.add (differentiable_const 1))).analyticAt w)
      (fun w _ => (hg.comp (differentiable_id.add (differentiable_const 1))).analyticAt w)
      fun t ht => by exact_mod_cast h (t + 1) (by linarith)
    have hshift := (hf.comp (differentiable_id.add (differentiable_const (I + 1)))).eq_of_ofReal_eq
      (hg.comp (differentiable_id.add (differentiable_const (I + 1)))) fun t => by
        simpa [add_assoc] using hslit (Or.inr (by simp : ((t : ℂ) + I).im ≠ 0))
    ext w
    simpa [sub_add_cancel] using congrFun hshift (w - (I + 1))
  have hinv_diff {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
      Differentiable ℂ fun w => (Gamma (f w))⁻¹ := by
    convert differentiable_one_div_Gamma.comp hf using 1
    rfl
  have step1 {l m : ℝ} (hl : 1 < l) (hm : 1 < m) (ν : ℂ) :
      legendreCombination l m ν (1 / 2) =
        (Gamma ((l : ℂ) + m + ν + 3 / 2) * Gamma (1 / 2 + m))⁻¹ :=
    congrFun (h_id (g := fun ν => (Gamma ((l : ℂ) + m + ν + 3 / 2) * Gamma (1 / 2 + m))⁻¹)
      (differentiable_legendreCombination_half (differentiable_const _) (differentiable_const _)
        differentiable_id)
      (by
        simp_rw [mul_inv]
        exact (hinv_diff (((differentiable_const _).add differentiable_id).add
          (differentiable_const _))).mul (differentiable_const _))
      (fun r hr => legendreCombination_half_ofReal hl hm hr)) ν
  have step2 {l : ℝ} (hl : 1 < l) (μ ν : ℂ) :
      legendreCombination l μ ν (1 / 2) =
        (Gamma ((l : ℂ) + μ + ν + 3 / 2) * Gamma (1 / 2 + μ))⁻¹ :=
    congrFun (h_id (g := fun μ => (Gamma ((l : ℂ) + μ + ν + 3 / 2) * Gamma (1 / 2 + μ))⁻¹)
      (differentiable_legendreCombination_half (differentiable_const _) differentiable_id
        (differentiable_const _))
      (by
        simp_rw [mul_inv]
        exact (hinv_diff ((((differentiable_const _).add differentiable_id).add
          (differentiable_const _)).add (differentiable_const _))).mul
          (hinv_diff ((differentiable_const _).add differentiable_id)))
      (fun r hr => step1 hl hr ν)) μ
  exact congrFun (h_id (g := fun lam => (Gamma (lam + mu + nu + 3 / 2) * Gamma (1 / 2 + mu))⁻¹)
    (differentiable_legendreCombination_half differentiable_id (differentiable_const _)
      (differentiable_const _))
    (by
      simp_rw [mul_inv]
      exact (hinv_diff (((differentiable_id.add (differentiable_const _)).add
        (differentiable_const _)).add (differentiable_const _))).mul (differentiable_const _))
    (fun r hr => step2 hr mu nu)) lam

/-- **Elliott's generalized Legendre relation** (DLMF 15.16.5) for the ordinary Gauss
hypergeometric series on `{z | ‖z‖ < 1 ∧ ‖1 - z‖ < 1}`, with `Γ(1/2 + mu)` in place of DLMF's
misprinted `Γ(1/2 + nu)`. -/
theorem ordinaryHypergeometric_legendreRelation {lam mu nu z : ℂ}
    (h₁ : ∀ k : ℕ, 1 + lam + mu ≠ -k) (h₂ : ∀ k : ℕ, 1 + nu + mu ≠ -k)
    (hz₀ : ‖z‖ < 1) (hz₁ : ‖1 - z‖ < 1) :
    ordinaryHypergeometric (1 / 2 + lam) (-1 / 2 - nu) (1 + lam + mu) z *
        ordinaryHypergeometric (1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) +
      ordinaryHypergeometric (1 / 2 + lam) (1 / 2 - nu) (1 + lam + mu) z *
        ordinaryHypergeometric (-1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) -
      ordinaryHypergeometric (1 / 2 + lam) (1 / 2 - nu) (1 + lam + mu) z *
        ordinaryHypergeometric (1 / 2 - lam) (1 / 2 + nu) (1 + nu + mu) (1 - z) =
      Gamma (1 + lam + mu) * Gamma (1 + nu + mu) *
        ((Gamma (lam + mu + nu + 3 / 2))⁻¹ * (Gamma (1 / 2 + mu))⁻¹) := by
  have ho₁ (a b w : ℂ) : ordinaryHypergeometric a b (1 + lam + mu) w =
      Gamma (1 + lam + mu) * regularizedGaussHGFun a b (1 + lam + mu) w := by
    rw [← ordinaryHypergeometric_div_Gamma_eq h₁, mul_div_cancel₀ _ (Gamma_ne_zero h₁)]
  have ho₂ (a b w : ℂ) : ordinaryHypergeometric a b (1 + nu + mu) w =
      Gamma (1 + nu + mu) * regularizedGaussHGFun a b (1 + nu + mu) w := by
    rw [← ordinaryHypergeometric_div_Gamma_eq h₂, mul_div_cancel₀ _ (Gamma_ne_zero h₂)]
  have hreg := regularizedGaussHGFun_legendreRelation lam mu nu hz₀ hz₁
  rw [mul_inv] at hreg
  rw [ho₁, ho₁, ho₂, ho₂]
  linear_combination Gamma (1 + lam + mu) * Gamma (1 + nu + mu) * hreg

/-- The `lam = mu = nu = 0` specialization of `Complex.ordinaryHypergeometric_legendreRelation` on
`{z | ‖z‖ < 1 ∧ ‖1 - z‖ < 1}`: Legendre's identity in hypergeometric form with constant `2 / π`. -/
theorem ordinaryHypergeometric_legendreRelation_zero {z : ℂ} (hz₀ : ‖z‖ < 1) (hz₁ : ‖1 - z‖ < 1) :
    ordinaryHypergeometric (-1 / 2 : ℂ) (1 / 2) 1 z *
        ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) 1 (1 - z) +
      ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) 1 z *
        ordinaryHypergeometric (-1 / 2 : ℂ) (1 / 2) 1 (1 - z) -
      ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) 1 z *
        ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2) 1 (1 - z) =
      2 / π := by
  have h1 : ∀ k : ℕ, (1 : ℂ) + 0 + 0 ≠ -k := ne_neg_natCast_of_re_pos (by simp)
  have h := ordinaryHypergeometric_legendreRelation (lam := 0) (mu := 0) (nu := 0) h1 h1 hz₀ hz₁
  simp only [add_zero, sub_zero, zero_add] at h
  have hsymm : ordinaryHypergeometric (1 / 2 : ℂ) (-1 / 2) 1 z =
      ordinaryHypergeometric (-1 / 2 : ℂ) (1 / 2) 1 z := by
    rw [ordinaryHypergeometric, ordinaryHypergeometricSeries_symm, ← ordinaryHypergeometric]
  rw [hsymm] at h
  refine h.trans ?_
  have hΓ : Gamma (3 / 2 : ℂ) * Gamma (1 / 2 : ℂ) = π / 2 := by
    have h32 : (3 / 2 : ℂ) = ((1 / 2 + 1 : ℝ) : ℂ) := by push_cast; ring
    have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h32, h12, Gamma_ofReal, Gamma_ofReal, ← ofReal_mul, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq, mul_assoc, Real.mul_self_sqrt Real.pi_nonneg]
    push_cast
    ring
  rw [Gamma_one, mul_one, one_mul, ← mul_inv, hΓ, inv_div]

end Complex

end
