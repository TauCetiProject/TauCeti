/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import Mathlib.Data.Nat.Choose.Cast
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Pochhammer
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Product identities for Gauss hypergeometric series

This file proves three classical product identities for Gauss hypergeometric functions. Two are
Wronskian-type identities for contiguous solutions of the hypergeometric differential equation
(DLMF 15.16.4 and 15.16.5), in which a bilinear combination of Gauss functions collapses to a
constant multiple of a reciprocal Gamma product. The third is the Burchnall–Chaundy product
formula (DLMF 15.16.3), which expands the product of two Gauss functions as a series of Gauss
functions. Because `Complex.regularizedGaussHGFun` divides by `Γ(c)`, each identity holds in
regularized form for all complex parameters without pole exclusions, and dividing by the Gamma
prefactors recovers the normalized identity for `ordinaryHypergeometric` away from the poles.

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

The third identity is the Burchnall–Chaundy product formula (DLMF 15.16.3), which expands the
product of two Gauss functions with the same parameters at arguments `z` and `ζ` in Gauss functions
at `z + ζ - z ζ`, for `‖z‖ < 1`, `‖ζ‖ < 1` and `‖z + ζ - z ζ‖ < 1`:
`𝐅(a, b; c; z) 𝐅(a, b; c; ζ)`
`= ∑ₛ (a)ₛ (b)ₛ (c - a)ₛ (c - b)ₛ / (s! Γ(c + s)) (z ζ)ˢ 𝐅(a + s, b + s; c + 2s; z + ζ - z ζ)`.
The coefficient of `ζⁿ` on the right is a finite sum over `s ≤ n`, which the `n`-fold iterate of
the contiguous relation `Complex.regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul` identifies with
the coefficient of `ζⁿ` on the left. The coefficients of the resulting double series grow at most
polynomially, so it converges absolutely when `‖z‖ + ‖ζ‖ ‖1 - z‖ < 1`; on the rest of the domain
both sides are holomorphic in `ζ` on a convex set, and the identity theorem applies.

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
* `Complex.hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun` — regularized form of the
  Burchnall–Chaundy product formula (DLMF 15.16.3), valid for all `a, b, c : ℂ`.
* `Complex.hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric` — DLMF 15.16.3 for
  `ordinaryHypergeometric` when `c` is not a nonpositive integer.

## References

* J. L. Burchnall and T. W. Chaundy, *Expansions of Appell's double hypergeometric functions*,
  Quart. J. Math. Oxford Ser. **11** (1940), 249–270.
* E. B. Elliott, *A formula including Legendre's $EK' + KE' - KK' = \frac{1}{2}\pi$*, Messenger of
  Mathematics **33** (1904), 31–32.
* A. Erdélyi, W. Magnus, F. Oberhettinger, and F. G. Tricomi, *Higher Transcendental Functions*,
  Vol. I, McGraw–Hill, 1953, §2.1.4 and §2.4.
* NIST *Digital Library of Mathematical Functions*, §15.16, equations 15.16.3–15.16.5,
  <https://dlmf.nist.gov/15.16>.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Real Topology

namespace Complex

/-! ### Bilinear product at opposite parameters (DLMF 15.16.4) -/

private theorem hasDerivAt_regularizedGaussHGFun_mul_neg_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w =>
      regularizedGaussHGFun a b c w * regularizedGaussHGFun (-a) (-b) (-c) w -
        a * b * (a - c) * (b - c) * w ^ 2 *
          regularizedGaussHGFun (1 + a) (1 + b) (2 + c) w *
            regularizedGaussHGFun (1 - a) (1 - b) (2 - c) w) 0 z := by
  have hdf₀ := hasDerivAt_regularizedGaussHGFun a b c hz
  have hdg₀ := hasDerivAt_regularizedGaussHGFun (-a) (-b) (-c) hz
  have hs₁ := regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul a b c hz
  have hs₂ := regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul (-a) (-b) (-c) hz
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
    a * b * regularizedGaussHGFun (1 - a) (1 - b) (1 - c) z * hs₁ +
      a * b * regularizedGaussHGFun (1 + a) (1 + b) (1 + c) z * hs₂ -
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
    simp [Φ, mul_comm]
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

private theorem hasDerivAt_legendreCombination (lam mu nu : ℂ) {z : ℂ}
    (hz₀ : ‖z‖ < 1) (hz₁ : ‖1 - z‖ < 1) :
    HasDerivAt (legendreCombination lam mu nu) 0 z := by
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
  -- Eliminate all four first derivatives using the `b`-raising and `b`-lowering contiguous ODEs.
  refine (((hum.mul hv₀).add (hu₀.mul hvm)).sub (hu₀.mul hv₀)).congr_deriv ?_
  have eq1 := mul_deriv_regularizedGaussHGFun_add_mul_eq_mul (1 / 2 + lam) (-1 / 2 - nu)
    (1 + lam + mu) hz₀
  have eq2 := mul_one_sub_mul_deriv_regularizedGaussHGFun (1 / 2 + lam) (1 / 2 - nu)
    (1 + lam + mu) hz₀
  have eq3 := mul_deriv_regularizedGaussHGFun_add_mul_eq_mul (1 / 2 + nu) (-1 / 2 - lam)
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
  have hmul : z * (1 - z) *
      (deriv um z * v₀ (1 - z) + um z * (deriv v₀ (1 - z) * -1) +
        (deriv u₀ z * vm (1 - z) + u₀ z * (deriv vm (1 - z) * -1)) -
        (deriv u₀ z * v₀ (1 - z) + u₀ z * (deriv v₀ (1 - z) * -1))) = 0 := by
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
    exact (hasDerivAt_legendreCombination lam mu nu hw₀ hw₁).differentiableAt.differentiableWithinAt
  · obtain ⟨hw₀, hw₁⟩ := (hmem w).mp hw
    exact (hasDerivAt_legendreCombination lam mu nu hw₀ hw₁).deriv

private theorem legendreCombination_half_of_re_gt {lam mu : ℂ}
    (hlam : 1 < lam.re) (hmu : 1 < mu.re) (nu : ℂ) :
    legendreCombination lam mu nu (1 / 2) =
      (Gamma (lam + mu + nu + 3 / 2) * Gamma (1 / 2 + mu))⁻¹ := by
  -- Send `z = x → 0⁺` along `(0, 1)`: the factors at `x` approach `(Γ(1 + λ + μ))⁻¹` while the
  -- factors at `1 - x` approach their Gauss `z → 1` values.
  have hcont_u (β : ℂ) : Tendsto
      (fun x : ℝ => regularizedGaussHGFun (1 / 2 + lam) β (1 + lam + mu) (x : ℂ))
      (𝓝[>] 0) (𝓝 (Gamma (1 + lam + mu))⁻¹) := by
    have hc : ContinuousAt
        (fun x : ℝ => regularizedGaussHGFun (1 / 2 + lam) β (1 + lam + mu) (x : ℂ)) 0 :=
      (analyticAt_regularizedGaussHGFun _ _ _ (by simp : ‖((0 : ℝ) : ℂ)‖ < 1)).continuousAt.comp
        continuous_ofReal.continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have htend_one : Tendsto (fun x : ℝ => (1 : ℂ) - x) (𝓝[>] 0) (𝓝[Metric.ball 0 1] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous fun x : ℝ => (1 : ℂ) - x := by fun_prop
      simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
      rw [Metric.mem_ball, dist_zero_right, ← ofReal_one, ← ofReal_sub, norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith [hx.2])]
      linarith [hx.1]
  have h12 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hm12 : ((-1 : ℂ) / 2).re = -1 / 2 := by norm_num
  have hv₀ := (tendsto_regularizedGaussHGFun_nhdsWithin_ball_one (a := 1 / 2 - lam)
    (b := 1 / 2 + nu) (c := 1 + nu + mu)
    (by simp only [add_re, sub_re, one_re, h12]; linarith)).comp htend_one
  have hvm := (tendsto_regularizedGaussHGFun_nhdsWithin_ball_one (a := -1 / 2 - lam)
    (b := 1 / 2 + nu) (c := 1 + nu + mu)
    (by simp only [add_re, sub_re, one_re, h12, hm12]; linarith)).comp htend_one
  have hcomb := (((hcont_u (-1 / 2 - nu)).mul hv₀).add ((hcont_u (1 / 2 - nu)).mul hvm)).sub
    ((hcont_u (1 / 2 - nu)).mul hv₀)
  have hconst : (fun x : ℝ => legendreCombination lam mu nu x) =ᶠ[𝓝[>] 0]
      fun _ => legendreCombination lam mu nu (1 / 2) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    have hx₀ : ‖(x : ℂ)‖ < 1 := by simp [Real.norm_eq_abs, abs_of_pos hx.1, hx.2]
    have hx₁ : ‖(1 : ℂ) - x‖ < 1 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.2])]
      linarith [hx.1]
    exact legendreCombination_eq_at_half lam mu nu hx₀ hx₁
  rw [tendsto_nhds_unique tendsto_const_nhds (hcomb.congr' hconst)]
  have hΓ_ne : Gamma (1 + lam + mu) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
  have hr1 : 1 + nu + mu - (-1 / 2 - lam) - (1 / 2 + nu) = 1 + lam + mu := by ring
  have hr2 : 1 + nu + mu - (-1 / 2 - lam) = lam + mu + nu + 3 / 2 := by ring
  have hr3 : 1 + nu + mu - (1 / 2 + nu) = 1 / 2 + mu := by ring
  rw [add_sub_right_comm, sub_self, zero_add, hr1, hr2, hr3]
  field_simp [hΓ_ne]

private theorem differentiable_legendreCombination_half {fl fm : ℂ → ℂ}
    (hl : Differentiable ℂ fl) (hm : Differentiable ℂ fm) (nu : ℂ) :
    Differentiable ℂ fun w => legendreCombination (fl w) (fm w) nu (1 / 2) := by
  have hhalf : ∀ _ : ℂ, ‖(1 / 2 : ℂ)‖ < 1 := fun _ => by norm_num
  have hhalf' : ∀ _ : ℂ, ‖(1 : ℂ) - 1 / 2‖ < 1 := fun _ => by norm_num
  have hu_m : Differentiable ℂ fun w =>
      regularizedGaussHGFun (1 / 2 + fl w) (-1 / 2 - nu) (1 + fl w + fm w) (1 / 2) :=
    Differentiable.regularizedGaussHGFun (by fun_prop) (differentiable_const _) (by fun_prop)
      (differentiable_const _) hhalf
  have hu_0 : Differentiable ℂ fun w =>
      regularizedGaussHGFun (1 / 2 + fl w) (1 / 2 - nu) (1 + fl w + fm w) (1 / 2) :=
    Differentiable.regularizedGaussHGFun (by fun_prop) (differentiable_const _) (by fun_prop)
      (differentiable_const _) hhalf
  have hv_0 : Differentiable ℂ fun w =>
      regularizedGaussHGFun (1 / 2 - fl w) (1 / 2 + nu) (1 + nu + fm w) (1 - 1 / 2) :=
    Differentiable.regularizedGaussHGFun (by fun_prop) (differentiable_const _) (by fun_prop)
      (differentiable_const _) hhalf'
  have hv_m : Differentiable ℂ fun w =>
      regularizedGaussHGFun (-1 / 2 - fl w) (1 / 2 + nu) (1 + nu + fm w) (1 - 1 / 2) :=
    Differentiable.regularizedGaussHGFun (by fun_prop) (differentiable_const _) (by fun_prop)
      (differentiable_const _) hhalf'
  exact ((hu_m.mul hv_0).add (hu_0.mul hv_m)).sub (hu_0.mul hv_0)

private theorem differentiable_inv_Gamma_legendreRHS {fl fm : ℂ → ℂ}
    (hl : Differentiable ℂ fl) (hm : Differentiable ℂ fm) (nu : ℂ) :
    Differentiable ℂ fun w =>
      (Gamma (fl w + fm w + nu + 3 / 2) * Gamma (1 / 2 + fm w))⁻¹ := by
  simp_rw [mul_inv]
  exact (differentiable_one_div_Gamma.comp (by fun_prop)).mul
    (differentiable_one_div_Gamma.comp (by fun_prop))

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
  -- First collapse `z` to `1 / 2` using vanishing of the `z`-derivative on the open lens.
  have hz_half := legendreCombination_eq_at_half lam mu nu hz₀ hz₁
  dsimp only [legendreCombination] at hz_half
  rw [hz_half]
  -- Extend `(lam, mu)` from `(1, ∞)²` to `ℂ²` via `Differentiable.eq_of_ofReal_gt_eq`.
  have step {l : ℝ} (hl : 1 < l) (μ : ℂ) :
      legendreCombination l μ nu (1 / 2) =
        (Gamma ((l : ℂ) + μ + nu + 3 / 2) * Gamma (1 / 2 + μ))⁻¹ :=
    congrFun ((differentiable_legendreCombination_half
        (differentiable_const _) differentiable_fun_id nu).eq_of_ofReal_gt_eq
      (differentiable_inv_Gamma_legendreRHS
        (differentiable_const _) differentiable_fun_id nu)
      fun r (hr : 1 < r) => legendreCombination_half_of_re_gt
        (by simpa using hl) (by simpa using hr) nu) μ
  exact congrFun ((differentiable_legendreCombination_half
      differentiable_fun_id (differentiable_const _) nu).eq_of_ofReal_gt_eq
    (differentiable_inv_Gamma_legendreRHS
      differentiable_fun_id (differentiable_const _) nu)
    fun r (hr : 1 < r) => step hr mu) lam

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

/-! ### Burchnall–Chaundy product formula (DLMF 15.16.3) -/

section BurchnallChaundy

open Finset

/-- The weight `C(s + m, s) (c + s)ₘ` of `z ^ s (1 - z) ^ m 𝐅(a + s + m, b + s + m; c + 2s + m; z)`
in the `(s + m)`-fold iterate of `Complex.regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul`. -/
private noncomputable def bcWeight (c : ℂ) (s m : ℕ) : ℂ :=
  ((s + m).choose s : ℂ) * (ascPochhammer ℂ m).eval (c + s)

/-- The factor `(c - a)ₛ (c - b)ₛ` of the iterated contiguous relation. -/
private noncomputable def bcP (a b c : ℂ) (s : ℕ) : ℂ :=
  (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b)

/-- The term `z ^ s (1 - z) ^ m 𝐅(a + s + m, b + s + m; c + 2s + m; z)` of the iterated contiguous
relation. -/
private noncomputable def bcX (a b c z : ℂ) (s m : ℕ) : ℂ :=
  z ^ s * (1 - z) ^ m * regularizedGaussHGFun (a + s + m) (b + s + m) (c + 2 * s + m) z

/-- Pascal-type recurrence for `bcWeight`, splitting off the last step of the iteration. -/
private theorem bcWeight_eq (c : ℂ) {s m : ℕ} (h : s + m ≠ 0) :
    bcWeight c s m =
      (if m = 0 then 0 else bcWeight c s (m - 1) * (c + 2 * s + (m - 1 : ℕ))) +
        (if s = 0 then 0 else bcWeight c (s - 1) m) := by
  rcases s with _ | s <;> rcases m with _ | m
  · simp at h
  · simp [bcWeight, ascPochhammer_succ_eval]
  · simp [bcWeight]
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, bcWeight]
    set N := s + m + 1
    rw [show s + 1 + (m + 1) = N + 1 by omega, show s + 1 + m = N by omega,
      show s + (m + 1) = N by omega, show c + ((s + 1 : ℕ) : ℂ) = c + s + 1 by push_cast; ring]
    have h₁ : ((N + 1).choose (s + 1) : ℂ) = N.choose s + N.choose (s + 1) := by
      exact_mod_cast Nat.choose_succ_succ N s
    have h₂ : (N.choose (s + 1) : ℂ) * (s + 1) = N.choose s * (m + 1) := by
      have := Nat.choose_succ_right_eq N s
      rw [show N - s = m + 1 by omega] at this
      exact_mod_cast this
    have hp : (ascPochhammer ℂ (m + 1)).eval (c + s) =
        (c + s) * (ascPochhammer ℂ m).eval (c + s + 1) := by
      rw [ascPochhammer_succ_eval, ← ascPochhammer_eval_succ]
    rw [ascPochhammer_succ_eval, hp]
    push_cast
    linear_combination (ascPochhammer ℂ m).eval (c + s + 1) * ((c + s + 1 + m) * h₁ - h₂)

/-- One step of `Complex.regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul` on the terms `bcX`. -/
private theorem bcP_mul_bcX (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (s m : ℕ) :
    bcP a b c s * bcX a b c z s m = (c + 2 * s + m) * bcP a b c s * bcX a b c z s (m + 1) +
      bcP a b c (s + 1) * bcX a b c z (s + 1) m := by
  have hs (x : ℂ) : x + ((s + 1 : ℕ) : ℂ) + m = x + s + m + 1 := by push_cast; ring
  have hm (x y : ℂ) : x + y + ((m + 1 : ℕ) : ℂ) = x + y + m + 1 := by push_cast; ring
  have hc : c + 2 * ((s + 1 : ℕ) : ℂ) + m = c + 2 * s + m + 2 := by push_cast; ring
  simp only [bcP, bcX, ascPochhammer_succ_eval]
  rw [hs a, hs b, hc, hm a, hm b, hm c,
    regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul (a + s + m) (b + s + m) (c + 2 * s + m) hz]
  ring

/-- Iterating `Complex.regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul` `n` times. -/
private theorem regularizedGaussHGFun_eq_sum_bcWeight (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (n : ℕ) :
    regularizedGaussHGFun a b c z =
      ∑ p ∈ antidiagonal n, bcWeight c p.1 p.2 * (bcP a b c p.1 * bcX a b c z p.1 p.2) := by
  induction n with
  | zero => simp [bcWeight, bcP, bcX]
  | succ n ih =>
    rw [ih]
    calc ∑ p ∈ antidiagonal n, bcWeight c p.1 p.2 * (bcP a b c p.1 * bcX a b c z p.1 p.2)
        = ∑ p ∈ antidiagonal n, (bcWeight c p.1 p.2 * (c + 2 * p.1 + p.2) *
            (bcP a b c p.1 * bcX a b c z p.1 (p.2 + 1)) +
          bcWeight c p.1 p.2 * (bcP a b c (p.1 + 1) * bcX a b c z (p.1 + 1) p.2)) :=
          sum_congr rfl fun p _ => by rw [bcP_mul_bcX a b c hz]; ring
      _ = ∑ p ∈ antidiagonal (n + 1),
            ((if p.2 = 0 then 0 else bcWeight c p.1 (p.2 - 1) * (c + 2 * p.1 + (p.2 - 1 : ℕ))) *
              (bcP a b c p.1 * bcX a b c z p.1 p.2) +
            (if p.1 = 0 then 0 else bcWeight c (p.1 - 1) p.2) *
              (bcP a b c p.1 * bcX a b c z p.1 p.2)) := by
          rw [sum_add_distrib, sum_add_distrib, Nat.sum_antidiagonal_succ',
            Nat.sum_antidiagonal_succ]
          simp
      _ = ∑ p ∈ antidiagonal (n + 1), bcWeight c p.1 p.2 * (bcP a b c p.1 * bcX a b c z p.1 p.2) :=
          sum_congr rfl fun p hp => by
            rw [bcWeight_eq c (s := p.1) (m := p.2) (by rw [mem_antidiagonal] at hp; omega)]
            ring

/-- `bcWeight c s m / ((s + m)! Γ(c + s + m)) = 1 / (s! m! Γ(c + s))`, for all `c`. -/
private theorem bcWeight_mul_inv (c : ℂ) (s m : ℕ) :
    bcWeight c s m * (((s + m)! : ℂ)⁻¹ * (Gamma (c + (s + m : ℕ)))⁻¹) =
      (s ! : ℂ)⁻¹ * (m ! : ℂ)⁻¹ * (Gamma (c + s))⁻¹ := by
  rw [inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (c + s) m, bcWeight,
    show c + ((s + m : ℕ) : ℂ) = c + s + m by push_cast; ring, Nat.cast_add_choose]
  field_simp [Nat.factorial_ne_zero]

/-- The coefficient `(a)ₛ (b)ₛ (c - a)ₛ (c - b)ₛ / (s! Γ(c + s))` of the Burchnall–Chaundy
expansion. -/
private noncomputable def bcCoeff (a b c : ℂ) (s : ℕ) : ℂ :=
  (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b * (ascPochhammer ℂ s).eval (c - a) *
    (ascPochhammer ℂ s).eval (c - b) / (s ! * Gamma (c + s))

/-- The norm of a term of the Burchnall–Chaundy double series, with the Pochhammer symbols in `a`
and `b` merged. -/
private theorem norm_bcCoeff_mul_coeff (a b c : ℂ) (s j : ℕ) :
    ‖bcCoeff a b c s‖ * ‖(regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)).coeff j‖ =
      ‖(ascPochhammer ℂ (s + j)).eval a‖ * ‖(ascPochhammer ℂ (s + j)).eval b‖ *
        (‖(ascPochhammer ℂ s).eval (c - a)‖ * ‖(ascPochhammer ℂ s).eval (c - b)‖) *
        (‖(Gamma (c + s))⁻¹‖ * ‖(Gamma (c + (2 * s + j : ℕ)))⁻¹‖) / (s ! * j !) := by
  rw [TauCeti.ascPochhammer_add_eval a s j, TauCeti.ascPochhammer_add_eval b s j,
    show c + ((2 * s + j : ℕ) : ℂ) = c + 2 * s + j by push_cast; ring]
  simp only [bcCoeff, coeff_regularizedGaussHGFunSeries, norm_mul, norm_inv,
    Complex.norm_natCast, div_eq_mul_inv, mul_inv]
  ring

/-- Polynomial growth of the Burchnall–Chaundy double series, from bounds on the Pochhammer symbols
of the parameters and on `1 / Γ(c + k)`. -/
private theorem norm_bcCoeff_mul_coeff_le (a b c : ℂ) {M N : ℕ} {G R : ℝ} (hR : 0 ≤ R)
    (hpoch : ∀ {x : ℂ}, x ∈ ({a, b, c - a, c - b} : Set ℂ) → ∀ n : ℕ,
      ‖(ascPochhammer ℂ n).eval x‖ ≤ n ! * ((M : ℝ) + n) ^ M)
    (hgam : ∀ k : ℕ, ‖(Gamma (c + k))⁻¹‖ * k ! ≤ G * (R + k) ^ N) (s j : ℕ) :
    ‖bcCoeff a b c s‖ * ‖(regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)).coeff j‖ ≤
      G ^ 2 * ((M : ℝ) + R + 2) ^ (4 * M + 2 * N) *
        (((s : ℝ) + 1) * ((j : ℝ) + 1)) ^ (4 * M + 2 * N) := by
  have hA := mul_le_mul (hpoch (x := a) (by simp) (s + j)) (hpoch (x := b) (by simp) (s + j))
    (norm_nonneg _) (by positivity)
  have hB := mul_le_mul (hpoch (x := c - a) (by simp) s) (hpoch (x := c - b) (by simp) s)
    (norm_nonneg _) (by positivity)
  have hC : ‖(Gamma (c + s))⁻¹‖ * ‖(Gamma (c + (2 * s + j : ℕ)))⁻¹‖ ≤
      G ^ 2 * ((R + s) ^ N * (R + (2 * s + j : ℕ)) ^ N) / (s ! * (2 * s + j)!) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖(Gamma (c + s))⁻¹‖ * ‖(Gamma (c + (2 * s + j : ℕ)))⁻¹‖ * (s ! * (2 * s + j)!)
        = (‖(Gamma (c + s))⁻¹‖ * s !) * (‖(Gamma (c + (2 * s + j : ℕ)))⁻¹‖ * (2 * s + j)!) := by
          ring
      _ ≤ (G * (R + s) ^ N) * (G * (R + (2 * s + j : ℕ)) ^ N) :=
          mul_le_mul (hgam s) (hgam _) (by positivity)
            ((mul_nonneg (norm_nonneg _) (by positivity)).trans (hgam s))
      _ = G ^ 2 * ((R + s) ^ N * (R + (2 * s + j : ℕ)) ^ N) := by ring
  set Y : ℝ := ((M : ℝ) + R + 2) * (((s : ℝ) + 1) * ((j : ℝ) + 1))
  have hs : (0 : ℝ) ≤ s := s.cast_nonneg
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  have hpoly : ((M : ℝ) + (s + j : ℕ)) ^ M * ((M : ℝ) + (s + j : ℕ)) ^ M *
      (((M : ℝ) + s) ^ M * ((M : ℝ) + s) ^ M) * ((R + s) ^ N * (R + (2 * s + j : ℕ)) ^ N) ≤
        Y ^ (4 * M + 2 * N) := by
    have h₁ : (M : ℝ) + (s + j : ℕ) ≤ Y := by push_cast; nlinarith [mul_nonneg hs hj]
    have h₂ : (M : ℝ) + s ≤ Y := by nlinarith [mul_nonneg hs hj]
    have h₃ : R + s ≤ Y := by nlinarith [mul_nonneg hs hj]
    have h₄ : R + (2 * s + j : ℕ) ≤ Y := by push_cast; nlinarith [mul_nonneg hs hj]
    calc _ ≤ Y ^ M * Y ^ M * (Y ^ M * Y ^ M) * (Y ^ N * Y ^ N) := by gcongr
      _ = Y ^ (4 * M + 2 * N) := by ring
  rw [norm_bcCoeff_mul_coeff]
  calc _ ≤ ((s + j)! * ((M : ℝ) + (s + j : ℕ)) ^ M * ((s + j)! * ((M : ℝ) + (s + j : ℕ)) ^ M)) *
        (s ! * ((M : ℝ) + s) ^ M * (s ! * ((M : ℝ) + s) ^ M)) *
        (G ^ 2 * ((R + s) ^ N * (R + (2 * s + j : ℕ)) ^ N) / (s ! * (2 * s + j)!)) /
          (s ! * j !) := by gcongr
    _ = G ^ 2 * (((M : ℝ) + (s + j : ℕ)) ^ M * ((M : ℝ) + (s + j : ℕ)) ^ M *
          (((M : ℝ) + s) ^ M * ((M : ℝ) + s) ^ M) * ((R + s) ^ N * (R + (2 * s + j : ℕ)) ^ N)) *
          (((s + j)! : ℝ) * (s + j)! / ((2 * s + j)! * j !)) := by
        field_simp
    _ ≤ G ^ 2 * Y ^ (4 * M + 2 * N) * 1 := by
        gcongr
        exact (div_le_one (by positivity)).2
          (mod_cast Nat.factorial_add_mul_factorial_add_le s j)
    _ = _ := by simp only [Y, mul_pow]; ring

/-- The terms of the Burchnall–Chaundy double series grow at most polynomially. -/
private theorem exists_norm_bcCoeff_mul_coeff_le (a b c : ℂ) : ∃ D : ℝ, ∃ Q : ℕ, ∀ s j : ℕ,
    ‖bcCoeff a b c s‖ * ‖(regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)).coeff j‖ ≤
      D * (((s : ℝ) + 1) * ((j : ℝ) + 1)) ^ Q := by
  obtain ⟨M, hM⟩ := exists_nat_ge (‖a‖ + ‖b‖ + ‖c - a‖ + ‖c - b‖)
  obtain ⟨N, hN⟩ := exists_nat_ge (1 - c.re)
  have hpoch {x : ℂ} (hx : x ∈ ({a, b, c - a, c - b} : Set ℂ)) (n : ℕ) :
      ‖(ascPochhammer ℂ n).eval x‖ ≤ n ! * ((M : ℝ) + n) ^ M := by
    refine TauCeti.norm_ascPochhammer_eval_le_factorial_mul_pow n ?_
    have := norm_nonneg a
    have := norm_nonneg b
    have := norm_nonneg (c - a)
    have := norm_nonneg (c - b)
    rcases hx with rfl | rfl | rfl | rfl <;> linarith
  -- `‖1 / Γ(c + k)‖ k! ≤ ‖1 / Γ(c + N)‖ (M + N + k) ^ N`, from
  -- `1 / Γ(c + k) = (c + k)_N / Γ(c + k + N)` and the factorial decay of `1 / Γ` on `1 ≤ re`.
  have hgam (k : ℕ) : ‖(Gamma (c + k))⁻¹‖ * k ! ≤
      ‖(Gamma (c + N))⁻¹‖ * (((M + N : ℕ) : ℝ) + k) ^ N := by
    rw [inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (c + k) N, norm_mul]
    have h₁ : ‖(ascPochhammer ℂ N).eval (c + k)‖ ≤ (((M + N : ℕ) : ℝ) + k) ^ N := by
      have hc : ‖c + k‖ ≤ ((M + k + 1 : ℕ) : ℝ) := by
        have := norm_sub_norm_le c a
        have := norm_nonneg b
        have := norm_nonneg (c - b)
        refine (norm_add_le _ _).trans ?_
        push_cast
        rw [Complex.norm_natCast]
        linarith
      refine (TauCeti.norm_ascPochhammer_eval_le_ascFactorial N hc).trans ?_
      have := Nat.ascFactorial_le_pow_add (M + k) N
      rw [show M + k + N = M + N + k by omega] at this
      exact_mod_cast this
    have h₂ : ‖(Gamma (c + k + N))⁻¹‖ * k ! ≤ ‖(Gamma (c + N))⁻¹‖ := by
      have := norm_inv_Gamma_add_natCast_le (s := c + N) (by simp; linarith) k
      rw [show c + k + N = c + N + k by ring]
      rwa [le_div_iff₀ (by positivity)] at this
    calc ‖(ascPochhammer ℂ N).eval (c + k)‖ * ‖(Gamma (c + k + N))⁻¹‖ * k !
        = ‖(ascPochhammer ℂ N).eval (c + k)‖ * (‖(Gamma (c + k + N))⁻¹‖ * k !) := by ring
      _ ≤ (((M + N : ℕ) : ℝ) + k) ^ N * ‖(Gamma (c + N))⁻¹‖ := by gcongr
      _ = ‖(Gamma (c + N))⁻¹‖ * (((M + N : ℕ) : ℝ) + k) ^ N := by ring
  exact ⟨_, _, norm_bcCoeff_mul_coeff_le a b c (by positivity) hpoch hgam⟩

/-- Absolute convergence of the Burchnall–Chaundy double series for `0 ≤ x, y < 1`. -/
private theorem summable_norm_bcCoeff_mul_tsum (a b c : ℂ) {x y : ℝ} (hx₀ : 0 ≤ x) (hx : x < 1)
    (hy₀ : 0 ≤ y) (hy : y < 1) :
    Summable fun s : ℕ => ‖bcCoeff a b c s‖ * x ^ s *
      ∑' j, ‖(regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)).coeff j‖ * y ^ j := by
  obtain ⟨D, Q, hDQ⟩ := exists_norm_bcCoeff_mul_coeff_le a b c
  have hgeo {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) :
      Summable fun n : ℕ => ((n : ℝ) + 1) ^ Q * r ^ n := by
    have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr₀]
    refine (((summable_pow_mul_geometric_of_norm_lt_one Q hr').add
      (summable_geometric_of_lt_one hr₀ hr)).mul_left (2 ^ (Q - 1))).of_nonneg_of_le
      (fun n => mul_nonneg (pow_nonneg n.cast_add_one_pos.le _) (pow_nonneg hr₀ _)) fun n => ?_
    calc ((n : ℝ) + 1) ^ Q * r ^ n ≤ 2 ^ (Q - 1) * ((n : ℝ) ^ Q + 1 ^ Q) * r ^ n := by
          gcongr; exact add_pow_le n.cast_nonneg zero_le_one Q
      _ = 2 ^ (Q - 1) * ((n : ℝ) ^ Q * r ^ n + r ^ n) := by ring
  set F : ℕ × ℕ → ℝ := fun p => ‖bcCoeff a b c p.1‖ * x ^ p.1 *
    (‖(regularizedGaussHGFunSeries (a + p.1) (b + p.1) (c + 2 * p.1)).coeff p.2‖ * y ^ p.2)
  have hF₀ : 0 ≤ F := fun p => mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hx₀ _))
    (mul_nonneg (norm_nonneg _) (pow_nonneg hy₀ _))
  have hF : Summable F := by
    refine (((hgeo hx₀ hx).mul_of_nonneg (hgeo hy₀ hy)
      (fun n => mul_nonneg (pow_nonneg n.cast_add_one_pos.le _) (pow_nonneg hx₀ _))
      fun n => mul_nonneg (pow_nonneg n.cast_add_one_pos.le _) (pow_nonneg hy₀ _)).mul_left
        D).of_nonneg_of_le hF₀ fun p => ?_
    calc F p = ‖bcCoeff a b c p.1‖ *
          ‖(regularizedGaussHGFunSeries (a + p.1) (b + p.1) (c + 2 * p.1)).coeff p.2‖ *
            (x ^ p.1 * y ^ p.2) := by simp only [F]; ring
      _ ≤ D * (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) ^ Q * (x ^ p.1 * y ^ p.2) :=
          mul_le_mul_of_nonneg_right (hDQ p.1 p.2) (by positivity)
      _ = D * ((((p.1 : ℝ) + 1) ^ Q * x ^ p.1) * (((p.2 : ℝ) + 1) ^ Q * y ^ p.2)) := by
          rw [mul_pow]; ring
  refine ((summable_prod_of_nonneg hF₀).1 hF).2.congr fun s => ?_
  simp only [F]
  rw [tsum_mul_left]

/-- The coefficient of `ζ ^ n` in the Burchnall–Chaundy double series. -/
private theorem sum_antidiagonal_bcCoeff (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (ζ : ℂ) (n : ℕ) :
    ∑ q ∈ antidiagonal n, bcCoeff a b c q.1 * (z * ζ) ^ q.1 * ((ζ * (1 - z)) ^ q.2 *
        ((ascPochhammer ℂ q.2).eval (a + q.1) * (ascPochhammer ℂ q.2).eval (b + q.1) / q.2 ! *
          regularizedGaussHGFun (a + q.1 + q.2) (b + q.1 + q.2) (c + 2 * q.1 + q.2) z)) =
      (regularizedGaussHGFunSeries a b c).coeff n * ζ ^ n * regularizedGaussHGFun a b c z := by
  rw [regularizedGaussHGFun_eq_sum_bcWeight a b c hz n, mul_sum]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨s, m⟩ := q
  rw [mem_antidiagonal] at hq
  subst hq
  have hw := bcWeight_mul_inv c s m
  simp only [bcCoeff, bcP, bcX, coeff_regularizedGaussHGFunSeries,
    TauCeti.ascPochhammer_add_eval a s m, TauCeti.ascPochhammer_add_eval b s m, div_eq_mul_inv,
    mul_inv, mul_pow] at hw ⊢
  linear_combination (-(ascPochhammer ℂ s).eval a * (ascPochhammer ℂ m).eval (a + s) *
    ((ascPochhammer ℂ s).eval b * (ascPochhammer ℂ m).eval (b + s)) *
    ((ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b)) *
    (z ^ s * (1 - z) ^ m *
      regularizedGaussHGFun (a + s + m) (b + s + m) (c + 2 * s + m) z) * ζ ^ (s + m)) * hw

/-- The triple series behind the Burchnall–Chaundy formula, indexed by `(s, (m, i))`, where `m` is
the power of `ζ (1 - z)` and `i` the power of `z` in the binomial expansion of
`𝐅(a + s, b + s; c + 2s; ζ (1 - z) + z)`. -/
private noncomputable def bcTriple (a b c z ζ : ℂ) (p : ℕ × ℕ × ℕ) : ℂ :=
  bcCoeff a b c p.1 * (z * ζ) ^ p.1 * (((p.2.1 + p.2.2).choose p.2.1 : ℂ) *
    (regularizedGaussHGFunSeries (a + p.1) (b + p.1) (c + 2 * p.1)).coeff (p.2.1 + p.2.2) *
      ((ζ * (1 - z)) ^ p.2.1 * z ^ p.2.2))

/-- The triple series `bcTriple` converges absolutely when `‖z ζ‖ < 1` and
`‖ζ (1 - z)‖ + ‖z‖ < 1`. -/
private theorem summable_bcTriple (a b c : ℂ) {z ζ : ℂ} (hzζ : ‖z * ζ‖ < 1)
    (hu : ‖ζ * (1 - z)‖ + ‖z‖ < 1) : Summable (bcTriple a b c z ζ) := by
  have hn (s : ℕ) := hasSum_norm_choose_mul_coeff_regularizedGaussHGFunSeries (a + s) (b + s)
    (c + 2 * s) hu
  refine Summable.of_norm ((summable_prod_of_nonneg fun p => norm_nonneg _).2
    ⟨fun s => ?_, ?_⟩)
  · exact ((hn s).summable.mul_left
      ‖bcCoeff a b c s * (z * ζ) ^ s‖).congr fun q => (norm_mul _ _).symm
  · refine (summable_norm_bcCoeff_mul_tsum a b c (norm_nonneg _) hzζ (by positivity) hu).congr
      fun s => ?_
    simp only [bcTriple]
    rw [tsum_congr fun q => norm_mul (bcCoeff a b c s * (z * ζ) ^ s) _, tsum_mul_left,
      (hn s).tsum_eq]
    simp only [norm_mul, norm_pow]

/-- The Burchnall–Chaundy expansion where the binomial double series converges absolutely. -/
private theorem hasSum_bcCoeff_of_norm_add_norm_mul_lt_one (a b c : ℂ) {z ζ : ℂ}
    (h : ‖z‖ + ‖ζ‖ * ‖1 - z‖ < 1) :
    HasSum (fun s : ℕ => bcCoeff a b c s * (z * ζ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  have hζz := mul_nonneg (norm_nonneg ζ) (norm_nonneg (1 - z))
  have hz : ‖z‖ < 1 := by linarith
  have hζ : ‖ζ‖ < 1 := by
    have h₁ : 1 - ‖z‖ ≤ ‖1 - z‖ := by simpa using norm_sub_norm_le (1 : ℂ) z
    nlinarith [mul_le_mul_of_nonneg_left h₁ (norm_nonneg ζ)]
  have hu : ‖ζ * (1 - z)‖ + ‖z‖ < 1 := by rw [norm_mul]; linarith
  have hΦ := summable_bcTriple a b c (by rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg ζ]) hu
  -- Summing over `(m, i)` first gives the Burchnall–Chaundy series.
  have h₁ : HasSum (fun s : ℕ => bcCoeff a b c s * (z * ζ) ^ s *
      regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (ζ * (1 - z) + z))
        (∑' p, bcTriple a b c z ζ p) :=
    hΦ.hasSum.prod_fiberwise fun s =>
      (hasSum_choose_mul_coeff_regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)
        hu).mul_left (bcCoeff a b c s * (z * ζ) ^ s)
  -- Summing over `i` and then over `s + m = n` gives the Cauchy product of `𝐅(z)` and `𝐅(ζ)`.
  set T : ℕ × ℕ → ℂ := fun q => bcCoeff a b c q.1 * (z * ζ) ^ q.1 * ((ζ * (1 - z)) ^ q.2 *
    ((ascPochhammer ℂ q.2).eval (a + q.1) * (ascPochhammer ℂ q.2).eval (b + q.1) / q.2 ! *
      regularizedGaussHGFun (a + q.1 + q.2) (b + q.1 + q.2) (c + 2 * q.1 + q.2) z))
  have hT : HasSum T (∑' p, bcTriple a b c z ζ p) := by
    refine ((Equiv.prodAssoc ℕ ℕ ℕ).hasSum_iff.2 hΦ.hasSum).prod_fiberwise fun q => ?_
    obtain ⟨s, m⟩ := q
    have hF := (hasSum_regularizedGaussHGFun (a + s + m) (b + s + m) (c + 2 * s + m) hz).mul_left
      (bcCoeff a b c s * (z * ζ) ^ s * ((ζ * (1 - z)) ^ m *
        ((ascPochhammer ℂ m).eval (a + s) * (ascPochhammer ℂ m).eval (b + s) / m !)))
    convert hF using 1
    · funext i
      simp only [Function.comp_apply, Equiv.prodAssoc_apply, bcTriple,
        choose_mul_coeff_regularizedGaussHGFunSeries]
      ring
    · simp only [T]
      ring
  have h₂ := (HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hT).sigma
    fun n => Finset.hasSum (antidiagonal n) T
  rw [show (fun n => ∑ q ∈ antidiagonal n, T q) = _ from
    funext (sum_antidiagonal_bcCoeff a b c hz ζ)] at h₂
  have h₃ := (hasSum_regularizedGaussHGFun a b c hζ).mul_right (regularizedGaussHGFun a b c z)
  have hval : ∑' p, bcTriple a b c z ζ p =
      regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ := by
    rw [h₂.unique h₃, mul_comm]
  rw [hval, show ζ * (1 - z) + z = z + ζ - z * ζ by ring] at h₁
  exact h₁

/-- The domain `{ξ | ‖ξ‖ < 1 ∧ ‖z + ξ - z ξ‖ < 1}` of the Burchnall–Chaundy expansion is convex. -/
private theorem convex_bcDomain (z : ℂ) : Convex ℝ {ξ : ℂ | ‖ξ‖ < 1 ∧ ‖z + ξ - z * ξ‖ < 1} := by
  convert (convex_ball (0 : ℂ) 1).inter
    ((convex_ball (-z) 1).linear_preimage (LinearMap.mulLeft ℝ (1 - z))) using 1
  ext ξ
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_ball, Set.mem_preimage,
    LinearMap.mulLeft_apply, dist_eq_norm, sub_neg_eq_add, sub_zero]
  rw [show (1 - z) * ξ + z = z + ξ - z * ξ by ring]

/-- The domain `{ξ | ‖ξ‖ < 1 ∧ ‖z + ξ - z ξ‖ < 1}` of the Burchnall–Chaundy expansion is open. -/
private theorem isOpen_bcDomain (z : ℂ) : IsOpen {ξ : ℂ | ‖ξ‖ < 1 ∧ ‖z + ξ - z * ξ‖ < 1} :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt (f := fun ξ : ℂ => ‖z + ξ - z * ξ‖) (by fun_prop) continuous_const)

/-- A bound for the terms of the Burchnall–Chaundy series by the majorant double series. -/
private theorem norm_bcTerm_le (a b c : ℂ) {z ξ : ℂ} {x y : ℝ} (hx : ‖z * ξ‖ ≤ x)
    (hy : ‖z + ξ - z * ξ‖ ≤ y) (hy₁ : y < 1) (s : ℕ) :
    ‖bcCoeff a b c s * (z * ξ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ξ - z * ξ)‖ ≤
      ‖bcCoeff a b c s‖ * x ^ s *
        ∑' j, ‖(regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)).coeff j‖ * y ^ j := by
  rw [norm_mul, norm_mul, norm_pow]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx s)
    (norm_nonneg _)) (norm_regularizedGaussHGFun_le_tsum _ _ _ hy hy₁) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (pow_nonneg ((norm_nonneg _).trans hx) _))

/-- The Burchnall–Chaundy series is holomorphic in `ζ` on its domain. -/
private theorem differentiableOn_tsum_bcTerm (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableOn ℂ (fun ξ => ∑' s : ℕ, bcCoeff a b c s * (z * ξ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ξ - z * ξ))
      {ξ : ℂ | ‖ξ‖ < 1 ∧ ‖z + ξ - z * ξ‖ < 1} := by
  intro ξ₀ hξ₀
  set y : ℝ := (1 + ‖z + ξ₀ - z * ξ₀‖) / 2
  have hy₁ : y < 1 := by simp only [y]; linarith [hξ₀.2]
  set V : Set ℂ := {ξ : ℂ | ‖ξ‖ < 1 ∧ ‖z + ξ - z * ξ‖ < 1} ∩ {ξ | ‖z + ξ - z * ξ‖ < y}
  have hW : IsOpen {ξ : ℂ | ‖z + ξ - z * ξ‖ < y} :=
    isOpen_lt (f := fun ξ : ℂ => ‖z + ξ - z * ξ‖) (by fun_prop) continuous_const
  have hVo : IsOpen V := (isOpen_bcDomain z).inter hW
  have hξ₀V : ξ₀ ∈ V := ⟨hξ₀, by simp only [Set.mem_ofPred_eq, y]; linarith [hξ₀.2]⟩
  have hzξ {ξ : ℂ} (hξ : ‖ξ‖ < 1) : ‖z * ξ‖ ≤ ‖z‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg z) hξ.le
  refine (DifferentiableOn.differentiableAt ?_ (hVo.mem_nhds hξ₀V)).differentiableWithinAt
  refine differentiableOn_tsum_of_summable_norm (summable_norm_bcCoeff_mul_tsum a b c
    (norm_nonneg z) hz (by simp only [y]; positivity) hy₁) (fun s => ?_) hVo
    fun s ξ hξ => norm_bcTerm_le a b c (hzξ hξ.1.1) (le_of_lt hξ.2) hy₁ s
  have hF : DifferentiableOn ℂ (fun ξ => regularizedGaussHGFun (a + s) (b + s) (c + 2 * s)
      (z + ξ - z * ξ)) V :=
    DifferentiableOn.regularizedGaussHGFun (differentiableOn_const _)
      (differentiableOn_const _) (differentiableOn_const _) (by fun_prop) fun ξ hξ => hξ.1.2
  exact ((differentiableOn_const _).mul
    (((differentiableOn_const _).mul differentiableOn_id).pow s)).mul hF

/-- **Burchnall–Chaundy product formula** (DLMF 15.16.3, regularized form): for `‖z‖ < 1`,
`‖ζ‖ < 1` and `‖z + ζ - z ζ‖ < 1`,
`𝐅(a, b; c; z) 𝐅(a, b; c; ζ) = ∑ₛ (a)ₛ (b)ₛ (c - a)ₛ (c - b)ₛ / (s! Γ(c + s)) (z ζ)ˢ`
`𝐅(a + s, b + s; c + 2s; z + ζ - z ζ)`, for all complex `a`, `b`, `c`. -/
theorem hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun (a b c : ℂ) {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum (fun s : ℕ => (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * Gamma (c + s)) * (z * ζ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  set U : Set ℂ := {ξ : ℂ | ‖ξ‖ < 1 ∧ ‖z + ξ - z * ξ‖ < 1}
  have hGa : AnalyticOnNhd ℂ
      (fun ξ => regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ξ) U :=
    fun ξ hξ => analyticAt_const.mul (analyticAt_regularizedGaussHGFun a b c hξ.1)
  -- Near `0` both sides agree by `hasSum_bcCoeff_of_norm_add_norm_mul_lt_one`; the identity
  -- theorem on the convex set `U` gives the rest.
  have heq : (fun ξ => ∑' s : ℕ, bcCoeff a b c s * (z * ξ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ξ - z * ξ)) =ᶠ[𝓝 0]
      fun ξ => regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ξ := by
    have hS : IsOpen {ξ : ℂ | ‖z‖ + ‖ξ‖ * ‖1 - z‖ < 1} :=
      isOpen_lt (f := fun ξ : ℂ => ‖z‖ + ‖ξ‖ * ‖1 - z‖) (by fun_prop) continuous_const
    filter_upwards [hS.mem_nhds (by simpa using hz)] with ξ hξ
    exact (hasSum_bcCoeff_of_norm_add_norm_mul_lt_one a b c hξ).tsum_eq
  have hEq := ((differentiableOn_tsum_bcTerm a b c hz).analyticOnNhd
    (isOpen_bcDomain z)).eqOn_of_preconnected_of_eventuallyEq hGa (convex_bcDomain z).isPreconnected
      (by simpa [U] using hz) heq
  have hzζ : ‖z * ζ‖ < 1 := (norm_mul_le _ _).trans_lt (by nlinarith [norm_nonneg z, norm_nonneg ζ])
  have hs := Summable.of_norm ((summable_norm_bcCoeff_mul_tsum a b c (norm_nonneg _) hzζ
    (norm_nonneg _) hw).of_nonneg_of_le (fun s => norm_nonneg _)
      (norm_bcTerm_le a b c le_rfl le_rfl hw))
  have h := hs.hasSum
  rw [show ∑' s : ℕ, bcCoeff a b c s * (z * ζ) ^ s *
      regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ) = _ from
    hEq (show ζ ∈ U from ⟨hζ, hw⟩)] at h
  simpa only [bcCoeff] using h

/-- **Burchnall–Chaundy product formula** (DLMF 15.16.3): for `c ∉ {0, -1, -2, …}`, `‖z‖ < 1`,
`‖ζ‖ < 1` and `‖z + ζ - z ζ‖ < 1`,
`F(a, b; c; z) F(a, b; c; ζ) = ∑ₛ (a)ₛ (b)ₛ (c - a)ₛ (c - b)ₛ / ((c)ₛ (c)₂ₛ s!) (z ζ)ˢ`
`F(a + s, b + s; c + 2s; z + ζ - z ζ)`. -/
theorem hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric {a b c z ζ : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum (fun s : ℕ => (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          ((ascPochhammer ℂ s).eval c * (ascPochhammer ℂ (2 * s)).eval c * s !) * (z * ζ) ^ s *
        ordinaryHypergeometric (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (ordinaryHypergeometric a b c z * ordinaryHypergeometric a b c ζ) := by
  have hF {α β γ w : ℂ} (hγ : ∀ k : ℕ, γ ≠ -k) :
      ordinaryHypergeometric α β γ w = Gamma γ * regularizedGaussHGFun α β γ w := by
    rw [← ordinaryHypergeometric_div_Gamma_eq hγ, mul_div_cancel₀ _ (Gamma_ne_zero hγ)]
  have hc' (k : ℕ) : ∀ m : ℕ, c + k ≠ -m := fun m h =>
    hc (m + k) (by push_cast; linear_combination h)
  have hΓ (k : ℕ) := Gamma_add_natCast_eq_ascPochhammer_eval_mul hc k
  have hp (k : ℕ) : (ascPochhammer ℂ k).eval c ≠ 0 := fun h0 =>
    Gamma_ne_zero (hc' k) (by rw [hΓ k, h0, zero_mul])
  rw [hF hc, hF hc]
  convert (hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun a b c hz hζ hw).mul_left
    (Gamma c ^ 2) using 1
  · funext s
    rw [show c + 2 * (s : ℂ) = c + ((2 * s : ℕ) : ℂ) by push_cast; ring, hF (hc' (2 * s)),
      hΓ (2 * s), hΓ s]
    have := hp s
    have := hp (2 * s)
    have := Gamma_ne_zero hc
    field_simp
  · ring

end BurchnallChaundy

end Complex

end
