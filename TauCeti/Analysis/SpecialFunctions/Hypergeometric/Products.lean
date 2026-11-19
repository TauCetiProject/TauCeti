/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral

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

open Filter Set
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
  have h₅ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a b c hz
  have h₇ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a b (c + 1) hz
  have hc2 : c + 1 + 1 = c + 2 := by ring
  rw [hc2] at h₇
  have h₉ := regularizedGaussHGFun_eq_sub_mul_add_mul a (b + 1) c hz
  linear_combination -(c - a) * h₂ - (c - a) * (c - b) * h₇ + c * h₅ + c * h₉

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

end Complex

end
