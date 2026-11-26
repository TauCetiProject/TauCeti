/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# The hypergeometric inverse germ of the roots-of-unity cover

For an integer `N ≥ 2`, let `F_N : 𝔻 → ℂ \ μ_N` be the holomorphic universal covering map of the
complement of the `N`th roots of unity with `F_N 0 = 0`. Calegari, Dimitrov and Tang show that its
local inverse at `0` is, up to the scalar factor `F_N' 0`, the ratio of Gauss hypergeometric series
`J_N(u) = u ₂F₁(a₊, a₊; 2a₊; u ^ N) / ₂F₁(a₋, a₋; 2a₋; u ^ N)`, where `a± = (N ± 1) / (2N)`. The
radial limit of this ratio at `u = 1` evaluates the conformal radius `|F_N' 0|` in Gamma functions.

This file defines `TauCeti.inverseRatio N` as this scalar expression in the native
`ordinaryHypergeometric` series and proves that it is an analytic germ at `0`, normalized like a
local inverse with derivative `1`, and equivariant under rotation by `N`th roots of unity. It is
only the germ of the convergent series: off the unit disc `‖u ^ N‖ < 1` the native series takes
junk values, and the expression is not the analytic continuation of the inverse.

The Taylor expansion is `J_N(u) = u + u ^ (N + 1) / (2N) + O(u ^ (2N + 1))`: the ratio of the two
series is `1 + (a₊ - a₋) x / 2 + O(x²)` in `x = u ^ N`, and `a₊ - a₋ = 1 / N`. Thus `J_N` differs
from the identity germ, which already shows at the third derivative of `J_2`.

The ratio comes from two hypergeometric solutions of linear equations. After the substitution
`x = u ^ N`, the local inverse is a quotient of solutions of the descended equation
`x (x - 1)² y'' + (1 - 1/N) (x - 1)² y' + (1/4 + (x - 1) / (4N²)) y = 0`, whose exponents are
`0, 1/N` at `x = 0` and `1/2, 1/2` at `x = 1`. Writing `y = g F` with `g` a branch of
`√(1 - x) x^ρ`, `ρ ∈ {0, 1/N}`, turns the descended operator into `g (1 - x)` times Gauss's
operator with `a = b = ρ + (1 - 1/N) / 2` and `c = 2a`, so that
`√(1 - x) x^(1/N) ₂F₁(a₊, a₊; 2a₊; x)` and `√(1 - x) ₂F₁(a₋, a₋; 2a₋; x)` are solutions. In the
variable `u`, the solutions `η₁(u) = √(1 - u ^ N) u ₂F₁(a₊, a₊; 2a₊; u ^ N)` and
`η₂(u) = √(1 - u ^ N) ₂F₁(a₋, a₋; 2a₋; u ^ N)` of the inverse-cover equation
`4 (u ^ N - 1)² y'' + ((N² - 1) u ^ (N - 2) + u ^ (2N - 2)) y = 0` need no branch of `x^(1/N)`.
They have the initial jets `(0, 1)` and `(1, 0)`, Wronskian `-1` on the unit disc, and quotient
`η₁ / η₂ = J_N`.

## Main definitions

* `TauCeti.inverseRatio N u`: the hypergeometric ratio `J_N(u)`.
* `TauCeti.hypergeometricRatio N x`: the ratio `ρ_N(x)` of the two series, so that
  `J_N(u) = u ρ_N(u ^ N)`.
* `TauCeti.inverseRatioNum N u`, `TauCeti.inverseRatioDen N u`: the solutions `η₁(u)`, `η₂(u)` of
  the inverse-cover equation, with `η₁ / η₂ = J_N`.

## Main results

* `TauCeti.inverseRatio_zero`: `J_N(0) = 0`.
* `TauCeti.inverseRatio_mul_of_pow_eq_one`: `J_N(ζ u) = ζ J_N(u)` whenever `ζ ^ N = 1`.
* `TauCeti.analyticAt_inverseRatio`: `J_N` is analytic wherever `‖u ^ N‖ < 1` and the denominator
  series does not vanish; `TauCeti.analyticAt_inverseRatio_zero` gives analyticity at `0`.
* `TauCeti.deriv_inverseRatio_zero`: `J_N'(0) = 1`.
* `TauCeti.iteratedDeriv_inverseRatio_zero_eq_zero`: the derivatives of orders `2, …, N` vanish
  at `0`.
* `TauCeti.iteratedDeriv_succ_inverseRatio_zero`: the derivative of order `N + 1` at `0` is
  `(N + 1)! / (2N)`; for instance `J_2'''(0) = 3 / 2`.
* `TauCeti.descendedInverseEquation_plus_of_hasDerivAt`,
  `TauCeti.descendedInverseEquation_minus_of_hasDerivAt`: on any branch, `√(1 - x) x^(1/N)` times
  `₂F₁(a₊, a₊; 2a₊; x)` and `√(1 - x)` times `₂F₁(a₋, a₋; 2a₋; x)` solve the descended equation;
  `TauCeti.descendedInverseEquation_plus` and `TauCeti.descendedInverseEquation_minus` are the
  principal branches.
* `TauCeti.inverseRatioNum_inverseCoverEquation`, `TauCeti.inverseRatioDen_inverseCoverEquation`:
  `η₁` and `η₂` solve the inverse-cover equation on the unit disc.
* `TauCeti.inverseRatioNum_div_inverseRatioDen`: `η₁ / η₂ = J_N`.
* `TauCeti.inverseRatioNum_mul_deriv_inverseRatioDen_sub`: the Wronskian `η₁ η₂' - η₁' η₂` is `-1`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.16 and its proof, equations (5.1.17)–(5.1.19),
  pp. 671–672.
-/

public section

namespace TauCeti

open scoped Nat

/-- The hypergeometric ratio `J_N(u) = u ₂F₁(a₊, a₊; 2a₊; u ^ N) / ₂F₁(a₋, a₋; 2a₋; u ^ N)` with
`a± = (N ± 1) / (2N)`. Calegari, Dimitrov and Tang show that for `N ≥ 2` its germ at `0` is, up to
a scalar factor, the local inverse of the universal covering map `𝔻 → ℂ \ μ_N` sending `0` to `0`.
It is the scalar expression in the native series, so it carries meaning only as a germ where
`‖u ^ N‖ < 1`. -/
noncomputable def inverseRatio (N : ℕ) (u : ℂ) : ℂ :=
  u * ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N)))
      (u ^ N) /
    ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N)))
      (u ^ N)

/-- The defining formula of `TauCeti.inverseRatio`. -/
theorem inverseRatio_def (N : ℕ) (u : ℂ) :
    inverseRatio N u =
      u * ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N))
          (2 * (((N : ℂ) + 1) / (2 * N))) (u ^ N) /
        ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
          (2 * (((N : ℂ) - 1) / (2 * N))) (u ^ N) := (rfl)

/-- The ratio `ρ_N(x) = ₂F₁(a₊, a₊; 2a₊; x) / ₂F₁(a₋, a₋; 2a₋; x)` of the two series in the
variable `x = u ^ N`, with `a± = (N ± 1) / (2N)`, so that `J_N(u) = u ρ_N(u ^ N)`. -/
noncomputable def hypergeometricRatio (N : ℕ) (x : ℂ) : ℂ :=
  ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N))) x /
    ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N)))
      x

/-- The defining formula of `TauCeti.hypergeometricRatio`. -/
theorem hypergeometricRatio_def (N : ℕ) (x : ℂ) :
    hypergeometricRatio N x =
      ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N))
          (2 * (((N : ℂ) + 1) / (2 * N))) x /
        ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
          (2 * (((N : ℂ) - 1) / (2 * N))) x := (rfl)

/-- `J_N(u) = u ρ_N(u ^ N)`. -/
theorem inverseRatio_eq_mul_hypergeometricRatio (N : ℕ) (u : ℂ) :
    inverseRatio N u = u * hypergeometricRatio N (u ^ N) := by
  rw [inverseRatio_def, hypergeometricRatio_def, mul_div_assoc]

/-- `ρ_N(0) = 1`. -/
@[simp]
theorem hypergeometricRatio_zero (N : ℕ) : hypergeometricRatio N 0 = 1 := by
  simp [hypergeometricRatio_def]

/-- Analyticity of `ρ_N` inside the unit disc, away from zeros of its denominator. -/
theorem analyticAt_hypergeometricRatio (N : ℕ) {x : ℂ} (hx : ‖x‖ < 1)
    (h : ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
      (2 * (((N : ℂ) - 1) / (2 * N))) x ≠ 0) :
    AnalyticAt ℂ (hypergeometricRatio N) x := by
  have hx' : x ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hx
  exact (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ x hx').div
    (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ x hx') h

/-- `ρ_N` is an analytic germ at `0`. -/
theorem analyticAt_hypergeometricRatio_zero (N : ℕ) :
    AnalyticAt ℂ (hypergeometricRatio N) 0 :=
  analyticAt_hypergeometricRatio N (by simp) (by simp)

/-- By the quotient rule, `ρ_N'(0) = a₊ a₊ / (2a₊) - a₋ a₋ / (2a₋) = a₊ / 2 - a₋ / 2 = 1 / (2N)`,
where `a a / (2a) = a / 2` also in the totalized case `a = 0`. -/
theorem deriv_hypergeometricRatio_zero (N : ℕ) :
    deriv (hypergeometricRatio N) 0 = 1 / (2 * N) := by
  have hnum := (analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) + 1) / (2 * N))
    (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N))) 0 (by simp)).differentiableAt
  have hden := (analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) - 1) / (2 * N))
    (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N))) 0 (by simp)).differentiableAt
  have hhalf (a : ℂ) : a * a / (2 * a) = a / 2 := by
    rw [div_mul_eq_div_div_swap, mul_self_div_self]
  rw [funext (hypergeometricRatio_def N), deriv_fun_div hnum hden (by simp)]
  simp only [deriv_ordinaryHypergeometric_zero, ordinaryHypergeometric_zero, hhalf]
  rcases eq_or_ne (N : ℂ) 0 with hN | hN
  · simp [hN]
  · field_simp
    ring

/-- `J_N(0) = 0`. -/
@[simp]
theorem inverseRatio_zero (N : ℕ) : inverseRatio N 0 = 0 := by
  simp [inverseRatio_def]

/-- **Rotation equivariance.** `J_N(ζ u) = ζ J_N(u)` for every `N`th root of unity `ζ`, since
`J_N(u) / u` depends only on `u ^ N`. -/
theorem inverseRatio_mul_of_pow_eq_one {N : ℕ} {ζ : ℂ} (hζ : ζ ^ N = 1) (u : ℂ) :
    inverseRatio N (ζ * u) = ζ * inverseRatio N u := by
  rw [inverseRatio_eq_mul_hypergeometricRatio, inverseRatio_eq_mul_hypergeometricRatio, mul_pow, hζ,
    one_mul, mul_assoc]

/-- `J_N` is analytic at every `u` with `‖u ^ N‖ < 1` at which the denominator series
`₂F₁(a₋, a₋; 2a₋; u ^ N)` does not vanish. -/
theorem analyticAt_inverseRatio {N : ℕ} {u : ℂ} (hu : ‖u ^ N‖ < 1)
    (h : ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
      (2 * (((N : ℂ) - 1) / (2 * N))) (u ^ N) ≠ 0) :
    AnalyticAt ℂ (inverseRatio N) u := by
  have hr : AnalyticAt ℂ (fun v : ℂ ↦ hypergeometricRatio N (v ^ N)) u :=
    (analyticAt_hypergeometricRatio N hu h).comp_of_eq (by fun_prop) rfl
  rw [funext (inverseRatio_eq_mul_hypergeometricRatio N)]
  fun_prop

/-- `J_N` is an analytic germ at `0`. -/
theorem analyticAt_inverseRatio_zero (N : ℕ) : AnalyticAt ℂ (inverseRatio N) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [funext (inverseRatio_eq_mul_hypergeometricRatio 0)]
    simp only [pow_zero]
    fun_prop
  · exact analyticAt_inverseRatio (by simp [hN]) (by simp [hN])

/-- For `N ≠ 0`, `J_N(u) = u + u ^ (N + 1) q(u)` for a function `q` analytic at `0` with
`q(0) = 1 / (2N)`; namely `q(u)` is the difference quotient of `ρ_N` at `0` evaluated at
`u ^ N`. -/
private theorem exists_inverseRatio_eq_add_pow_mul {N : ℕ} (hN : N ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ q 0 = 1 / (2 * N) ∧
      ∀ u, inverseRatio N u = u + u ^ (N + 1) * q u := by
  refine ⟨fun u ↦ dslope (hypergeometricRatio N) 0 (u ^ N), ?_, ?_, fun u ↦ ?_⟩
  · refine AnalyticAt.comp (g := dslope (hypergeometricRatio N) 0) ?_ (analyticAt_id.pow N)
    simpa [hN] using (analyticAt_hypergeometricRatio_zero N).dslope 0
  · simp [hN, dslope_same, deriv_hypergeometricRatio_zero]
  · have h := sub_smul_dslope (hypergeometricRatio N) 0 (u ^ N)
    rw [sub_zero, smul_eq_mul, hypergeometricRatio_zero] at h
    rw [inverseRatio_eq_mul_hypergeometricRatio, pow_succ', mul_assoc, h]
    ring

/-- The iterated derivatives of `J_N` at `0` agree with those of `u ↦ u + u ^ (N + 1) q(u)`:
`(if k = 1 then 1 else 0) + k.descFactorial (N + 1) q⁽ᵏ⁻ᴺ⁻¹⁾(0)`. -/
private theorem iteratedDeriv_inverseRatio_zero_eq {N : ℕ} {q : ℂ → ℂ} (hq : AnalyticAt ℂ q 0)
    (hJ : ∀ u, inverseRatio N u = u + u ^ (N + 1) * q u) (k : ℕ) :
    iteratedDeriv k (inverseRatio N) 0 =
      (if k = 1 then 1 else 0) + k.descFactorial (N + 1) * iteratedDeriv (k - (N + 1)) q 0 := by
  have hpow := iteratedDeriv_pow_sub_smul (a := (0 : ℂ)) k (N + 1) hq.contDiffAt
  simp only [sub_zero, smul_eq_mul, nsmul_eq_mul] at hpow
  rw [funext hJ, iteratedDeriv_fun_add (f := fun u ↦ u) (g := fun u ↦ u ^ (N + 1) * q u)
    contDiffAt_id ((contDiffAt_id.pow _).mul hq.contDiffAt), iteratedDeriv_fun_id_zero, hpow]

/-- **Normalization.** `J_N'(0) = 1`, as for the local inverse of a covering map normalized by a
positive derivative, up to that scalar. -/
@[simp]
theorem deriv_inverseRatio_zero (N : ℕ) : deriv (inverseRatio N) 0 = 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h1 : ₂F₁ (0 : ℂ) 0 0 (1 : ℂ) = 1 := by
      simpa using ordinaryHypergeometric_neg_nat_eq_sum 0 (0 : ℂ) 0 (1 : ℂ)
    have hfun : inverseRatio 0 = id := by
      funext u
      simp [inverseRatio_def, h1]
    simp [hfun]
  · obtain ⟨q, hq, -, hJ⟩ := exists_inverseRatio_eq_add_pow_mul hN
    rw [← iteratedDeriv_one, iteratedDeriv_inverseRatio_zero_eq hq hJ,
      Nat.descFactorial_of_lt (by omega)]
    simp

/-- The derivatives of `J_N` of orders `2, …, N` vanish at `0`: the Taylor expansion of `J_N`
at `0` has no terms between `u` and `u ^ (N + 1)`. -/
theorem iteratedDeriv_inverseRatio_zero_eq_zero {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) :
    iteratedDeriv k (inverseRatio N) 0 = 0 := by
  obtain ⟨q, hq, -, hJ⟩ := exists_inverseRatio_eq_add_pow_mul (N := N) (by omega)
  rw [iteratedDeriv_inverseRatio_zero_eq hq hJ, Nat.descFactorial_of_lt (by omega)]
  simp [show k ≠ 1 by omega]

/-- The derivative of `J_N` of order `N + 1` at `0` is `(N + 1)! / (2N)`: the first correction
to the identity germ is `u ^ (N + 1) / (2N)`. -/
theorem iteratedDeriv_succ_inverseRatio_zero {N : ℕ} (hN : N ≠ 0) :
    iteratedDeriv (N + 1) (inverseRatio N) 0 = (N + 1)! / (2 * N) := by
  obtain ⟨q, hq, hq0, hJ⟩ := exists_inverseRatio_eq_add_pow_mul hN
  rw [iteratedDeriv_inverseRatio_zero_eq hq hJ, Nat.sub_self, iteratedDeriv_zero, hq0,
    Nat.descFactorial_self]
  simp [hN, div_eq_mul_inv]

/-- `J_2'''(0) = 3 / 2`, matching the cubic Taylor coefficient `1 / 4` of
`J_2(u) = u + u ^ 3 / 4 + O(u ^ 5)`; the identity germ would give `0`. -/
example : iteratedDeriv 3 (inverseRatio 2) 0 = 3 / 2 := by
  rw [iteratedDeriv_succ_inverseRatio_zero two_ne_zero]
  norm_num [Nat.factorial]

section Solutions

open Complex Filter
open scoped Topology

/-! ### The descended inverse equation -/

/-- The operator identity behind the two hypergeometric solutions: if `g' = g ℓ` near `x` with
`ℓ(w) = ρ / w - 1 / (2 (1 - w))` and `ρ ∈ {0, 1 / N}`, then the descended operator applied to
`g F` at `x` is `g(x) (1 - x)` times Gauss's operator with `a = b = ρ + (1 - 1/N) / 2` and
`c = 2a` applied to `F`. -/
private theorem descended_residual_eq {N : ℕ} (hN : (N : ℂ) ≠ 0) {ρ : ℂ} (hρ : ρ = 0 ∨ ρ = 1 / N)
    {g F : ℂ → ℂ} {x : ℂ} (hx : x ≠ 0 ∨ ρ = 0) (hx1 : x ≠ 1)
    (hg : ∀ᶠ w in 𝓝 x, HasDerivAt g (g w * (ρ / w - 1 / (2 * (1 - w)))) w)
    (hF : AnalyticAt ℂ F x) :
    x * (x - 1) ^ 2 * deriv (deriv fun w ↦ g w * F w) x +
        (1 - 1 / N) * (x - 1) ^ 2 * deriv (fun w ↦ g w * F w) x +
        (1 / 4 + (x - 1) / (4 * N ^ 2)) * (g x * F x) =
      g x * (1 - x) * (x * (1 - x) * deriv (deriv F) x +
        (2 * (ρ + (1 - 1 / N) / 2) - (2 * (ρ + (1 - 1 / N) / 2) + 1) * x) * deriv F x -
        (ρ + (1 - 1 / N) / 2) * (ρ + (1 - 1 / N) / 2) * F x) := by
  have hx1' : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  -- The logarithmic derivative `ℓ` of `g` and its derivative at `x`.
  have hℓd : HasDerivAt (fun w ↦ ρ / w - 1 / (2 * (1 - w)))
      (-ρ / x ^ 2 - 1 / (2 * (1 - x) ^ 2)) x := by
    have h2 : HasDerivAt (fun w : ℂ ↦ 1 / (2 * (1 - w))) (1 / (2 * (1 - x) ^ 2)) x := by
      have h := (hasDerivAt_const x (1 : ℂ)).fun_div
        (((hasDerivAt_id' x).const_sub 1).const_mul 2) (mul_ne_zero two_ne_zero hx1')
      exact h.congr_deriv (by field_simp; ring)
    rcases hx with hx | rfl
    · exact (((hasDerivAt_id x).inv hx).const_mul ρ).sub h2 |>.congr_deriv (by simp; ring)
    · simpa using h2.const_sub 0
  have hgd2 := hasDerivAt_deriv_of_eventually_hasDerivAt_mul hg hℓd
  -- Expand the first and second derivatives of `g F` by the product rule.
  have h1 := TauCeti.hasDerivAt_deriv_mul_comp (p := g) («φ» := id) (F := F) (z := x)
    (hg.mono fun w hw ↦ hw.differentiableAt) (Eventually.of_forall fun _ ↦ differentiableAt_id)
    (hF.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt) hgd2.differentiableAt
    (by simp) hF.deriv.differentiableAt
  have h0 := TauCeti.deriv_mul_comp_eventuallyEq (p := g) («φ» := id) (F := F) (z := x)
    (hg.mono fun w hw ↦ hw.differentiableAt) (Eventually.of_forall fun _ ↦ differentiableAt_id)
    (hF.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
  simp only [deriv_id', deriv_const', deriv_id, id_eq] at h1 h0
  rw [h1.deriv, h0.eq_of_nhds, hgd2.deriv, hg.self_of_nhds.deriv]
  generalize g x = G
  generalize deriv (deriv F) x = F2
  generalize deriv F x = F1
  generalize F x = F0
  -- Both indicial exponents make the operators proportional.
  rcases hρ with rfl | rfl
  · field_simp
    ring
  · rcases hx with hx | hx
    · field_simp
      ring
    · simp [hN] at hx

/-- `c = 2a₊ = (N + 1) / N` is not a nonpositive integer. -/
private theorem natCast_ne_neg_two_mul_plus {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    (k : ℂ) ≠ -(2 * (((N : ℂ) + 1) / (2 * N))) := by
  intro h
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp at h
  have h' : ((k * N + N + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
  exact absurd (Nat.cast_eq_zero.mp h') (by omega)

/-- `c = 2a₋ = (N - 1) / N` is not a nonpositive integer when `N ≥ 2`. -/
private theorem natCast_ne_neg_two_mul_minus {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    (k : ℂ) ≠ -(2 * (((N : ℂ) - 1) / (2 * N))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  intro h
  push_cast at h
  have hM : (M : ℂ) + 2 ≠ 0 := by norm_cast
  field_simp at h
  have h' : ((k * (M + 2) + M + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
  exact absurd (Nat.cast_eq_zero.mp h') (by omega)

/-- **The first hypergeometric solution, on any branch.** Let `N ≠ 0` and `0 < ‖x‖ < 1`, and let
`g` be a branch of `√(1 - x) x^(1/N)` near `x`, in the sense that
`g' = g (1 / (N w) - 1 / (2 (1 - w)))` there. Then `y = g ₂F₁(a₊, a₊; 2a₊; ·)`, with
`a₊ = (N + 1) / (2N)`, solves the descended inverse equation
`x (x - 1)² y'' + (1 - 1/N) (x - 1)² y' + (1/4 + (x - 1) / (4N²)) y = 0` at `x`. -/
theorem descendedInverseEquation_plus_of_hasDerivAt {N : ℕ} (hN : N ≠ 0) {g : ℂ → ℂ} {x : ℂ}
    (hx₀ : x ≠ 0) (hx : ‖x‖ < 1)
    (hg : ∀ᶠ w in 𝓝 x, HasDerivAt g (g w * (1 / (N * w) - 1 / (2 * (1 - w)))) w) :
    let y : ℂ → ℂ := fun w ↦ g w * ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N))
      (2 * (((N : ℂ) + 1) / (2 * N))) w
    x * (x - 1) ^ 2 * deriv (deriv y) x + (1 - 1 / N) * (x - 1) ^ 2 * deriv y x +
      (1 / 4 + (x - 1) / (4 * N ^ 2)) * y x = 0 := by
  intro y
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hx₁ : x ≠ 1 := fun h ↦ by simp [h] at hx
  have h := descended_residual_eq (F := ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N))
    (2 * (((N : ℂ) + 1) / (2 * N)))) hN' (Or.inr rfl) (Or.inl hx₀) hx₁
    (hg.mono fun w hw ↦ hw.congr_deriv (by ring))
    (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ x (mem_ball_zero_iff.mpr hx))
  have ha : 1 / (N : ℂ) + (1 - 1 / N) / 2 = ((N : ℂ) + 1) / (2 * N) := by
    field_simp
    ring
  rw [ha] at h
  rw [h, ← mul_zero (g x * (1 - x)), ← ordinaryHypergeometric_gaussEquation_of_norm_lt_one _ _ _
    (natCast_ne_neg_two_mul_plus hN) hx]
  ring

/-- **The second hypergeometric solution, on any branch.** Let `N ≥ 2` and `‖x‖ < 1`, and let `g`
be a branch of `√(1 - x)` near `x`, in the sense that `g' = -g / (2 (1 - w))` there. Then
`y = g ₂F₁(a₋, a₋; 2a₋; ·)`, with `a₋ = (N - 1) / (2N)`, solves the descended inverse equation
`x (x - 1)² y'' + (1 - 1/N) (x - 1)² y' + (1/4 + (x - 1) / (4N²)) y = 0` at `x`. -/
theorem descendedInverseEquation_minus_of_hasDerivAt {N : ℕ} (hN : 2 ≤ N) {g : ℂ → ℂ} {x : ℂ}
    (hx : ‖x‖ < 1) (hg : ∀ᶠ w in 𝓝 x, HasDerivAt g (-g w / (2 * (1 - w))) w) :
    let y : ℂ → ℂ := fun w ↦ g w * ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
      (2 * (((N : ℂ) - 1) / (2 * N))) w
    x * (x - 1) ^ 2 * deriv (deriv y) x + (1 - 1 / N) * (x - 1) ^ 2 * deriv y x +
      (1 / 4 + (x - 1) / (4 * N ^ 2)) * y x = 0 := by
  intro y
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hx₁ : x ≠ 1 := fun h ↦ by simp [h] at hx
  have h := descended_residual_eq (F := ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
    (2 * (((N : ℂ) - 1) / (2 * N)))) hN' (Or.inl rfl) (Or.inr rfl) hx₁
    (hg.mono fun w hw ↦ hw.congr_deriv (by ring))
    (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ x (mem_ball_zero_iff.mpr hx))
  have ha : 0 + (1 - 1 / (N : ℂ)) / 2 = ((N : ℂ) - 1) / (2 * N) := by
    field_simp
    ring
  rw [ha] at h
  rw [h, ← mul_zero (g x * (1 - x)), ← ordinaryHypergeometric_gaussEquation_of_norm_lt_one _ _ _
    (natCast_ne_neg_two_mul_minus hN) hx]
  ring

/-- `1 - x` lies in the slit plane inside the unit disc. -/
private theorem one_sub_mem_slitPlane {x : ℂ} (hx : ‖x‖ < 1) : 1 - x ∈ slitPlane := by
  simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -x) (by simpa using hx)

/-- The principal branch of `√(1 - w) w^(1/N)` has logarithmic derivative
`1 / (N w) - 1 / (2 (1 - w))` on the slit unit disc. -/
private theorem hasDerivAt_sqrt_one_sub_mul_cpow {N : ℕ} {w : ℂ} (hw : w ∈ slitPlane)
    (hw₁ : 1 - w ∈ slitPlane) :
    HasDerivAt (fun v : ℂ ↦ (1 - v) ^ (1 / 2 : ℂ) * v ^ (1 / (N : ℂ)))
      ((1 - w) ^ (1 / 2 : ℂ) * w ^ (1 / (N : ℂ)) * (1 / (N * w) - 1 / (2 * (1 - w)))) w := by
  have hw₀ : w ≠ 0 := slitPlane_ne_zero hw
  have hw₁₀ : 1 - w ≠ 0 := slitPlane_ne_zero hw₁
  refine ((((hasDerivAt_id' w).const_sub 1).cpow_const hw₁).mul
    ((hasDerivAt_id' w).cpow_const hw)).congr_deriv ?_
  rw [cpow_sub _ _ hw₀, cpow_sub _ _ hw₁₀, cpow_one, cpow_one]
  field_simp
  ring

/-- **The first hypergeometric solution.** For `N ≠ 0` and `x` in the unit disc slit along
`(-1, 0]`, the principal branch `y(x) = √(1 - x) x^(1/N) ₂F₁(a₊, a₊; 2a₊; x)`, with
`a₊ = (N + 1) / (2N)`, solves the descended inverse equation
`x (x - 1)² y'' + (1 - 1/N) (x - 1)² y' + (1/4 + (x - 1) / (4N²)) y = 0` at `x`. -/
theorem descendedInverseEquation_plus {N : ℕ} (hN : N ≠ 0) {x : ℂ} (hx₀ : x ∈ slitPlane)
    (hx : ‖x‖ < 1) :
    let y : ℂ → ℂ := fun w ↦ (1 - w) ^ (1 / 2 : ℂ) * w ^ (1 / (N : ℂ)) *
      ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N))) w
    x * (x - 1) ^ 2 * deriv (deriv y) x + (1 - 1 / N) * (x - 1) ^ 2 * deriv y x +
      (1 / 4 + (x - 1) / (4 * N ^ 2)) * y x = 0 := by
  have hev : ∀ᶠ w in 𝓝 x, w ∈ slitPlane ∧ 1 - w ∈ slitPlane :=
    Filter.Eventually.and (isOpen_slitPlane.mem_nhds hx₀) <|
      ((continuous_const.sub continuous_id).continuousAt (x := x)).eventually_mem
        (isOpen_slitPlane.mem_nhds (one_sub_mem_slitPlane hx))
  exact descendedInverseEquation_plus_of_hasDerivAt hN (slitPlane_ne_zero hx₀) hx
    (hev.mono fun w hw ↦ hasDerivAt_sqrt_one_sub_mul_cpow hw.1 hw.2)

/-- **The second hypergeometric solution.** For `N ≥ 2` and `‖x‖ < 1`, the principal branch
`y(x) = √(1 - x) ₂F₁(a₋, a₋; 2a₋; x)`, with `a₋ = (N - 1) / (2N)`, solves the descended inverse
equation `x (x - 1)² y'' + (1 - 1/N) (x - 1)² y' + (1/4 + (x - 1) / (4N²)) y = 0` at `x`. -/
theorem descendedInverseEquation_minus {N : ℕ} (hN : 2 ≤ N) {x : ℂ} (hx : ‖x‖ < 1) :
    let y : ℂ → ℂ := fun w ↦ (1 - w) ^ (1 / 2 : ℂ) *
      ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N))) w
    x * (x - 1) ^ 2 * deriv (deriv y) x + (1 - 1 / N) * (x - 1) ^ 2 * deriv y x +
      (1 / 4 + (x - 1) / (4 * N ^ 2)) * y x = 0 := by
  have hev : ∀ᶠ w in 𝓝 x, 1 - w ∈ slitPlane :=
    ((continuous_const.sub continuous_id).continuousAt (x := x)).eventually_mem
      (isOpen_slitPlane.mem_nhds (one_sub_mem_slitPlane hx))
  refine descendedInverseEquation_minus_of_hasDerivAt hN hx (hev.mono fun w hw ↦ ?_)
  have hw₀ : 1 - w ≠ 0 := slitPlane_ne_zero hw
  refine (((hasDerivAt_id' w).const_sub 1).cpow_const hw).congr_deriv ?_
  rw [cpow_sub _ _ hw₀, cpow_one]
  field_simp

/-! ### The two solutions of the inverse-cover equation -/

/-- The first solution `η₁(u) = √(1 - u ^ N) u ₂F₁(a₊, a₊; 2a₊; u ^ N)`, with
`a₊ = (N + 1) / (2N)`, of the inverse-cover equation
`4 (u ^ N - 1)² y'' + ((N² - 1) u ^ (N - 2) + u ^ (2N - 2)) y = 0`. Under `x = u ^ N` it is the
first hypergeometric solution `√(1 - x) x^(1/N) ₂F₁(a₊, a₊; 2a₊; x)` of the descended equation, on
the branch of `x^(1/N)` equal to `u`, and the numerator of `TauCeti.inverseRatio N` up to the
common factor `√(1 - u ^ N)`. It uses the native series, so it carries meaning only where
`‖u ^ N‖ < 1`. -/
noncomputable def inverseRatioNum (N : ℕ) (u : ℂ) : ℂ :=
  (1 - u ^ N) ^ (1 / 2 : ℂ) * u *
    ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N)))
      (u ^ N)

/-- The second solution `η₂(u) = √(1 - u ^ N) ₂F₁(a₋, a₋; 2a₋; u ^ N)`, with
`a₋ = (N - 1) / (2N)`, of the inverse-cover equation
`4 (u ^ N - 1)² y'' + ((N² - 1) u ^ (N - 2) + u ^ (2N - 2)) y = 0`. It is the second
hypergeometric solution `√(1 - x) ₂F₁(a₋, a₋; 2a₋; x)` of the descended equation at `x = u ^ N`,
and the denominator of `TauCeti.inverseRatio N` up to the common factor `√(1 - u ^ N)`. It uses
the native series, so it carries meaning only where `‖u ^ N‖ < 1`. -/
noncomputable def inverseRatioDen (N : ℕ) (u : ℂ) : ℂ :=
  (1 - u ^ N) ^ (1 / 2 : ℂ) *
    ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N)))
      (u ^ N)

/-- The defining formula of `TauCeti.inverseRatioNum`. -/
theorem inverseRatioNum_def (N : ℕ) (u : ℂ) :
    inverseRatioNum N u = (1 - u ^ N) ^ (1 / 2 : ℂ) * u *
      ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N)))
        (u ^ N) := (rfl)

/-- The defining formula of `TauCeti.inverseRatioDen`. -/
theorem inverseRatioDen_def (N : ℕ) (u : ℂ) :
    inverseRatioDen N u = (1 - u ^ N) ^ (1 / 2 : ℂ) *
      ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N)))
        (u ^ N) := (rfl)

/-- `η₁(0) = 0`. -/
@[simp]
theorem inverseRatioNum_zero (N : ℕ) : inverseRatioNum N 0 = 0 := by
  simp [inverseRatioNum_def]

/-- `η₂(0) = 1`. -/
@[simp]
theorem inverseRatioDen_zero {N : ℕ} (hN : N ≠ 0) : inverseRatioDen N 0 = 1 := by
  simp [inverseRatioDen_def, hN]

/-- `η₁ / η₂ = J_N` wherever `‖u ^ N‖ < 1`: the common factor `√(1 - u ^ N)` cancels. -/
theorem inverseRatioNum_div_inverseRatioDen {N : ℕ} {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    inverseRatioNum N u / inverseRatioDen N u = inverseRatio N u := by
  have hs : (1 - u ^ N) ^ (1 / 2 : ℂ) ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
    (by norm_num)).mpr (slitPlane_ne_zero (one_sub_mem_slitPlane hu))
  rw [inverseRatioNum_def, inverseRatioDen_def, inverseRatio_def, mul_assoc,
    mul_div_mul_left _ _ hs]

/-- **Rotation equivariance.** `η₁(ζ u) = ζ η₁(u)` for every `N`th root of unity `ζ`. -/
theorem inverseRatioNum_mul_of_pow_eq_one {N : ℕ} {ζ : ℂ} (hζ : ζ ^ N = 1) (u : ℂ) :
    inverseRatioNum N (ζ * u) = ζ * inverseRatioNum N u := by
  rw [inverseRatioNum_def, inverseRatioNum_def, mul_pow, hζ, one_mul]
  ring

/-- **Rotation invariance.** `η₂(ζ u) = η₂(u)` for every `N`th root of unity `ζ`. -/
theorem inverseRatioDen_mul_of_pow_eq_one {N : ℕ} {ζ : ℂ} (hζ : ζ ^ N = 1) (u : ℂ) :
    inverseRatioDen N (ζ * u) = inverseRatioDen N u := by
  rw [inverseRatioDen_def, inverseRatioDen_def, mul_pow, hζ, one_mul]

/-- `w ↦ √(1 - w ^ N)` is analytic where `‖w ^ N‖ < 1`. -/
private theorem analyticAt_sqrt_one_sub_pow {N : ℕ} {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    AnalyticAt ℂ (fun w : ℂ ↦ (1 - w ^ N) ^ (1 / 2 : ℂ)) u :=
  AnalyticAt.cpow (f := fun w : ℂ ↦ 1 - w ^ N) (by fun_prop) analyticAt_const
    (one_sub_mem_slitPlane hu)

/-- `w ↦ √(1 - w ^ N)` has logarithmic derivative `-N w ^ (N - 1) / (2 (1 - w ^ N))` where
`‖w ^ N‖ < 1`. -/
private theorem hasDerivAt_sqrt_one_sub_pow (N : ℕ) {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ (1 - w ^ N) ^ (1 / 2 : ℂ))
      ((1 - u ^ N) ^ (1 / 2 : ℂ) * (-(N * u ^ (N - 1)) / (2 * (1 - u ^ N)))) u := by
  have h₀ : 1 - u ^ N ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane hu)
  refine (((hasDerivAt_pow N u).const_sub 1).cpow_const (one_sub_mem_slitPlane hu)).congr_deriv ?_
  rw [cpow_sub _ _ h₀, cpow_one]
  field_simp

/-- `η₁` is analytic wherever `‖u ^ N‖ < 1`. -/
theorem analyticAt_inverseRatioNum {N : ℕ} {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    AnalyticAt ℂ (inverseRatioNum N) u := by
  have hF := analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) + 1) / (2 * N))
    (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N))) (u ^ N) (mem_ball_zero_iff.mpr hu)
  exact ((analyticAt_sqrt_one_sub_pow hu).mul analyticAt_id).mul
    (hF.comp_of_eq (analyticAt_id.pow N) rfl)

/-- `η₂` is analytic wherever `‖u ^ N‖ < 1`. -/
theorem analyticAt_inverseRatioDen {N : ℕ} {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    AnalyticAt ℂ (inverseRatioDen N) u := by
  have hF := analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) - 1) / (2 * N))
    (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N))) (u ^ N) (mem_ball_zero_iff.mpr hu)
  exact (analyticAt_sqrt_one_sub_pow hu).mul (hF.comp_of_eq (analyticAt_id.pow N) rfl)

/-- The second derivative of `w ↦ √(1 - w ^ N)` where `‖w ^ N‖ < 1`, through its logarithmic
derivative `ℓ(w) = -N w ^ (N - 1) / (2 (1 - w ^ N))`: it is `√(1 - u ^ N) (ℓ(u)² + ℓ'(u))`. -/
private theorem hasDerivAt_deriv_sqrt_one_sub_pow (N : ℕ) {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    HasDerivAt (deriv fun w : ℂ ↦ (1 - w ^ N) ^ (1 / 2 : ℂ))
      ((1 - u ^ N) ^ (1 / 2 : ℂ) * ((-(N * u ^ (N - 1)) / (2 * (1 - u ^ N))) ^ 2 +
        ((-(N * (((N - 1 : ℕ) : ℂ) * u ^ (N - 1 - 1)))) * (2 * (1 - u ^ N)) -
          -(N * u ^ (N - 1)) * (2 * -(N * u ^ (N - 1)))) / (2 * (1 - u ^ N)) ^ 2)) u := by
  have h₀ : 2 * (1 - u ^ N) ≠ 0 :=
    mul_ne_zero two_ne_zero (slitPlane_ne_zero (one_sub_mem_slitPlane hu))
  have hev : ∀ᶠ w in 𝓝 u, ‖w ^ N‖ < 1 :=
    (continuous_norm.comp (continuous_pow N)).continuousAt.eventually_lt continuousAt_const hu
  refine hasDerivAt_deriv_of_eventually_hasDerivAt_mul
    (ℓ := fun w : ℂ ↦ -(N * w ^ (N - 1)) / (2 * (1 - w ^ N)))
    (hev.mono fun w hw ↦ hasDerivAt_sqrt_one_sub_pow N hw) ?_
  exact (((hasDerivAt_pow (N - 1) u).const_mul (N : ℂ)).neg.fun_div
    (((hasDerivAt_pow N u).const_sub 1).const_mul 2) h₀).congr_deriv (by simp only [Pi.neg_apply])

/-- **The second solution of the inverse-cover equation.** For `N ≥ 2` and `‖u ^ N‖ < 1`,
`η₂(u) = √(1 - u ^ N) ₂F₁(a₋, a₋; 2a₋; u ^ N)` satisfies
`4 (u ^ N - 1)² η₂'' + ((N² - 1) u ^ (N - 2) + u ^ (2N - 2)) η₂ = 0` at `u`. -/
theorem inverseRatioDen_inverseCoverEquation {N : ℕ} (hN : 2 ≤ N) {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    4 * (u ^ N - 1) ^ 2 * deriv (deriv (inverseRatioDen N)) u +
      (((N : ℂ) ^ 2 - 1) * u ^ (N - 2) + u ^ (2 * N - 2)) * inverseRatioDen N u = 0 := by
  set a : ℂ := ((N : ℂ) - 1) / (2 * N) with ha
  have hF := analyticOnNhd_ordinaryHypergeometric ℂ a a (2 * a) (u ^ N) (mem_ball_zero_iff.mpr hu)
  have hd := (analyticAt_sqrt_one_sub_pow hu).hasDerivAt_deriv_mul_comp
    («φ» := fun w : ℂ ↦ w ^ N) (analyticAt_id.pow N) hF
  have hφ₁ : deriv (fun w : ℂ ↦ w ^ N) = fun w ↦ (N : ℂ) * w ^ (N - 1) :=
    funext fun w ↦ (hasDerivAt_pow N w).deriv
  have hφ₂ : deriv (fun w : ℂ ↦ (N : ℂ) * w ^ (N - 1)) u =
      N * (((N - 1 : ℕ) : ℂ) * u ^ (N - 1 - 1)) :=
    ((hasDerivAt_pow (N - 1) u).const_mul _).deriv
  have hG := ordinaryHypergeometric_gaussEquation_of_norm_lt_one a a (2 * a)
    (natCast_ne_neg_two_mul_minus hN) hu
  have h₀ : 1 - u ^ N ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane hu)
  rw [show inverseRatioDen N = fun w ↦ (1 - w ^ N) ^ (1 / 2 : ℂ) * ₂F₁ a a (2 * a) (w ^ N) from
    funext (inverseRatioDen_def N), hd.deriv, (hasDerivAt_sqrt_one_sub_pow N hu).deriv,
    (hasDerivAt_deriv_sqrt_one_sub_pow N hu).deriv, hφ₁, hφ₂]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  simp only [show M + 2 - 1 = M + 1 by omega, show M + 1 - 1 = M by omega,
    show M + 2 - 2 = M by omega, show 2 * (M + 2) - 2 = 2 * M + 2 by omega] at hG h₀ ⊢
  generalize ₂F₁ a a (2 * a) (u ^ (M + 2)) = F₀ at hG ⊢
  generalize deriv (₂F₁ a a (2 * a)) (u ^ (M + 2)) = F₁ at hG ⊢
  generalize deriv (deriv (₂F₁ a a (2 * a))) (u ^ (M + 2)) = F₂ at hG ⊢
  generalize (1 - u ^ (M + 2)) ^ (1 / 2 : ℂ) = S
  have hM : (M : ℂ) + 2 ≠ 0 := by norm_cast
  rw [ha] at hG
  push_cast at hG ⊢
  -- After clearing denominators, the inverse-cover operator applied to `η₂` is
  -- `u ^ (N - 2) (1 - u ^ N) √(1 - u ^ N)` times Gauss's operator, up to the cleared factors.
  field_simp at hG ⊢
  linear_combination 4 * (1 - u ^ (M + 2)) ^ 3 * u ^ M * S * hG

/-- **The first solution of the inverse-cover equation.** For `N ≥ 2` and `‖u ^ N‖ < 1`,
`η₁(u) = √(1 - u ^ N) u ₂F₁(a₊, a₊; 2a₊; u ^ N)` satisfies
`4 (u ^ N - 1)² η₁'' + ((N² - 1) u ^ (N - 2) + u ^ (2N - 2)) η₁ = 0` at `u`. -/
theorem inverseRatioNum_inverseCoverEquation {N : ℕ} (hN : 2 ≤ N) {u : ℂ} (hu : ‖u ^ N‖ < 1) :
    4 * (u ^ N - 1) ^ 2 * deriv (deriv (inverseRatioNum N)) u +
      (((N : ℂ) ^ 2 - 1) * u ^ (N - 2) + u ^ (2 * N - 2)) * inverseRatioNum N u = 0 := by
  set a : ℂ := ((N : ℂ) + 1) / (2 * N) with ha
  have hF := analyticOnNhd_ordinaryHypergeometric ℂ a a (2 * a) (u ^ N) (mem_ball_zero_iff.mpr hu)
  have hs := analyticAt_sqrt_one_sub_pow hu
  -- The prefactor `p(w) = √(1 - w ^ N) w` and its first two derivatives at `u`.
  have hd := (hs.fun_mul analyticAt_id).hasDerivAt_deriv_mul_comp
    («φ» := fun w : ℂ ↦ w ^ N) (analyticAt_id.pow N) hF
  simp only [id_eq] at hd
  have hp₂ := hs.hasDerivAt_deriv_mul_comp («φ» := id) (F := id) analyticAt_id analyticAt_id
  simp only [id_eq, deriv_id', deriv_id, deriv_const', mul_one, one_pow, mul_zero,
    add_zero] at hp₂
  have hp₁ := ((hasDerivAt_sqrt_one_sub_pow N hu).fun_mul (hasDerivAt_id' u)).deriv
  have hφ₁ : deriv (fun w : ℂ ↦ w ^ N) = fun w ↦ (N : ℂ) * w ^ (N - 1) :=
    funext fun w ↦ (hasDerivAt_pow N w).deriv
  have hφ₂ : deriv (fun w : ℂ ↦ (N : ℂ) * w ^ (N - 1)) u =
      N * (((N - 1 : ℕ) : ℂ) * u ^ (N - 1 - 1)) :=
    ((hasDerivAt_pow (N - 1) u).const_mul _).deriv
  have hG := ordinaryHypergeometric_gaussEquation_of_norm_lt_one a a (2 * a)
    (natCast_ne_neg_two_mul_plus (by omega)) hu
  have h₀ : 1 - u ^ N ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane hu)
  rw [show inverseRatioNum N = fun w ↦ (1 - w ^ N) ^ (1 / 2 : ℂ) * w * ₂F₁ a a (2 * a) (w ^ N)
    from funext (inverseRatioNum_def N), hd.deriv, hp₁, hp₂.deriv,
    (hasDerivAt_sqrt_one_sub_pow N hu).deriv, (hasDerivAt_deriv_sqrt_one_sub_pow N hu).deriv, hφ₁,
    hφ₂]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  simp only [show M + 2 - 1 = M + 1 by omega, show M + 1 - 1 = M by omega,
    show M + 2 - 2 = M by omega, show 2 * (M + 2) - 2 = 2 * M + 2 by omega] at hG h₀ ⊢
  generalize ₂F₁ a a (2 * a) (u ^ (M + 2)) = F₀ at hG ⊢
  generalize deriv (₂F₁ a a (2 * a)) (u ^ (M + 2)) = F₁ at hG ⊢
  generalize deriv (deriv (₂F₁ a a (2 * a))) (u ^ (M + 2)) = F₂ at hG ⊢
  generalize (1 - u ^ (M + 2)) ^ (1 / 2 : ℂ) = S
  have hM : (M : ℂ) + 2 ≠ 0 := by norm_cast
  rw [ha] at hG
  push_cast at hG ⊢
  -- After clearing denominators, the inverse-cover operator applied to `η₁` is
  -- `u ^ (N - 1) (1 - u ^ N) √(1 - u ^ N)` times Gauss's operator, up to the cleared factors.
  field_simp at hG ⊢
  linear_combination 4 * (1 - u ^ (M + 2)) ^ 3 * u ^ M * S * u * hG

/-- `η₁'(0) = 1`. -/
@[simp]
theorem deriv_inverseRatioNum_zero {N : ℕ} (hN : N ≠ 0) : deriv (inverseRatioNum N) 0 = 1 := by
  have hu : ‖(0 : ℂ) ^ N‖ < 1 := by simp [hN]
  have hF := analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) + 1) / (2 * N))
    (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N))) ((0 : ℂ) ^ N)
    (mem_ball_zero_iff.mpr hu)
  have h := ((analyticAt_sqrt_one_sub_pow hu).fun_mul analyticAt_id).deriv_mul_comp_eventuallyEq
    («φ» := fun w : ℂ ↦ w ^ N) (analyticAt_id.pow N) hF
  simp only [id_eq] at h
  rw [funext (inverseRatioNum_def N), h.eq_of_nhds,
    ((hasDerivAt_sqrt_one_sub_pow N hu).fun_mul (hasDerivAt_id' 0)).deriv]
  simp [hN]

/-- `η₂'(0) = 0`. -/
@[simp]
theorem deriv_inverseRatioDen_zero {N : ℕ} (hN : 2 ≤ N) : deriv (inverseRatioDen N) 0 = 0 := by
  have hu : ‖(0 : ℂ) ^ N‖ < 1 := by simp [show N ≠ 0 by omega]
  have hF := analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) - 1) / (2 * N))
    (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N))) ((0 : ℂ) ^ N)
    (mem_ball_zero_iff.mpr hu)
  have h := (analyticAt_sqrt_one_sub_pow hu).deriv_mul_comp_eventuallyEq
    («φ» := fun w : ℂ ↦ w ^ N) (analyticAt_id.pow N) hF
  rw [funext (inverseRatioDen_def N), h.eq_of_nhds, (hasDerivAt_sqrt_one_sub_pow N hu).deriv,
    (hasDerivAt_pow N (0 : ℂ)).deriv]
  simp [show N - 1 ≠ 0 by omega]

/-- For `N ≠ 0`, `‖u ^ N‖ < 1` exactly when `‖u‖ < 1`. -/
private theorem norm_pow_lt_one_iff {N : ℕ} (hN : N ≠ 0) {u : ℂ} : ‖u ^ N‖ < 1 ↔ ‖u‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one_iff_of_nonneg (norm_nonneg u) hN

/-- **The Wronskian of `η₁` and `η₂`.** For `N ≥ 2`, `η₁ η₂' - η₁' η₂ = -1` on the unit disc: the
inverse-cover equation has no first-derivative term, so the Wronskian is constant on the disc,
and its value at `0` is `-1` by the initial values. In particular `η₁` and `η₂` are linearly
independent solutions. -/
theorem inverseRatioNum_mul_deriv_inverseRatioDen_sub {N : ℕ} (hN : 2 ≤ N) {u : ℂ}
    (hu : ‖u ^ N‖ < 1) :
    inverseRatioNum N u * deriv (inverseRatioDen N) u -
      deriv (inverseRatioNum N) u * inverseRatioDen N u = -1 := by
  have hN₀ : N ≠ 0 := by omega
  have hball (v : ℂ) (hv : v ∈ Metric.ball (0 : ℂ) 1) : ‖v ^ N‖ < 1 :=
    (norm_pow_lt_one_iff hN₀).mpr (mem_ball_zero_iff.mp hv)
  have h₁ : AnalyticOnNhd ℂ (inverseRatioNum N) (Metric.ball 0 1) :=
    fun v hv ↦ analyticAt_inverseRatioNum (hball v hv)
  have h₂ : AnalyticOnNhd ℂ (inverseRatioDen N) (Metric.ball 0 1) :=
    fun v hv ↦ analyticAt_inverseRatioDen (hball v hv)
  -- The Wronskian has derivative `η₁ η₂'' - η₁'' η₂`, which the two equations make vanish.
  have hW (v : ℂ) (hv : v ∈ Metric.ball (0 : ℂ) 1) :
      HasDerivAt (fun w ↦ inverseRatioNum N w * deriv (inverseRatioDen N) w -
        deriv (inverseRatioNum N) w * inverseRatioDen N w) 0 v := by
    have hd := ((h₁ v hv).differentiableAt.hasDerivAt.fun_mul
      (h₂.deriv v hv).differentiableAt.hasDerivAt).fun_sub
      ((h₁.deriv v hv).differentiableAt.hasDerivAt.fun_mul (h₂ v hv).differentiableAt.hasDerivAt)
    refine hd.congr_deriv ?_
    have e₁ := inverseRatioNum_inverseCoverEquation hN (hball v hv)
    have e₂ := inverseRatioDen_inverseCoverEquation hN (hball v hv)
    have hv₁ : 4 * (v ^ N - 1) ^ 2 ≠ 0 := by
      refine mul_ne_zero (by norm_num) (pow_ne_zero 2 (sub_ne_zero.mpr fun h ↦ ?_))
      simpa [h] using hball v hv
    refine (mul_right_inj' hv₁).mp ?_
    linear_combination inverseRatioNum N v * e₂ - inverseRatioDen N v * e₁
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun v hv ↦ (hW v hv).differentiableAt.differentiableWithinAt)
    (fun v hv ↦ (hW v hv).deriv) (mem_ball_zero_iff.mpr ((norm_pow_lt_one_iff hN₀).mp hu))
    (Metric.mem_ball_self one_pos)
  rw [hconst]
  simp [hN, hN₀]

/-- On the sector `-π/N < arg u ≤ π/N`, where the principal branch gives `(u ^ N) ^ (1/N) = u`,
`η₁(u)` is the first hypergeometric solution
`√(1 - x) x^(1/N) ₂F₁(a₊, a₊; 2a₊; x)` of the descended equation at `x = u ^ N`. (The second
solution `√(1 - x) ₂F₁(a₋, a₋; 2a₋; x)` at `x = u ^ N` is `η₂(u)` by definition.) -/
theorem inverseRatioNum_eq_of_arg_mem {N : ℕ} {u : ℂ} (hlt : -(Real.pi / N) < u.arg)
    (hle : u.arg ≤ Real.pi / N) :
    inverseRatioNum N u = (1 - u ^ N) ^ (1 / 2 : ℂ) * (u ^ N) ^ (1 / (N : ℂ)) *
      ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N)))
        (u ^ N) := by
  rw [one_div (N : ℂ), pow_cpow_nat_inv hlt hle, inverseRatioNum_def]

end Solutions

end TauCeti
