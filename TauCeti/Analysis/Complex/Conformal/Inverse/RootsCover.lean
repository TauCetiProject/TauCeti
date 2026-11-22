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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.DSlope
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

## Main definitions

* `TauCeti.inverseRatio N u`: the hypergeometric ratio `J_N(u)`.

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

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.16 and its proof, pp. 671–672.
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

/-- The ratio of the two series in the variable `x = u ^ N`, so that `J_N(u) = u ρ_N(u ^ N)`. -/
private noncomputable def seriesRatio (N : ℕ) (x : ℂ) : ℂ :=
  ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N))) x /
    ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N)))
      x

private theorem inverseRatio_eq_mul_seriesRatio (N : ℕ) (u : ℂ) :
    inverseRatio N u = u * seriesRatio N (u ^ N) := by
  rw [inverseRatio_def, seriesRatio, mul_div_assoc]

private theorem seriesRatio_zero (N : ℕ) : seriesRatio N 0 = 1 := by
  simp [seriesRatio]

/-- Analyticity of `ρ_N` inside the unit disc, away from zeros of its denominator. -/
private theorem analyticAt_seriesRatio (N : ℕ) {x : ℂ} (hx : ‖x‖ < 1)
    (h : ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
      (2 * (((N : ℂ) - 1) / (2 * N))) x ≠ 0) :
    AnalyticAt ℂ (seriesRatio N) x := by
  have hx' : x ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hx
  exact (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ x hx').div
    (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ x hx') h

private theorem analyticAt_seriesRatio_zero (N : ℕ) : AnalyticAt ℂ (seriesRatio N) 0 :=
  analyticAt_seriesRatio N (by simp) (by simp)

/-- By the quotient rule, `ρ_N'(0) = a₊ a₊ / (2a₊) - a₋ a₋ / (2a₋) = a₊ / 2 - a₋ / 2 = 1 / (2N)`,
where `a a / (2a) = a / 2` also in the totalized case `a = 0`. -/
private theorem deriv_seriesRatio_zero (N : ℕ) : deriv (seriesRatio N) 0 = 1 / (2 * N) := by
  have hnum := (analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) + 1) / (2 * N))
    (((N : ℂ) + 1) / (2 * N)) (2 * (((N : ℂ) + 1) / (2 * N))) 0 (by simp)).differentiableAt
  have hden := (analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) - 1) / (2 * N))
    (((N : ℂ) - 1) / (2 * N)) (2 * (((N : ℂ) - 1) / (2 * N))) 0 (by simp)).differentiableAt
  have hfun : seriesRatio N = fun x ↦
      ₂F₁ (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N))
          (2 * (((N : ℂ) + 1) / (2 * N))) x /
        ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
          (2 * (((N : ℂ) - 1) / (2 * N))) x := rfl
  have hhalf (a : ℂ) : a * a / (2 * a) = a / 2 := by
    rw [div_mul_eq_div_div_swap, mul_self_div_self]
  rw [hfun, deriv_fun_div hnum hden (by simp), deriv_ordinaryHypergeometric_zero,
    deriv_ordinaryHypergeometric_zero, hhalf, hhalf, ordinaryHypergeometric_zero,
    ordinaryHypergeometric_zero]
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
  rw [inverseRatio_eq_mul_seriesRatio, inverseRatio_eq_mul_seriesRatio, mul_pow, hζ, one_mul,
    mul_assoc]

/-- `J_N` is analytic at every `u` with `‖u ^ N‖ < 1` at which the denominator series
`₂F₁(a₋, a₋; 2a₋; u ^ N)` does not vanish. -/
theorem analyticAt_inverseRatio {N : ℕ} {u : ℂ} (hu : ‖u ^ N‖ < 1)
    (h : ₂F₁ (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
      (2 * (((N : ℂ) - 1) / (2 * N))) (u ^ N) ≠ 0) :
    AnalyticAt ℂ (inverseRatio N) u := by
  have hr : AnalyticAt ℂ (fun v : ℂ ↦ seriesRatio N (v ^ N)) u :=
    (analyticAt_seriesRatio N hu h).comp_of_eq (by fun_prop) rfl
  rw [funext (inverseRatio_eq_mul_seriesRatio N)]
  fun_prop

/-- `J_N` is an analytic germ at `0`. -/
theorem analyticAt_inverseRatio_zero (N : ℕ) : AnalyticAt ℂ (inverseRatio N) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [funext (inverseRatio_eq_mul_seriesRatio 0)]
    simp only [pow_zero]
    fun_prop
  · exact analyticAt_inverseRatio (by simp [hN]) (by simp [hN])

/-- For `N ≠ 0`, `J_N(u) = u + u ^ (N + 1) q(u)` for a function `q` analytic at `0` with
`q(0) = 1 / (2N)`; namely `q(u)` is the difference quotient of `ρ_N` at `0` evaluated at
`u ^ N`. -/
private theorem exists_inverseRatio_eq_add_pow_mul {N : ℕ} (hN : N ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ q 0 = 1 / (2 * N) ∧
      ∀ u, inverseRatio N u = u + u ^ (N + 1) * q u := by
  refine ⟨fun u ↦ dslope (seriesRatio N) 0 (u ^ N), ?_, ?_, fun u ↦ ?_⟩
  · refine AnalyticAt.comp (g := dslope (seriesRatio N) 0) ?_ (analyticAt_id.pow N)
    simpa [hN] using (analyticAt_seriesRatio_zero N).dslope 0
  · simp [hN, dslope_same, deriv_seriesRatio_zero]
  · have h := sub_smul_dslope (seriesRatio N) 0 (u ^ N)
    rw [sub_zero, smul_eq_mul, seriesRatio_zero] at h
    rw [inverseRatio_eq_mul_seriesRatio, pow_succ', mul_assoc, h]
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
  simp
  omega

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

end TauCeti
