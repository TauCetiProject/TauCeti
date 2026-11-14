/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.Analysis.SpecialFunctions.Gamma.TaylorSeries
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# The explicit Gamma conformal radius and its odd-zeta expansion

For an integer `N ≥ 2`, the holomorphic universal covering map of `ℂ \ μ_N` based at the origin has
conformal radius
`γ_N = 16 ^ (1 / N) * Γ(1 + 1 / (2N)) ^ 2 * Γ(1 - 1 / N) / (Γ(1 - 1 / (2N)) ^ 2 * Γ(1 + 1 / N))`.
This file defines `TauCeti.gammaRadius` by that real Gamma formula and develops its analytic
identities and effective asymptotic expansion in powers of `1 / N`:

* Legendre's duplication formula rewrites `gammaRadius N` for `N ≥ 2` without the `16 ^ (1 / N)`
  prefactor as `Γ((N - 1) / (2N)) ^ 2 * Γ(1 + 1 / N) / (Γ((N + 1) / (2N)) ^ 2 * Γ(1 - 1 / N))`,
  from which the closed values at `N = 2` and `N = 3` follow.
* Combining the Taylor series of `log (Γ(1 + x))` at `x = ±1 / (2N)` and `x = ±1 / N` cancels
  Euler's constant and all even zeta values, leaving an absolutely convergent series of positive
  odd-zeta terms for `log (gammaRadius N) - (log 16) / N`.
* Exponentiating that positive series yields both the strict lower bound
  `16 ^ (1 / N) * (1 + Re ζ(3) / (2N ^ 3) + 3 Re ζ(5) / (8N ^ 5)) < gammaRadius N` and an explicit
  `O(N ^ (-6))` upper bound with constant `3`.

Outside `N ≥ 2`, `gammaRadius N` is only the totalized real expression: `gammaRadius 1 = 0`
because `Γ(0) = 0`, and `gammaRadius 0 = 1` by division-by-zero totalization; neither value has a
uniformization meaning.

## Main definitions

* `TauCeti.gammaRadius`: the explicit real Gamma formula for `γ_N`.

## Main results

* `TauCeti.gammaRadius_zero` and `TauCeti.gammaRadius_one`: totalized values `1` and `0` at
  `N = 0` and `N = 1`.
* `TauCeti.gammaRadius_pos`: `0 < gammaRadius N` for `N ≠ 1`.
* `TauCeti.gammaRadius_eq_div`: the alternative Gamma quotient formula for `N ≠ 0`.
* `TauCeti.tendsto_gammaRadius_atTop`: `gammaRadius N → 1` as `N → ∞`.
* `TauCeti.gammaRadius_two` and `TauCeti.gammaRadius_three`: closed values
  `Γ(1 / 4) ^ 4 / (4 * π ^ 2)` and `Γ(1 / 6) ^ 3 / (12 * π ^ (3 / 2))`.
* `TauCeti.hasSum_log_gammaRadius_sub_div` and `TauCeti.log_gammaRadius_eq_div_add_tsum`: the
  odd-zeta power series for `log (gammaRadius N)` when `N ≠ 1`.
* `TauCeti.mul_lt_gammaRadius`, `TauCeti.gammaRadius_le_mul_add`, and
  `TauCeti.exists_pos_forall_gammaRadius_eq`: the positive `O(N ^ (-6))` remainder expansion of
  `gammaRadius N`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Theorem 5.1.4, equation (5.1.6), and Example 5.1.22.
-/

public section

namespace TauCeti

open Filter
open scoped Topology

/-- The explicit real Gamma expression for the conformal radius at `0` of the complement of the
`N`th roots of unity when `2 ≤ N`. For `N < 2` it is only the totalized arithmetic expression
(`gammaRadius 1 = 0` via `Real.Gamma 0 = 0`, and `gammaRadius 0 = 1` via `1 / 0 = 0`) and carries
no geometric meaning. -/
noncomputable def gammaRadius (N : ℕ) : ℝ :=
  (16 : ℝ) ^ (1 / (N : ℝ)) * Real.Gamma (1 + 1 / (2 * (N : ℝ))) ^ 2 *
    Real.Gamma (1 - 1 / (N : ℝ)) /
    (Real.Gamma (1 - 1 / (2 * (N : ℝ))) ^ 2 * Real.Gamma (1 + 1 / (N : ℝ)))

/-- The defining formula of `TauCeti.gammaRadius`. -/
theorem gammaRadius_def (N : ℕ) :
    gammaRadius N =
      (16 : ℝ) ^ (1 / (N : ℝ)) * Real.Gamma (1 + 1 / (2 * (N : ℝ))) ^ 2 *
        Real.Gamma (1 - 1 / (N : ℝ)) /
        (Real.Gamma (1 - 1 / (2 * (N : ℝ))) ^ 2 * Real.Gamma (1 + 1 / (N : ℝ))) := (rfl)

/-- At `N = 0`, division-by-zero totalization gives `gammaRadius 0 = 1`. -/
@[simp]
theorem gammaRadius_zero : gammaRadius 0 = 1 := by
  simp [gammaRadius_def]

/-- At `N = 1`, the totalized expression vanishes because `Real.Gamma 0 = 0`. -/
@[simp]
theorem gammaRadius_one : gammaRadius 1 = 0 := by
  simp [gammaRadius_def]

private theorem inv_natCast_le_half {N : ℕ} (hN : 2 ≤ N) : 1 / (N : ℝ) ≤ 1 / 2 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  exact one_div_le_one_div_of_le two_pos hN2

private theorem inv_two_mul_natCast_le_quarter {N : ℕ} (hN : 2 ≤ N) :
    1 / (2 * (N : ℝ)) ≤ 1 / 4 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- For every `N ≠ 1`, `gammaRadius N` is strictly positive; for `2 ≤ N` every Gamma factor in its
numerator and denominator is positive and nonzero, while at `N = 0` it evaluates to `1`. -/
theorem gammaRadius_pos {N : ℕ} (hN : N ≠ 1) : 0 < gammaRadius N := by
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  · have hN2 : 2 ≤ N := by omega
    rw [gammaRadius_def]
    have h1 : 1 / (N : ℝ) ≤ 1 / 2 := inv_natCast_le_half hN2
    have h2 : 1 / (2 * (N : ℝ)) ≤ 1 / 4 := inv_two_mul_natCast_le_quarter hN2
    have hg2 : 0 < Real.Gamma (1 - 1 / (N : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
    have hg3 : 0 < Real.Gamma (1 - 1 / (2 * (N : ℝ))) := Real.Gamma_pos_of_pos (by linarith)
    positivity

private theorem gamma_sq_mul_gamma_add_half_sq (y : ℝ) :
    Real.Gamma y ^ 2 * Real.Gamma (y + 1 / 2) ^ 2 =
      Real.Gamma (2 * y) ^ 2 * ((2 : ℝ) ^ (1 - 2 * y)) ^ 2 * Real.sqrt Real.pi ^ 2 := by
  have hd := Real.Gamma_mul_Gamma_add_half y
  linear_combination (Real.Gamma y * Real.Gamma (y + 1 / 2) +
    Real.Gamma (2 * y) * (2 : ℝ) ^ (1 - 2 * y) * Real.sqrt Real.pi) * hd

private theorem gammaRadius_eq_div_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    gammaRadius N =
      Real.Gamma (((N : ℝ) - 1) / (2 * (N : ℝ))) ^ 2 * Real.Gamma (1 + 1 / (N : ℝ)) /
        (Real.Gamma (((N : ℝ) + 1) / (2 * (N : ℝ))) ^ 2 * Real.Gamma (1 - 1 / (N : ℝ))) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  let x : ℝ := 1 / (N : ℝ)
  have hx : x ≤ 1 / 2 := inv_natCast_le_half hN
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hm : ((N : ℝ) - 1) / (2 * (N : ℝ)) = (1 - x) / 2 := by dsimp [x]; field_simp [hN0]
  have hp : ((N : ℝ) + 1) / (2 * (N : ℝ)) = (1 + x) / 2 := by dsimp [x]; field_simp [hN0]
  have hp' : 1 + 1 / (2 * (N : ℝ)) = (1 + x) / 2 + 1 / 2 := by dsimp [x]; field_simp [hN0]; ring
  have hm' : 1 - 1 / (2 * (N : ℝ)) = (1 - x) / 2 + 1 / 2 := by dsimp [x]; field_simp [hN0]; ring
  have hsq_pos := gamma_sq_mul_gamma_add_half_sq ((1 + x) / 2)
  have hp1 : 2 * ((1 + x) / 2) = 1 + x := by ring
  have hp2 : 1 - (1 + x) = -x := by ring
  rw [hp1, hp2] at hsq_pos
  have hsq_neg := gamma_sq_mul_gamma_add_half_sq ((1 - x) / 2)
  have hm1 : 2 * ((1 - x) / 2) = 1 - x := by ring
  have hm2 : 1 - (1 - x) = x := by ring
  rw [hm1, hm2] at hsq_neg
  have hpow : (16 : ℝ) ^ x * ((2 : ℝ) ^ (-x)) ^ 2 = ((2 : ℝ) ^ x) ^ 2 := by
    have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h16, ← Real.rpow_mul zero_le_two, ← Real.rpow_natCast ((2 : ℝ) ^ (-x)),
      ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos,
      ← Real.rpow_natCast ((2 : ℝ) ^ x), ← Real.rpow_mul zero_le_two]
    congr 1; push_cast; ring
  have hg_d1 : Real.Gamma ((1 - x) / 2 + 1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hg_d2 : Real.Gamma (1 + x) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hg_d4 : Real.Gamma (1 - x) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hx_def : 1 / (N : ℝ) = x := rfl
  rw [gammaRadius_def, hm, hp, hp', hm', hx_def, div_eq_div_iff (by positivity) (by positivity)]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hg_d2) (pow_ne_zero 2 hpi))
  linear_combination
    (16 : ℝ) ^ x * Real.Gamma (1 - x) ^ 2 * Real.Gamma (1 + x) ^ 2 * Real.sqrt Real.pi ^ 2 *
        hsq_pos -
      Real.Gamma (1 + x) ^ 4 * Real.sqrt Real.pi ^ 2 * hsq_neg +
      Real.Gamma (1 - x) ^ 2 * Real.Gamma (1 + x) ^ 4 * Real.sqrt Real.pi ^ 4 * hpow

/-- **Alternative Gamma formula for `gammaRadius`** (via Legendre's duplication formula):
for `N ≠ 0`,
`gammaRadius N = Γ((N - 1) / (2N)) ^ 2 * Γ(1 + 1 / N) / (Γ((N + 1) / (2N)) ^ 2 * Γ(1 - 1 / N))`. -/
theorem gammaRadius_eq_div {N : ℕ} (hN : N ≠ 0) :
    gammaRadius N =
      Real.Gamma (((N : ℝ) - 1) / (2 * (N : ℝ))) ^ 2 * Real.Gamma (1 + 1 / (N : ℝ)) /
        (Real.Gamma (((N : ℝ) + 1) / (2 * (N : ℝ))) ^ 2 * Real.Gamma (1 - 1 / (N : ℝ))) := by
  rcases eq_or_ne N 1 with rfl | hN1
  · simp
  · exact gammaRadius_eq_div_of_two_le (by omega)

/-- As `N → ∞`, `gammaRadius N` tends to `1`. -/
theorem tendsto_gammaRadius_atTop : Tendsto gammaRadius atTop (𝓝 1) := by
  let g : ℝ → ℝ := fun x ↦
    (16 : ℝ) ^ x * Real.Gamma (1 + x / 2) ^ 2 * Real.Gamma (1 - x) /
      (Real.Gamma (1 - x / 2) ^ 2 * Real.Gamma (1 + x))
  have hΓ : ContinuousAt Real.Gamma 1 :=
    (Real.differentiableAt_Gamma fun m ↦ by linarith).continuousAt
  have hc_add2 : ContinuousAt (fun x : ℝ ↦ Real.Gamma (1 + x / 2)) 0 :=
    hΓ.comp_of_eq (f := fun x : ℝ ↦ 1 + x / 2) (by fun_prop) (by norm_num)
  have hc_sub1 : ContinuousAt (fun x : ℝ ↦ Real.Gamma (1 - x)) 0 :=
    hΓ.comp_of_eq (f := fun x : ℝ ↦ 1 - x) (by fun_prop) (by norm_num)
  have hc_sub2 : ContinuousAt (fun x : ℝ ↦ Real.Gamma (1 - x / 2)) 0 :=
    hΓ.comp_of_eq (f := fun x : ℝ ↦ 1 - x / 2) (by fun_prop) (by norm_num)
  have hc_add1 : ContinuousAt (fun x : ℝ ↦ Real.Gamma (1 + x)) 0 :=
    hΓ.comp_of_eq (f := fun x : ℝ ↦ 1 + x) (by fun_prop) (by norm_num)
  have hc16 : ContinuousAt (fun x : ℝ ↦ (16 : ℝ) ^ x) 0 :=
    Real.continuousAt_const_rpow (by norm_num)
  have hden0 : Real.Gamma (1 - (0 : ℝ) / 2) ^ 2 * Real.Gamma (1 + (0 : ℝ)) ≠ 0 := by
    norm_num [Real.Gamma_one]
  have hcg : ContinuousAt g 0 :=
    (((hc16.mul (hc_add2.pow 2)).mul hc_sub1).div ((hc_sub2.pow 2).mul hc_add1) hden0)
  have hg0 : g 0 = 1 := by
    dsimp [g]
    norm_num [Real.Gamma_one]
  have ht := (hg0 ▸ hcg.tendsto).comp tendsto_one_div_atTop_nhds_zero_nat
  refine ht.congr fun N ↦ ?_
  dsimp [g, Function.comp_apply]
  rw [gammaRadius_def, div_div, mul_comm (N : ℝ) 2]

/-- The exact value `gammaRadius 2 = Γ(1 / 4) ^ 4 / (4 * π ^ 2)`. -/
theorem gammaRadius_two : gammaRadius 2 = Real.Gamma (1 / 4) ^ 4 / (4 * Real.pi ^ 2) := by
  rw [gammaRadius_eq_div (by norm_num)]
  have ha1 : (((2 : ℕ) : ℝ) - 1) / (2 * ((2 : ℕ) : ℝ)) = 1 / 4 := by norm_num
  have ha2 : (1 : ℝ) + 1 / ((2 : ℕ) : ℝ) = 3 / 2 := by norm_num
  have ha3 : (((2 : ℕ) : ℝ) + 1) / (2 * ((2 : ℕ) : ℝ)) = 3 / 4 := by norm_num
  have ha4 : (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [ha1, ha2, ha3, ha4]
  have h32 : Real.Gamma (3 / 2) = 1 / 2 * Real.Gamma (1 / 2) := by
    have h := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
    norm_num at h
    exact h
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  have hsin : Real.sin (Real.pi * (1 / 4)) = Real.sqrt 2 / 2 := by
    rw [mul_one_div, Real.sin_pi_div_four]
  have hsub : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  rw [hsub, hsin] at hrefl
  have hsq : Real.Gamma (1 / 4) ^ 2 * Real.Gamma (3 / 4) ^ 2 = 2 * Real.pi ^ 2 := by
    have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
    have hrefl' : Real.Gamma (1 / 4) * Real.Gamma (3 / 4) * Real.sqrt 2 = 2 * Real.pi := by
      field_simp [h2] at hrefl ⊢
      linarith
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have hsq' : (Real.Gamma (1 / 4) * Real.Gamma (3 / 4) * Real.sqrt 2) ^ 2 =
        (2 * Real.pi) ^ 2 := congrArg (· ^ 2) hrefl'
    nlinarith [hsq2, hsq']
  rw [h32, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination -Real.Gamma (1 / 4) ^ 2 * Real.Gamma (1 / 2) * hsq

/-- The exact value `gammaRadius 3 = Γ(1 / 6) ^ 3 / (12 * π ^ (3 / 2))`. -/
theorem gammaRadius_three :
    gammaRadius 3 = Real.Gamma (1 / 6) ^ 3 / (12 * Real.pi ^ ((3 : ℝ) / 2)) := by
  rw [gammaRadius_eq_div (by norm_num)]
  have ha1 : (((3 : ℕ) : ℝ) - 1) / (2 * ((3 : ℕ) : ℝ)) = 1 / 3 := by norm_num
  have ha2 : (1 : ℝ) + 1 / ((3 : ℕ) : ℝ) = 4 / 3 := by norm_num
  have ha3 : (((3 : ℕ) : ℝ) + 1) / (2 * ((3 : ℕ) : ℝ)) = 2 / 3 := by norm_num
  have ha4 : (1 : ℝ) - 1 / ((3 : ℕ) : ℝ) = 2 / 3 := by norm_num
  rw [ha1, ha2, ha3, ha4]
  have h43 : Real.Gamma (4 / 3) = 1 / 3 * Real.Gamma (1 / 3) := by
    have h := Real.Gamma_add_one (s := 1 / 3) (by norm_num)
    norm_num at h
    exact h
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 6 : ℝ)
  norm_num at hdup
  have hpow2 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    norm_num
  have hpowpi : Real.sqrt Real.pi ^ 3 = Real.pi ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    norm_num
  have hcube : Real.Gamma (1 / 6) ^ 3 * Real.Gamma (2 / 3) ^ 3 =
      4 * Real.Gamma (1 / 3) ^ 3 * Real.pi ^ ((3 : ℝ) / 2) := by
    have hc := congrArg (· ^ 3) hdup
    rw [mul_pow, mul_pow, mul_pow, hpow2, hpowpi] at hc
    linarith
  rw [h43, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination -hcube

/-! ### Odd-zeta series for `log (gammaRadius N)` -/

private noncomputable def oddZetaRadiusTerm (N k : ℕ) : ℝ :=
  (2 ^ (2 * k + 2) - 1 : ℝ) * (riemannZeta (2 * k + 3)).re /
    (2 ^ (2 * k + 1) * (2 * k + 3) * (N : ℝ) ^ (2 * k + 3))

private theorem oddZetaRadiusTerm_pos {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    0 < oddZetaRadiusTerm N k := by
  dsimp [oddZetaRadiusTerm]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by linarith
  have hpow : (1 : ℝ) < 2 ^ (2 * k + 2) := by
    have : (2 : ℝ) ^ 2 ≤ 2 ^ (2 * k + 2) := pow_le_pow_right₀ one_le_two (by omega)
    linarith
  have hcast : (2 * (k : ℂ) + 3) = ((2 * (k : ℝ) + 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hzeta : 0 < (riemannZeta (2 * k + 3)).re := by
    rw [hcast]
    exact riemannZeta_re_pos_of_one_lt (by linarith)
  have hnum : 0 < (2 ^ (2 * k + 2) - 1 : ℝ) * (riemannZeta (2 * k + 3)).re :=
    mul_pos (sub_pos.mpr hpow) hzeta
  exact div_pos hnum (mul_pos (by positivity) (pow_pos hN0 _))

private theorem log_gammaRadius_sub_div_eq {N : ℕ} (hN : 2 ≤ N) :
    Real.log (gammaRadius N) - Real.log 16 / (N : ℝ) =
      2 * (Real.log (Real.Gamma (1 + 1 / (2 * (N : ℝ)))) +
          Real.eulerMascheroniConstant * (1 / (2 * (N : ℝ)))) +
        (Real.log (Real.Gamma (1 + -1 / (N : ℝ))) +
          Real.eulerMascheroniConstant * (-1 / (N : ℝ))) -
        (2 * (Real.log (Real.Gamma (1 + -1 / (2 * (N : ℝ)))) +
            Real.eulerMascheroniConstant * (-1 / (2 * (N : ℝ)))) +
          (Real.log (Real.Gamma (1 + 1 / (N : ℝ))) +
            Real.eulerMascheroniConstant * (1 / (N : ℝ)))) := by
  have h1 : 1 / (N : ℝ) ≤ 1 / 2 := inv_natCast_le_half hN
  have h2 : 1 / (2 * (N : ℝ)) ≤ 1 / 4 := inv_two_mul_natCast_le_quarter hN
  have hg1 : 0 < Real.Gamma (1 + 1 / (2 * (N : ℝ))) := Real.Gamma_pos_of_pos (by positivity)
  have hg2 : 0 < Real.Gamma (1 - 1 / (N : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
  have hg3 : 0 < Real.Gamma (1 - 1 / (2 * (N : ℝ))) := Real.Gamma_pos_of_pos (by linarith)
  have hg4 : 0 < Real.Gamma (1 + 1 / (N : ℝ)) := Real.Gamma_pos_of_pos (by positivity)
  have h16 : 0 < (16 : ℝ) ^ (1 / (N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  rw [gammaRadius_def,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) hg2.ne',
    Real.log_mul h16.ne' (pow_ne_zero 2 hg1.ne'),
    Real.log_mul (pow_ne_zero 2 hg3.ne') hg4.ne',
    Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 16)]
  have hs1 : (1 : ℝ) + -1 / (N : ℝ) = 1 - 1 / (N : ℝ) := by ring
  have hs2 : (1 : ℝ) + -1 / (2 * (N : ℝ)) = 1 - 1 / (2 * (N : ℝ)) := by ring
  rw [hs1, hs2]
  push_cast
  ring

private noncomputable def combinedLogGammaTerm (N j : ℕ) : ℝ :=
  2 * ((-1 : ℝ) ^ j * (riemannZeta (j + 2)).re * (1 / (2 * (N : ℝ))) ^ (j + 2) / (j + 2)) +
      (-1 : ℝ) ^ j * (riemannZeta (j + 2)).re * (-1 / (N : ℝ)) ^ (j + 2) / (j + 2) -
    (2 * ((-1 : ℝ) ^ j * (riemannZeta (j + 2)).re * (-1 / (2 * (N : ℝ))) ^ (j + 2) / (j + 2)) +
      (-1 : ℝ) ^ j * (riemannZeta (j + 2)).re * (1 / (N : ℝ)) ^ (j + 2) / (j + 2))

private theorem combinedLogGammaTerm_even {N j : ℕ} (hj : Even j) :
    combinedLogGammaTerm N j = 0 := by
  rcases hj with ⟨k, rfl⟩
  dsimp [combinedLogGammaTerm]
  have heven1 : (-1 / (N : ℝ)) ^ (k + k + 2) = (1 / (N : ℝ)) ^ (k + k + 2) := by
    rw [neg_div, Even.neg_pow ⟨k + 1, by omega⟩]
  have heven2 : (-1 / (2 * (N : ℝ))) ^ (k + k + 2) = (1 / (2 * (N : ℝ))) ^ (k + k + 2) := by
    rw [neg_div, Even.neg_pow ⟨k + 1, by omega⟩]
  rw [heven1, heven2]
  ring

private theorem combinedLogGammaTerm_two_mul_add_one {N : ℕ} (hN0 : (N : ℝ) ≠ 0) (k : ℕ) :
    combinedLogGammaTerm N (2 * k + 1) = oddZetaRadiusTerm N k := by
  dsimp [combinedLogGammaTerm, oddZetaRadiusTerm]
  have hodd1 : (-1 : ℝ) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
  have hodd_neg1 : (-1 / (N : ℝ)) ^ (2 * k + 1 + 2) = -(1 / (N : ℝ)) ^ (2 * k + 3) := by
    rw [neg_div, Odd.neg_pow ⟨k + 1, by omega⟩]
  have hodd_neg2 : (-1 / (2 * (N : ℝ))) ^ (2 * k + 1 + 2) =
      -(1 / (2 * (N : ℝ))) ^ (2 * k + 3) := by
    rw [neg_div, Odd.neg_pow ⟨k + 1, by omega⟩]
  have hexp : 2 * k + 1 + 2 = 2 * k + 3 := by omega
  rw [hodd1, hodd_neg1, hodd_neg2, hexp]
  have hcast : ((2 * k + 1 : ℕ) : ℂ) + 2 = 2 * (k : ℂ) + 3 := by push_cast; ring
  have hcastR : ((2 * k + 1 : ℕ) : ℝ) + 2 = 2 * (k : ℝ) + 3 := by push_cast; ring
  rw [hcast, hcastR]
  have h2pow : (2 : ℝ) ^ (2 * k + 3) = 4 * 2 ^ (2 * k + 1) := by
    have he : 2 * k + 3 = (2 * k + 1) + 2 := by omega
    rw [he, pow_add]; ring
  have h2pow' : (2 : ℝ) ^ (2 * k + 2) = 2 * 2 ^ (2 * k + 1) := by
    have he : 2 * k + 2 = (2 * k + 1) + 1 := by omega
    rw [he, pow_succ']
  rw [one_div_pow, one_div_pow, mul_pow, h2pow, h2pow']
  have hk0 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  have hp0 : (2 : ℝ) ^ (2 * k + 1) ≠ 0 := by positivity
  have hNp : (N : ℝ) ^ (2 * k + 3) ≠ 0 := pow_ne_zero _ hN0
  field_simp [hk0, hp0, hNp]
  ring

private theorem hasSum_log_gammaRadius_sub_div_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    HasSum (fun k : ℕ ↦
      (2 ^ (2 * k + 2) - 1 : ℝ) * (riemannZeta (2 * k + 3)).re /
        (2 ^ (2 * k + 1) * (2 * k + 3) * (N : ℝ) ^ (2 * k + 3)))
      (Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hx1 : |1 / (2 * (N : ℝ))| < 1 := by
    rw [abs_of_nonneg (by positivity)]; linarith [inv_two_mul_natCast_le_quarter hN]
  have hx2 : |-1 / (N : ℝ)| < 1 := by
    rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]; linarith [inv_natCast_le_half hN]
  have hx3 : |-1 / (2 * (N : ℝ))| < 1 := by
    rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
    linarith [inv_two_mul_natCast_le_quarter hN]
  have hx4 : |1 / (N : ℝ)| < 1 := by
    rw [abs_of_nonneg (by positivity)]; linarith [inv_natCast_le_half hN]
  have hs : HasSum (combinedLogGammaTerm N) (Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)) := by
    have h := (((Real.hasSum_log_Gamma_one_add_add_eulerMascheroniConstant_mul hx1).mul_left 2).add
      (Real.hasSum_log_Gamma_one_add_add_eulerMascheroniConstant_mul hx2)).sub
      (((Real.hasSum_log_Gamma_one_add_add_eulerMascheroniConstant_mul hx3).mul_left 2).add
        (Real.hasSum_log_Gamma_one_add_add_eulerMascheroniConstant_mul hx4))
    rwa [← log_gammaRadius_sub_div_eq hN] at h
  have hinj : Function.Injective fun k : ℕ ↦ 2 * k + 1 := fun a b hab ↦ by dsimp at hab; omega
  rw [← hinj.hasSum_iff] at hs
  · exact hs.congr_fun fun k ↦ (combinedLogGammaTerm_two_mul_add_one hN0 k).symm
  · intro j hj
    rcases Nat.even_or_odd j with hev | ⟨k, rfl⟩
    · exact combinedLogGammaTerm_even hev
    · exact False.elim (hj ⟨k, rfl⟩)

/-- **Odd-zeta series for `log (gammaRadius N)`**: for every `N ≠ 1`,
`log (gammaRadius N) - (log 16) / N` is the sum of the odd-zeta series
`∑_{k ≥ 0} (2 ^ (2k + 2) - 1) Re(ζ(2k + 3)) / (2 ^ (2k + 1) (2k + 3) N ^ (2k + 3))` (whose terms
are strictly positive for `N ≥ 2` and vanish at `N = 0`). -/
theorem hasSum_log_gammaRadius_sub_div {N : ℕ} (hN : N ≠ 1) :
    HasSum (fun k : ℕ ↦
      (2 ^ (2 * k + 2) - 1 : ℝ) * (riemannZeta (2 * k + 3)).re /
        (2 ^ (2 * k + 1) * (2 * k + 3) * (N : ℝ) ^ (2 * k + 3)))
      (Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · simp only [gammaRadius_zero, Real.log_one, Nat.cast_zero, div_zero, sub_self]
    refine (hasSum_zero (α := ℝ)).congr_fun fun k ↦ ?_
    rw [zero_pow (by omega), mul_zero, div_zero]
  · exact hasSum_log_gammaRadius_sub_div_of_two_le (by omega)

/-- **Odd-zeta series for `log (gammaRadius N)`**, written with `tsum`. -/
theorem log_gammaRadius_eq_div_add_tsum {N : ℕ} (hN : N ≠ 1) :
    Real.log (gammaRadius N) =
      Real.log 16 / (N : ℝ) +
        ∑' k : ℕ, (2 ^ (2 * k + 2) - 1 : ℝ) * (riemannZeta (2 * k + 3)).re /
          (2 ^ (2 * k + 1) * (2 * k + 3) * (N : ℝ) ^ (2 * k + 3)) := by
  have h := (hasSum_log_gammaRadius_sub_div hN).tsum_eq
  linarith

/-! ### Effective positive `O(N ^ (-6))` expansion -/

private theorem oddZetaRadiusTerm_zero (N : ℕ) :
    oddZetaRadiusTerm N 0 = (riemannZeta 3).re / (2 * (N : ℝ) ^ 3) := by
  dsimp [oddZetaRadiusTerm]
  norm_num
  ring

private theorem oddZetaRadiusTerm_one (N : ℕ) :
    oddZetaRadiusTerm N 1 = 3 * (riemannZeta 5).re / (8 * (N : ℝ) ^ 5) := by
  dsimp [oddZetaRadiusTerm]
  norm_num
  ring

private theorem oddZetaRadiusTerm_le {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    oddZetaRadiusTerm N k ≤ 4 / ((2 * (k : ℝ) + 3) * (N : ℝ) ^ (2 * k + 3)) := by
  dsimp [oddZetaRadiusTerm]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast : (2 * (k : ℂ) + 3) = ((2 * (k : ℝ) + 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hzeta0 : 0 < (riemannZeta (2 * k + 3)).re := by
    rw [hcast]
    exact riemannZeta_re_pos_of_one_lt (by linarith)
  have hzeta2 : (riemannZeta (2 * k + 3)).re ≤ 2 :=
    (riemannZeta_re_lt_two (by simp; linarith)).le
  have h2pow : (2 ^ (2 * k + 2) - 1 : ℝ) ≤ 2 * 2 ^ (2 * k + 1) := by
    have he : 2 * k + 2 = (2 * k + 1) + 1 := by omega
    rw [he, pow_succ']
    linarith
  have hnum : (2 ^ (2 * k + 2) - 1 : ℝ) * (riemannZeta (2 * k + 3)).re ≤
      4 * 2 ^ (2 * k + 1) := by
    have hp : (0 : ℝ) < 2 ^ (2 * k + 1) := by positivity
    nlinarith
  have hden : 0 ≤ (2 : ℝ) ^ (2 * k + 1) * (2 * (k : ℝ) + 3) * (N : ℝ) ^ (2 * k + 3) :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  calc (2 ^ (2 * k + 2) - 1 : ℝ) * (riemannZeta (2 * k + 3)).re /
        (2 ^ (2 * k + 1) * (2 * k + 3) * (N : ℝ) ^ (2 * k + 3))
      ≤ (4 * 2 ^ (2 * k + 1)) / (2 ^ (2 * k + 1) * (2 * k + 3) * (N : ℝ) ^ (2 * k + 3)) :=
        div_le_div_of_nonneg_right hnum hden
    _ = 4 / ((2 * (k : ℝ) + 3) * (N : ℝ) ^ (2 * k + 3)) := by
        have hp0 : (2 : ℝ) ^ (2 * k + 1) ≠ 0 := by positivity
        field_simp [hp0]

private theorem oddZetaRadiusTerm_add_two_le {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    oddZetaRadiusTerm N (k + 2) ≤ (4 / 7 : ℝ) / (N : ℝ) ^ 7 * (1 / (N : ℝ) ^ 2) ^ k := by
  have hb := oddZetaRadiusTerm_le hN (k + 2)
  have hexp : 2 * (k + 2) + 3 = 7 + 2 * k := by omega
  rw [hexp] at hb
  have hden : (7 : ℝ) * (N : ℝ) ^ (7 + 2 * k) ≤
      (2 * ((k + 2 : ℕ) : ℝ) + 3) * (N : ℝ) ^ (7 + 2 * k) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    push_cast
    linarith
  calc oddZetaRadiusTerm N (k + 2)
      ≤ 4 / ((2 * ((k + 2 : ℕ) : ℝ) + 3) * (N : ℝ) ^ (7 + 2 * k)) := hb
    _ ≤ 4 / (7 * (N : ℝ) ^ (7 + 2 * k)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = (4 / 7 : ℝ) / (N : ℝ) ^ 7 * (1 / (N : ℝ) ^ 2) ^ k := by
        rw [pow_add, pow_mul, one_div_pow]
        ring

private theorem tsum_oddZetaRadiusTerm_shift_two_bounds {N : ℕ} (hN : 2 ≤ N) :
    0 < ∑' k : ℕ, oddZetaRadiusTerm N (k + 2) ∧
      (∑' k : ℕ, oddZetaRadiusTerm N (k + 2)) ≤ (1 / 2 : ℝ) / (N : ℝ) ^ 6 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsum : Summable (oddZetaRadiusTerm N) :=
    (hasSum_log_gammaRadius_sub_div_of_two_le hN).summable
  have hsum2 : Summable fun k : ℕ ↦ oddZetaRadiusTerm N (k + 2) :=
    (summable_nat_add_iff 2).mpr hsum
  refine ⟨hsum2.tsum_pos (fun k ↦ (oddZetaRadiusTerm_pos hN (k + 2)).le) 0
    (oddZetaRadiusTerm_pos hN 2), ?_⟩
  have hr0 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
  have hr1 : 1 / (N : ℝ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hmaj : Summable fun k : ℕ ↦ (4 / 7 : ℝ) / (N : ℝ) ^ 7 * (1 / (N : ℝ) ^ 2) ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  calc ∑' k : ℕ, oddZetaRadiusTerm N (k + 2)
      ≤ ∑' k : ℕ, (4 / 7 : ℝ) / (N : ℝ) ^ 7 * (1 / (N : ℝ) ^ 2) ^ k :=
        hsum2.tsum_le_tsum (oddZetaRadiusTerm_add_two_le hN) hmaj
    _ = (4 / 7 : ℝ) / (N : ℝ) ^ 7 * (1 - 1 / (N : ℝ) ^ 2)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ (4 / 7 : ℝ) / (N : ℝ) ^ 7 * (4 / 3 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h14 : 1 / (N : ℝ) ^ 2 ≤ 1 / 4 :=
          one_div_le_one_div_of_le (by norm_num) (by nlinarith)
        have h43 : (4 / 3 : ℝ) = 1 / (3 / 4) := by norm_num
        rw [inv_eq_one_div, h43]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ ≤ (1 / 2 : ℝ) / (N : ℝ) ^ 6 := by
        have hN6_pos : 0 ≤ (N : ℝ) ^ 6 := by positivity
        have hN7 : 2 * (N : ℝ) ^ 6 ≤ (N : ℝ) ^ 7 := by
          have hp : (N : ℝ) ^ 7 = (N : ℝ) * (N : ℝ) ^ 6 := by ring
          rw [hp]
          exact mul_le_mul_of_nonneg_right hN2 hN6_pos
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith

private theorem gammaRadius_eq_rpow_mul_exp {N : ℕ} (hN : 2 ≤ N) :
    gammaRadius N =
      (16 : ℝ) ^ (1 / (N : ℝ)) * Real.exp (Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)) := by
  have hpos : 0 < gammaRadius N := gammaRadius_pos (by omega)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16), ← Real.exp_add]
  have hadd : Real.log 16 * (1 / (N : ℝ)) +
      (Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)) = Real.log (gammaRadius N) := by ring
  rw [hadd, Real.exp_log hpos]

private theorem log_gammaRadius_sub_div_eq_add_tail {N : ℕ} (hN : 2 ≤ N) :
    Real.log (gammaRadius N) - Real.log 16 / (N : ℝ) =
      oddZetaRadiusTerm N 0 + oddZetaRadiusTerm N 1 +
        ∑' k : ℕ, oddZetaRadiusTerm N (k + 2) := by
  have hhs : HasSum (oddZetaRadiusTerm N) (Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)) :=
    hasSum_log_gammaRadius_sub_div_of_two_le hN
  have hsplit := (hhs.summable.sum_add_tsum_nat_add 2).symm
  rw [hhs.tsum_eq] at hsplit
  simpa [Finset.sum_range_succ, add_assoc] using hsplit

private theorem log_gammaRadius_sub_div_bounds {N : ℕ} (hN : 2 ≤ N) :
    0 < Real.log (gammaRadius N) - Real.log 16 / (N : ℝ) ∧
      Real.log (gammaRadius N) - Real.log 16 / (N : ℝ) ≤ (3 / 2 : ℝ) / (N : ℝ) ^ 3 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by linarith
  obtain ⟨hRpos, hRle⟩ := tsum_oddZetaRadiusTerm_shift_two_bounds hN
  rw [log_gammaRadius_sub_div_eq_add_tail hN]
  refine ⟨by linarith [oddZetaRadiusTerm_pos hN 0, oddZetaRadiusTerm_pos hN 1, hRpos], ?_⟩
  have ht0 : oddZetaRadiusTerm N 0 ≤ 1 / (N : ℝ) ^ 3 := by
    rw [oddZetaRadiusTerm_zero, div_le_div_iff₀ (by positivity) (by positivity)]
    have hz3 : (riemannZeta 3).re ≤ 2 := (riemannZeta_re_lt_two (by norm_num)).le
    nlinarith [pow_pos hN0 3]
  have ht1 : oddZetaRadiusTerm N 1 ≤ (3 / 16 : ℝ) / (N : ℝ) ^ 3 := by
    rw [oddZetaRadiusTerm_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have hz5 : (riemannZeta 5).re ≤ 2 := (riemannZeta_re_lt_two (by norm_num)).le
    have hN5 : 4 * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 5 := by
      calc 4 * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = (N : ℝ) ^ 5 := by ring
    nlinarith [pow_pos hN0 3, pow_pos hN0 5]
  have hR3 : (∑' k : ℕ, oddZetaRadiusTerm N (k + 2)) ≤ (1 / 16 : ℝ) / (N : ℝ) ^ 3 := by
    have hN6 : 8 * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 6 := by
      calc 8 * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 * (N : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (N : ℝ)]) (by positivity)
        _ = (N : ℝ) ^ 6 := by ring
    refine hRle.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hN0 3]
  calc oddZetaRadiusTerm N 0 + oddZetaRadiusTerm N 1 + ∑' k : ℕ, oddZetaRadiusTerm N (k + 2)
      ≤ 1 / (N : ℝ) ^ 3 + (3 / 16 : ℝ) / (N : ℝ) ^ 3 + (1 / 16 : ℝ) / (N : ℝ) ^ 3 := by linarith
    _ ≤ (3 / 2 : ℝ) / (N : ℝ) ^ 3 := by
        rw [← add_div, ← add_div]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **Strict lower bound for `gammaRadius N`** (positivity of the `O(N ^ (-6))` remainder in
Calegari–Dimitrov–Tang (5.1.6)): for `2 ≤ N`, `gammaRadius N` strictly exceeds its two-term
odd-zeta truncation. -/
theorem mul_lt_gammaRadius {N : ℕ} (hN : 2 ≤ N) :
    (16 : ℝ) ^ (1 / (N : ℝ)) *
        (1 + (riemannZeta 3).re / (2 * (N : ℝ) ^ 3) +
          3 * (riemannZeta 5).re / (8 * (N : ℝ) ^ 5)) <
      gammaRadius N := by
  let S : ℝ := Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)
  have hS : S = oddZetaRadiusTerm N 0 + oddZetaRadiusTerm N 1 +
      ∑' k : ℕ, oddZetaRadiusTerm N (k + 2) := log_gammaRadius_sub_div_eq_add_tail hN
  have hRpos : 0 < ∑' k : ℕ, oddZetaRadiusTerm N (k + 2) :=
    (tsum_oddZetaRadiusTerm_shift_two_bounds hN).1
  have hexp : 1 + oddZetaRadiusTerm N 0 + oddZetaRadiusTerm N 1 < Real.exp S := by
    linarith [Real.add_one_le_exp S, hS, hRpos]
  rw [gammaRadius_eq_rpow_mul_exp hN, ← oddZetaRadiusTerm_zero, ← oddZetaRadiusTerm_one]
  exact mul_lt_mul_of_pos_left hexp (Real.rpow_pos_of_pos (by norm_num) _)

private theorem gammaRadius_le_mul_add_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    gammaRadius N ≤
      (16 : ℝ) ^ (1 / (N : ℝ)) *
        (1 + (riemannZeta 3).re / (2 * (N : ℝ) ^ 3) +
          3 * (riemannZeta 5).re / (8 * (N : ℝ) ^ 5) + 3 / (N : ℝ) ^ 6) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  let S : ℝ := Real.log (gammaRadius N) - Real.log 16 / (N : ℝ)
  let R : ℝ := ∑' k : ℕ, oddZetaRadiusTerm N (k + 2)
  have hS : S = oddZetaRadiusTerm N 0 + oddZetaRadiusTerm N 1 + R :=
    log_gammaRadius_sub_div_eq_add_tail hN
  have hRle : R ≤ (1 / 2 : ℝ) / (N : ℝ) ^ 6 := (tsum_oddZetaRadiusTerm_shift_two_bounds hN).2
  obtain ⟨hSpos, hSle⟩ := log_gammaRadius_sub_div_bounds hN
  have hS1 : |S| ≤ 1 := by
    rw [abs_of_pos hSpos]
    have hN3 : (8 : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg (N : ℝ)]
    refine hSle.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have hexp : Real.exp S ≤ 1 + S + S ^ 2 := by
    linarith [(abs_le.mp (Real.abs_exp_sub_one_sub_id_le hS1)).2]
  have hSsq : S ^ 2 ≤ (9 / 4 : ℝ) / (N : ℝ) ^ 6 := by
    calc S ^ 2 ≤ ((3 / 2 : ℝ) / (N : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ hSpos.le hSle 2
      _ = (9 / 4 : ℝ) / (N : ℝ) ^ 6 := by ring
  have hRS : R + S ^ 2 ≤ 3 / (N : ℝ) ^ 6 := by
    calc R + S ^ 2 ≤ (1 / 2 : ℝ) / (N : ℝ) ^ 6 + (9 / 4 : ℝ) / (N : ℝ) ^ 6 :=
          add_le_add hRle hSsq
      _ ≤ 3 / (N : ℝ) ^ 6 := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have htot : Real.exp S ≤
      1 + oddZetaRadiusTerm N 0 + oddZetaRadiusTerm N 1 + 3 / (N : ℝ) ^ 6 := by
    linarith [hexp, hS, hRS]
  rw [gammaRadius_eq_rpow_mul_exp hN, ← oddZetaRadiusTerm_zero, ← oddZetaRadiusTerm_one]
  exact mul_le_mul_of_nonneg_left htot (Real.rpow_pos_of_pos (by norm_num) _).le

/-- **Effective upper bound for `gammaRadius N`**: for every `N : ℕ` (nontrivially for `2 ≤ N`, and
by totalization at `N = 0, 1`), the remainder after the `N ^ (-3)` and `N ^ (-5)` odd-zeta terms is
at most `3 / N ^ 6`. -/
theorem gammaRadius_le_mul_add (N : ℕ) :
    gammaRadius N ≤
      (16 : ℝ) ^ (1 / (N : ℝ)) *
        (1 + (riemannZeta 3).re / (2 * (N : ℝ) ^ 3) +
          3 * (riemannZeta 5).re / (8 * (N : ℝ) ^ 5) + 3 / (N : ℝ) ^ 6) := by
  rcases N with _ | _ | N
  · simp
  · rw [gammaRadius_one]
    have hz3 : 0 < (riemannZeta 3).re := by
      simpa using riemannZeta_re_pos_of_one_lt (x := 3) (by norm_num)
    have hz5 : 0 < (riemannZeta 5).re := by
      simpa using riemannZeta_re_pos_of_one_lt (x := 5) (by norm_num)
    positivity
  · exact gammaRadius_le_mul_add_of_two_le (by omega)

/-- **Positive asymptotic expansion of `gammaRadius N`** (Calegari–Dimitrov–Tang (5.1.6)):
there is an explicit positive constant `C` (`C = 3` suffices) such that for every `N ≥ 2`,
`gammaRadius N = 16 ^ (1 / N) * (1 + Re ζ(3) / (2N ^ 3) + 3 Re ζ(5) / (8N ^ 5) + E)` with
`0 < E ≤ C / N ^ 6`. -/
theorem exists_pos_forall_gammaRadius_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∃ E : ℝ, 0 < E ∧ E ≤ C / (N : ℝ) ^ 6 ∧
      gammaRadius N = (16 : ℝ) ^ (1 / (N : ℝ)) *
        (1 + (riemannZeta (3 : ℂ)).re / (2 * (N : ℝ) ^ 3) +
          3 * (riemannZeta (5 : ℂ)).re / (8 * (N : ℝ) ^ 5) + E) := by
  refine ⟨3, by norm_num, fun N hN ↦ ?_⟩
  have h16 : 0 < (16 : ℝ) ^ (1 / (N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  let A : ℝ := 1 + (riemannZeta (3 : ℂ)).re / (2 * (N : ℝ) ^ 3) +
    3 * (riemannZeta (5 : ℂ)).re / (8 * (N : ℝ) ^ 5)
  refine ⟨gammaRadius N / (16 : ℝ) ^ (1 / (N : ℝ)) - A, ?_, ?_, ?_⟩
  · rw [sub_pos, lt_div_iff₀ h16, mul_comm]
    exact mul_lt_gammaRadius hN
  · rw [sub_le_iff_le_add', div_le_iff₀ h16, mul_comm]
    exact gammaRadius_le_mul_add N
  · dsimp [A]
    field_simp [h16.ne']
    ring

end TauCeti
