/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# Taylor series of digamma and `logGamma` at `1`

On the open unit disc `‖z‖ < 1`, expanding each paired summand of Gauss' digamma series in powers
of `z / (n + 1)` and interchanging the double sum expresses `Complex.digamma (1 + z)` in terms of
Euler's constant `γ` and the integer zeta values `riemannZeta (k + 2)`:
`ψ(1 + z) = -γ + ∑' k, (-1) ^ k * ζ(k + 2) * z ^ (k + 1)`.
Integrating termwise on subdiscs of the unit disc and matching values at `z = 0` via
`TauCeti.logGamma_one` yields the power series of the normalized holomorphic branch
`TauCeti.logGamma (1 + z)`:
`logGamma (1 + z) = -γ * z + ∑' k, (-1) ^ k * ζ(k + 2) * z ^ (k + 2) / (k + 2)`.
Restricting to `x ∈ (-1, 1)` gives the corresponding real Taylor expansions for
`Real.digamma (1 + x)` and `Real.log (Real.Gamma (1 + x))`.

## Main results

* `Complex.hasSum_digamma_one_add_add_eulerMascheroniConstant` and
  `Complex.digamma_one_add_eq_neg_eulerMascheroniConstant_add_tsum`: Taylor expansion of
  `Complex.digamma (1 + z)` for `‖z‖ < 1`.
* `Real.hasSum_digamma_one_add_add_eulerMascheroniConstant` and
  `Real.digamma_one_add_eq_neg_eulerMascheroniConstant_add_tsum`: Taylor expansion of
  `Real.digamma (1 + x)` for `|x| < 1`.
* `TauCeti.hasSum_logGamma_one_add_add_eulerMascheroniConstant_mul` and
  `TauCeti.logGamma_one_add_eq_neg_eulerMascheroniConstant_mul_add_tsum`: Taylor expansion of
  `TauCeti.logGamma (1 + z)` for `‖z‖ < 1`.
* `Real.hasSum_log_Gamma_one_add_add_eulerMascheroniConstant_mul` and
  `Real.log_Gamma_one_add_eq_neg_eulerMascheroniConstant_mul_add_tsum`: Taylor expansion of
  `Real.log (Real.Gamma (1 + x))` for `|x| < 1`.

## References

* [NIST DLMF, equations 5.7.3 and 5.7.4](https://dlmf.nist.gov/5.7).
* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), proof of Theorem 5.1.4.
-/

public section

open Complex Metric

private theorem riemannZeta_nat_add_two_eq_ofReal (k : ℕ) :
    riemannZeta (k + 2) = ((riemannZeta (k + 2)).re : ℂ) := by
  have hcast : ((k : ℂ) + 2) = (((k : ℝ) + 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have him : (riemannZeta (k + 2)).im = 0 := by
    rw [hcast]
    exact riemannZeta_im_eq_zero_of_one_lt (by linarith)
  exact Complex.ext rfl him

namespace Complex

private theorem hasSum_gaussTerm_geometric {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * z ^ (k + 1) / ((n : ℂ) + 1) ^ (k + 2))
      (1 / ((n : ℂ) + 1) - 1 / (1 + z + n)) := by
  let w : ℂ := -z / ((n : ℂ) + 1)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hw : ‖w‖ < 1 := by
    rw [norm_div, norm_neg, ← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
    exact (div_le_self (norm_nonneg z) hn1).trans_lt hz
  have hn0 : (n : ℂ) + 1 ≠ 0 := n.cast_add_one_ne_zero
  have hzn0 : 1 + z + (n : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hzre : -‖z‖ ≤ z.re := neg_le_of_abs_le (abs_re_le_norm z)
    simp only [add_re, one_re, natCast_re, zero_re] at hre
    linarith
  have h1w : 1 - w = (1 + z + n) / ((n : ℂ) + 1) := by
    dsimp [w]
    field_simp [hn0]
    ring
  have htarget : z / ((n : ℂ) + 1) ^ 2 * (1 - w)⁻¹ =
      1 / ((n : ℂ) + 1) - 1 / (1 + z + n) := by
    rw [h1w, inv_div]
    field_simp [hn0, hzn0]
    ring
  have hgeom := (hasSum_geometric_of_norm_lt_one hw).mul_left (z / ((n : ℂ) + 1) ^ 2)
  rw [htarget] at hgeom
  refine hgeom.congr_fun fun k ↦ ?_
  have hwk : w ^ k = (-1) ^ k * z ^ k / ((n : ℂ) + 1) ^ k := by
    have hw' : w = (-1 * z) / ((n : ℂ) + 1) := by dsimp [w]; ring
    rw [hw', div_pow, mul_pow]
  rw [hwk, pow_succ, pow_add]
  field_simp [hn0]

private theorem summable_uncurry_digamma_double {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (Function.uncurry fun n k : ℕ ↦
      (-1) ^ k * z ^ (k + 1) / ((n : ℂ) + 1) ^ (k + 2)) := by
  have hu : Summable fun n : ℕ ↦ ‖1 / ((n : ℝ) + 1) ^ 2‖ := by
    have hs : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2 := by
      simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact hs.norm
  have hv : Summable fun k : ℕ ↦ ‖‖z‖ ^ (k + 1)‖ :=
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖).congr
      (fun k ↦ by rw [pow_succ']) |>.norm
  have hmul : Summable fun p : ℕ × ℕ ↦ (1 / ((p.1 : ℝ) + 1) ^ 2) * ‖z‖ ^ (p.2 + 1) :=
    summable_mul_of_summable_norm hu hv
  refine hmul.of_norm_bounded fun ⟨n, k⟩ ↦ ?_
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by simpa using Complex.norm_natCast (n + 1)
  simp only [Function.uncurry_apply_pair, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, hnorm]
  have hpow : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ (k + 2) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow

private theorem hasSum_zeta_pow_term (z : ℂ) (k : ℕ) :
    HasSum (fun n : ℕ ↦ (-1) ^ k * z ^ (k + 1) / ((n : ℂ) + 1) ^ (k + 2))
      ((-1) ^ k * riemannZeta (k + 2) * z ^ (k + 1)) := by
  have hsum_real : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ (k + 2) := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega))
  have hsum : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ (k + 2) := by
    refine .of_norm_bounded hsum_real fun n ↦ ?_
    have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by simpa using Complex.norm_natCast (n + 1)
    simp [hnorm]
  have hzeta : riemannZeta (k + 2) = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (k + 2) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith)]
    refine tsum_congr fun n ↦ ?_
    have hcast : ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, cpow_natCast]
  have h1 : HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ (k + 2)) (riemannZeta (k + 2)) := by
    rw [hzeta]
    exact hsum.hasSum
  simpa [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using
    h1.mul_left ((-1) ^ k * z ^ (k + 1))

/-- **Taylor series of complex digamma at `1`** (DLMF 5.7.4): for `‖z‖ < 1`,
`ψ(1 + z) + γ = ∑_{k ≥ 0} (-1) ^ k ζ(k + 2) z ^ (k + 1)`. -/
theorem hasSum_digamma_one_add_add_eulerMascheroniConstant {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * riemannZeta (k + 2) * z ^ (k + 1))
      (digamma (1 + z) + Real.eulerMascheroniConstant) := by
  have hdouble := (summable_uncurry_digamma_double hz).hasSum
  have hrow := hdouble.prod_fiberwise (hasSum_gaussTerm_geometric hz)
  have hcol := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hdouble).prod_fiberwise
    (hasSum_zeta_pow_term z)
  have hpoles : ∀ m : ℕ, 1 + z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    have hzre : -‖z‖ ≤ z.re := neg_le_of_abs_le (abs_re_le_norm z)
    simp only [add_re, one_re, neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hgauss : HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) - 1 / (1 + z + n))
      (digamma (1 + z) + Real.eulerMascheroniConstant) := by
    have heq := digamma_eq_gaussSeries hpoles
    have htsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (1 + z + n)) =
        digamma (1 + z) + Real.eulerMascheroniConstant := by
      linear_combination -heq
    rw [← htsum]
    exact (summable_gaussSeries (1 + z)).hasSum
  rwa [hrow.unique hgauss] at hcol

/-- **Taylor series of complex digamma at `1`**, written with `tsum`. -/
theorem digamma_one_add_eq_neg_eulerMascheroniConstant_add_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    digamma (1 + z) =
      -Real.eulerMascheroniConstant +
        ∑' k : ℕ, (-1) ^ k * riemannZeta (k + 2) * z ^ (k + 1) := by
  have h := (hasSum_digamma_one_add_add_eulerMascheroniConstant hz).tsum_eq
  linear_combination -h

end Complex

namespace Real

/-- **Taylor series of real digamma at `1`**: for `|x| < 1`,
`ψ(1 + x) + γ = ∑_{k ≥ 0} (-1) ^ k Re(ζ(k + 2)) x ^ (k + 1)`. -/
theorem hasSum_digamma_one_add_add_eulerMascheroniConstant {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * (riemannZeta (k + 2)).re * x ^ (k + 1))
      (digamma (1 + x) + eulerMascheroniConstant) := by
  have hxc : ‖(x : ℂ)‖ < 1 := by simpa [Complex.norm_real] using hx
  have hc := Complex.reCLM.hasSum
    (Complex.hasSum_digamma_one_add_add_eulerMascheroniConstant hxc)
  have htarget : Complex.reCLM (Complex.digamma (1 + (x : ℂ)) + eulerMascheroniConstant) =
      digamma (1 + x) + eulerMascheroniConstant := by
    have h1 : (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by push_cast; rfl
    rw [h1, Complex.digamma_ofReal]
    simp
  rw [htarget] at hc
  refine hc.congr_fun fun k ↦ ?_
  have hterm : (-1 : ℂ) ^ k * riemannZeta (k + 2) * (x : ℂ) ^ (k + 1) =
      (((-1 : ℝ) ^ k * (riemannZeta (k + 2)).re * x ^ (k + 1) : ℝ) : ℂ) := by
    rw [riemannZeta_nat_add_two_eq_ofReal]
    push_cast
    rfl
  rw [hterm, Complex.reCLM_apply, Complex.ofReal_re]

/-- **Taylor series of real digamma at `1`**, written with `tsum`. -/
theorem digamma_one_add_eq_neg_eulerMascheroniConstant_add_tsum {x : ℝ} (hx : |x| < 1) :
    digamma (1 + x) =
      -eulerMascheroniConstant +
        ∑' k : ℕ, (-1) ^ k * (riemannZeta (k + 2)).re * x ^ (k + 1) := by
  have h := (hasSum_digamma_one_add_add_eulerMascheroniConstant hx).tsum_eq
  linear_combination -h

end Real

namespace TauCeti

private noncomputable def logGammaSeriesTerm (k : ℕ) (z : ℂ) : ℂ :=
  (-1) ^ k * riemannZeta (k + 2) * z ^ (k + 2) / (k + 2)

private theorem summable_logGammaSeriesTerm {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ ↦ logGammaSeriesTerm k z := by
  have hgeom : Summable fun k : ℕ ↦ 2 * ‖z‖ ^ (k + 2) :=
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (2 * ‖z‖ ^ 2)).congr
      fun k ↦ by ring
  refine hgeom.of_norm_bounded fun k ↦ ?_
  dsimp [logGammaSeriesTerm]
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  have hk : (1 : ℝ) ≤ ‖(k : ℂ) + 2‖ := by
    have hc : (k : ℂ) + 2 = ((k + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_natCast]
    exact_mod_cast (by omega : 1 ≤ k + 2)
  calc ‖riemannZeta (k + 2)‖ * ‖z‖ ^ (k + 2) / ‖(k : ℂ) + 2‖
      ≤ ‖riemannZeta (k + 2)‖ * ‖z‖ ^ (k + 2) := div_le_self (by positivity) hk
    _ ≤ 2 * ‖z‖ ^ (k + 2) :=
      mul_le_mul_of_nonneg_right (norm_riemannZeta_lt_two (by simp)).le (by positivity)

private theorem hasDerivAt_logGammaSeriesTerm (k : ℕ) (w : ℂ) :
    HasDerivAt (logGammaSeriesTerm k) ((-1) ^ k * riemannZeta (k + 2) * w ^ (k + 1)) w := by
  have hk0 : (k : ℂ) + 2 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (k + 1)
  have hpow : HasDerivAt (fun z : ℂ ↦ ((-1) ^ k * riemannZeta (k + 2) / (k + 2)) * z ^ (k + 2))
      (((-1) ^ k * riemannZeta (k + 2) / (k + 2)) * ((k + 2 : ℕ) * w ^ (k + 1))) w := by
    simpa [Nat.add_sub_cancel] using
      (hasDerivAt_pow (k + 2) w).const_mul ((-1) ^ k * riemannZeta (k + 2) / (k + 2))
  have hfun : (fun z : ℂ ↦ ((-1) ^ k * riemannZeta (k + 2) / (k + 2)) * z ^ (k + 2)) =
      logGammaSeriesTerm k := by
    ext z
    dsimp [logGammaSeriesTerm]
    ring
  have hval : ((-1) ^ k * riemannZeta (k + 2) / (k + 2)) * ((k + 2 : ℕ) * w ^ (k + 1)) =
      (-1) ^ k * riemannZeta (k + 2) * w ^ (k + 1) := by
    push_cast
    field_simp [hk0]
  rwa [hfun, hval] at hpow

private theorem hasDerivAt_tsum_logGammaSeriesTerm {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    HasDerivAt (fun z : ℂ ↦ ∑' k : ℕ, logGammaSeriesTerm k z)
      (Complex.digamma (1 + w) + Real.eulerMascheroniConstant) w := by
  have hu : Summable fun k : ℕ ↦ 2 * r ^ (k + 1) :=
    ((summable_geometric_of_lt_one hr0.le hr1).mul_left (2 * r)).congr fun k ↦ by ring
  have h0 : Summable fun k : ℕ ↦ logGammaSeriesTerm k 0 :=
    summable_logGammaSeriesTerm (by norm_num)
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    (fun k y _ ↦ hasDerivAt_logGammaSeriesTerm k y)
    (fun k y hy ↦ by
      have hyr : ‖y‖ ≤ r := le_of_lt (by simpa using hy)
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      exact mul_le_mul (norm_riemannZeta_lt_two (by simp)).le
        (pow_le_pow_left₀ (norm_nonneg y) hyr (k + 1)) (by positivity) (by positivity))
    (mem_ball_self hr0) h0 hw
  have hw1 : ‖w‖ < 1 := (by simpa using hw : ‖w‖ < r).trans hr1
  rwa [(Complex.hasSum_digamma_one_add_add_eulerMascheroniConstant hw1).tsum_eq] at hd

private theorem hasDerivAt_logGamma_one_add_linear {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (fun z : ℂ ↦ logGamma (1 + z) + Real.eulerMascheroniConstant * z)
      (Complex.digamma (1 + w) + Real.eulerMascheroniConstant) w := by
  have hslit : 1 + w ∈ slitPlane := mem_slitPlane_of_norm_lt_one hw
  have hdiff : DifferentiableAt ℂ logGamma (1 + w) :=
    differentiableOn_logGamma.differentiableAt (isOpen_slitPlane.mem_nhds hslit)
  have hcomp := hdiff.hasDerivAt.comp w ((hasDerivAt_id w).const_add 1)
  rw [Function.comp_def, deriv_logGamma hslit, mul_one] at hcomp
  have h2 : HasDerivAt (fun z : ℂ ↦ (Real.eulerMascheroniConstant : ℂ) * z)
      Real.eulerMascheroniConstant w := by
    simpa using (hasDerivAt_id w).const_mul (Real.eulerMascheroniConstant : ℂ)
  exact hcomp.fun_add h2

/-- **Taylor series of `logGamma` at `1`** (DLMF 5.7.3): for `‖z‖ < 1`,
`logGamma (1 + z) + γ z = ∑_{k ≥ 0} (-1) ^ k ζ(k + 2) z ^ (k + 2) / (k + 2)`. -/
theorem hasSum_logGamma_one_add_add_eulerMascheroniConstant_mul {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * riemannZeta (k + 2) * z ^ (k + 2) / (k + 2))
      (logGamma (1 + z) + Real.eulerMascheroniConstant * z) := by
  let r : ℝ := (‖z‖ + 1) / 2
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hzr : z ∈ ball (0 : ℂ) r := by
    simp only [mem_ball, dist_zero_right, r]
    linarith
  let D : ℂ → ℂ := fun w ↦
    (logGamma (1 + w) + Real.eulerMascheroniConstant * w) - ∑' k : ℕ, logGammaSeriesTerm k w
  have hD : ∀ w ∈ ball (0 : ℂ) r, HasDerivAt D 0 w := fun w hw ↦ by
    have hw1 : ‖w‖ < 1 := (by simpa using hw : ‖w‖ < r).trans hr1
    simpa only [sub_self] using (hasDerivAt_logGamma_one_add_linear hw1).fun_sub
      (hasDerivAt_tsum_logGammaSeriesTerm hr0 hr1 hw)
  have hconst : D z = D 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun w hw ↦ (hD w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hD w hw).deriv) hzr (mem_ball_self hr0)
  have hD0 : D 0 = 0 := by
    simp [D, logGammaSeriesTerm]
  have heq : ∑' k : ℕ, logGammaSeriesTerm k z =
      logGamma (1 + z) + Real.eulerMascheroniConstant * z :=
    (sub_eq_zero.mp (hconst.trans hD0)).symm
  rw [← heq]
  exact (summable_logGammaSeriesTerm hz).hasSum

/-- **Taylor series of `logGamma` at `1`**, written with `tsum`. -/
theorem logGamma_one_add_eq_neg_eulerMascheroniConstant_mul_add_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    logGamma (1 + z) =
      -Real.eulerMascheroniConstant * z +
        ∑' k : ℕ, (-1) ^ k * riemannZeta (k + 2) * z ^ (k + 2) / (k + 2) := by
  have h := (hasSum_logGamma_one_add_add_eulerMascheroniConstant_mul hz).tsum_eq
  linear_combination -h

end TauCeti

namespace Real

/-- **Taylor series of `log (Gamma (1 + x))` at `0`** (DLMF 5.7.3): for `|x| < 1`,
`log (Gamma (1 + x)) + γ x = ∑_{k ≥ 0} (-1) ^ k Re(ζ(k + 2)) x ^ (k + 2) / (k + 2)`. -/
theorem hasSum_log_Gamma_one_add_add_eulerMascheroniConstant_mul {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * (riemannZeta (k + 2)).re * x ^ (k + 2) / (k + 2))
      (log (Gamma (1 + x)) + eulerMascheroniConstant * x) := by
  have hxc : ‖(x : ℂ)‖ < 1 := by simpa [Complex.norm_real] using hx
  have hxpos : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have hc := Complex.reCLM.hasSum
    (TauCeti.hasSum_logGamma_one_add_add_eulerMascheroniConstant_mul hxc)
  have htarget :
      Complex.reCLM (TauCeti.logGamma (1 + (x : ℂ)) + eulerMascheroniConstant * (x : ℂ)) =
        log (Gamma (1 + x)) + eulerMascheroniConstant * x := by
    have h1 : (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by push_cast; rfl
    rw [h1, TauCeti.logGamma_ofReal hxpos]
    simp
  rw [htarget] at hc
  refine hc.congr_fun fun k ↦ ?_
  have hterm : (-1 : ℂ) ^ k * riemannZeta (k + 2) * (x : ℂ) ^ (k + 2) / (k + 2) =
      (((-1 : ℝ) ^ k * (riemannZeta (k + 2)).re * x ^ (k + 2) / (k + 2) : ℝ) : ℂ) := by
    rw [riemannZeta_nat_add_two_eq_ofReal]
    push_cast
    rfl
  rw [hterm, Complex.reCLM_apply, Complex.ofReal_re]

/-- **Taylor series of `log (Gamma (1 + x))` at `0`**, written with `tsum`. -/
theorem log_Gamma_one_add_eq_neg_eulerMascheroniConstant_mul_add_tsum {x : ℝ} (hx : |x| < 1) :
    log (Gamma (1 + x)) =
      -eulerMascheroniConstant * x +
        ∑' k : ℕ, (-1) ^ k * (riemannZeta (k + 2)).re * x ^ (k + 2) / (k + 2) := by
  have h := (hasSum_log_Gamma_one_add_add_eulerMascheroniConstant_mul hx).tsum_eq
  linear_combination -h

end Real
