/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.SpecialFunctions.Gamma.Log
import TauCeti.Data.Nat.Cast.Basic

/-!
# Real digamma and its bounds on the positive real axis

This file defines the real digamma function `Real.digamma := logDeriv Real.Gamma`, the logarithmic
derivative of real Gamma, and relates it to Mathlib's `Complex.digamma`.

## Main declarations

* `Real.digamma`: the logarithmic derivative of `Real.Gamma`, with the total value `0` at the
  poles `0, -1, -2, ...`.
* `Complex.digamma_ofReal`: at every real point, complex digamma is the coercion of real digamma.
* `Real.hasDerivAt_log_Gamma`, `Real.digamma_eq_deriv_log_Gamma`: at every regular real point,
  real digamma is the derivative of `log ∘ Gamma`.
* `Real.digamma_one`, `Real.digamma_apply_add_one`, `Real.digamma_apply_add_nat`: the value
  `ψ(1) = -γ` and the recurrence `ψ(x + 1) = ψ(x) + 1 / x` with its iterates.
* `Real.digamma_le_log_le`: for `x > 0`, `ψ(x) ≤ log x ≤ ψ(x + 1)`.
* `Real.monotoneOn_digamma`: digamma is monotone on the positive real axis, being the derivative
  of the convex function `log ∘ Gamma`.
* `Real.differentiableAt_digamma`, `Real.deriv_digamma_apply_add_nat`, `Real.deriv_digamma_pos`:
  at every regular real point digamma is differentiable, its derivative satisfies the shifted
  recurrence `ψ'(x + n) = ψ'(x) - ∑_{k < n} 1 / (x + k)²`, and it is positive.
* `Real.digamma_one_half`, `Real.digamma_three_halves`, `Real.digamma_one_half_neg`,
  `Real.digamma_three_halves_pos`: the values `ψ(1/2) = -γ - 2 log 2 < 0` and
  `ψ(3/2) = 2 - γ - 2 log 2 > 0`.
* `Real.abs_digamma_sub_log_le`, `Complex.norm_digamma_ofReal_sub_log_le`,
  `Complex.isBigO_digamma_ofReal_sub_log`: for `x > 0`, `|ψ(x) - log x| ≤ 1 / x`, so complex
  digamma differs from the logarithm by `O(1 / x)` on the positive real axis.
* `TauCeti.contDiffOn_digamma_Ioi`, `TauCeti.iteratedDeriv_digamma_ofReal`: `C^∞` smoothness of
  `Real.digamma` on `(0, ∞)` and coercion of higher derivatives from `Complex.digamma`.

The positive-axis bounds come from the log-convexity of Gamma (Bohr–Mollerup): `ψ(x)` and
`ψ(x + 1)` are the derivatives of the convex function `log ∘ Gamma` at the endpoints of
`[x, x + 1]`, and its secant slope over that interval is `log x`.

## References

* T. Tao, [Mathlib PR #43556](https://github.com/leanprover-community/mathlib4/pull/43556),
  for the real digamma definition, recurrence, coercion and bound statements.
-/

public section

open Complex Filter Set Topology

namespace Real

/-- The real digamma function is the logarithmic derivative of real Gamma. -/
noncomputable def digamma : ℝ → ℝ := logDeriv Gamma

/-- The defining logarithmic-derivative formula for real digamma. -/
theorem digamma_def : digamma = logDeriv Gamma := (rfl)

end Real

namespace Complex

private theorem real_ne_neg_nat_of_pos {x : ℝ} (hx : 0 < x) :
    ∀ m : ℕ, x ≠ -(m : ℝ) := by
  intro m
  linarith

private theorem ofReal_ne_neg_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
  intro m hm
  exact hx m (by exact_mod_cast hm)

/-- At every regular real point, the complex Gamma derivative is the complex coercion
of the derivative of real Gamma. -/
theorem deriv_Gamma_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    deriv Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hpoles := ofReal_ne_neg_nat hx
  have hc := (differentiableAt_Gamma _ hpoles).hasDerivAt.comp_ofReal
  have hr := (Real.differentiableAt_Gamma hx).hasDerivAt.ofReal_comp
  have heq : (fun y : ℝ ↦ Gamma (y : ℂ)) = fun y ↦ (Real.Gamma y : ℂ) :=
    funext Gamma_ofReal
  rw [heq] at hc
  exact hc.unique hr

/-- At every real point, including the total zero values at poles, complex digamma
is the coercion of the real Gamma logarithmic derivative. -/
@[simp]
theorem digamma_ofReal {x : ℝ} :
    digamma (x : ℂ) = (Real.digamma x : ℂ) := by
  rw [Real.digamma_def]
  by_cases hx : ∀ m : ℕ, x ≠ -(m : ℝ)
  · rw [digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx, Gamma_ofReal, logDeriv_apply,
      ofReal_div]
  · push Not at hx
    obtain ⟨m, rfl⟩ := hx
    simp [digamma_def, logDeriv_apply, Gamma_neg_nat_eq_zero, Real.Gamma_neg_nat_eq_zero]

end Complex

namespace Real

/-- At every regular real point, the derivative of the real logarithm of Gamma is digamma. -/
theorem hasDerivAt_log_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    HasDerivAt (log ∘ Gamma) (digamma x) x := by
  simpa only [digamma_def, Function.comp_def, logDeriv_apply] using
    (differentiableAt_Gamma hx).hasDerivAt.log (Gamma_ne_zero hx)

/-- The real logarithm of Gamma is differentiable at every regular real point. -/
theorem differentiableAt_log_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    DifferentiableAt ℝ (log ∘ Gamma) x := (hasDerivAt_log_Gamma hx).differentiableAt

/-- Real digamma equals the derivative of the logarithm of Gamma at each regular point. -/
theorem digamma_eq_deriv_log_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma x = deriv (log ∘ Gamma) x := (hasDerivAt_log_Gamma hx).deriv.symm

/-- The value of real digamma at one is minus Euler's constant. -/
theorem digamma_one : digamma 1 = -eulerMascheroniConstant := by
  apply Complex.ofReal_injective
  push_cast
  simpa [← Complex.digamma_ofReal] using Complex.digamma_one

/-- Real digamma satisfies the Gamma recurrence at every regular real point. -/
theorem digamma_apply_add_one {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma (x + 1) = digamma x + 1 / x := by
  apply Complex.ofReal_injective
  push_cast
  simpa [← Complex.digamma_ofReal, one_div] using
    Complex.digamma_apply_add_one (x : ℂ) (Complex.ofReal_ne_neg_nat hx)

/-- The real digamma recurrence iterates over every natural shift. -/
theorem digamma_apply_add_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) (n : ℕ) :
    digamma (x + n) = digamma x + ∑ k ∈ Finset.range n, (x + k)⁻¹ := by
  apply Complex.ofReal_injective
  push_cast
  simpa [← Complex.digamma_ofReal] using
    Complex.digamma_apply_add_nat (Complex.ofReal_ne_neg_nat hx) n

private theorem log_Gamma_slope {x : ℝ} (hx : 0 < x) :
    slope (log ∘ Gamma) x (x + 1) = log x := by
  rw [slope_def_field, Function.comp_apply, Function.comp_apply,
    show x + 1 - x = 1 by ring, div_one,
    Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne']
  ring

/-- Positive real digamma lies below the logarithm, and its next shift lies above it. -/
theorem digamma_le_log_le {x : ℝ} (hx : 0 < x) :
    digamma x ≤ log x ∧ log x ≤ digamma (x + 1) := by
  have hu := convexOn_log_Gamma.le_slope_of_hasDerivAt (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : 0 < x + 1)) (by linarith)
    (hasDerivAt_log_Gamma (Complex.real_ne_neg_nat_of_pos hx))
  have hl := convexOn_log_Gamma.slope_le_of_hasDerivAt (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : 0 < x + 1)) (by linarith)
    (hasDerivAt_log_Gamma (Complex.real_ne_neg_nat_of_pos (by linarith : 0 < x + 1)))
  rw [log_Gamma_slope hx] at hu hl
  exact ⟨hu, hl⟩

/-- The explicit digamma error bound holds on the whole positive real axis. -/
theorem abs_digamma_sub_log_le {x : ℝ} (hx : 0 < x) : |digamma x - log x| ≤ 1 / x := by
  obtain ⟨hu, hl⟩ := digamma_le_log_le hx
  rw [digamma_apply_add_one (Complex.real_ne_neg_nat_of_pos hx)] at hl
  rw [abs_le]
  constructor <;> linarith

/-- Real digamma is monotone on the positive real axis. -/
theorem monotoneOn_digamma : MonotoneOn digamma (Ioi 0) := by
  -- Digamma is the derivative of `log ∘ Gamma`, which is convex by the Bohr–Mollerup theorem.
  have hd : EqOn digamma (deriv (log ∘ Gamma)) (Ioi 0) := fun x hx ↦
    digamma_eq_deriv_log_Gamma (Complex.real_ne_neg_nat_of_pos hx)
  exact (convexOn_log_Gamma.monotoneOn_deriv fun x hx ↦
    differentiableAt_log_Gamma (Complex.real_ne_neg_nat_of_pos hx)).congr hd.symm

/-- Real digamma is differentiable at every regular real point. -/
theorem differentiableAt_digamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    DifferentiableAt ℝ digamma x := by
  have hd := (Complex.analyticAt_digamma (Complex.ofReal_ne_neg_nat hx)).differentiableAt
  simpa [Complex.digamma_ofReal] using hd.hasDerivAt.real_of_complex.differentiableAt

/-- The derivative of the digamma recurrence: `ψ'(x + n) = ψ'(x) - ∑_{k < n} 1 / (x + k)²` at
every regular real point. -/
theorem deriv_digamma_apply_add_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) (n : ℕ) :
    deriv digamma (x + n) = deriv digamma x - ∑ k ∈ Finset.range n, ((x + k) ^ 2)⁻¹ := by
  have hxn := TauCeti.add_natCast_ne_neg_natCast hx n
  have hk : ∀ k ∈ Finset.range n, x + k ≠ 0 := fun k _ h => hx k (by linarith)
  have h := ((differentiableAt_digamma hx).hasDerivAt.add (HasDerivAt.fun_sum
    (u := Finset.range n) fun (k : ℕ) hk' =>
      ((hasDerivAt_id x).add_const (k : ℝ)).inv (hk k hk'))).unique
    (((differentiableAt_digamma hxn).hasDerivAt.comp_add_const x (n : ℝ)).congr_of_eventuallyEq
      (by
        filter_upwards [eventually_ne_neg_natCast hx] with y hy
        simp only [Pi.add_apply, Pi.inv_apply, id]
        exact (digamma_apply_add_nat hy n).symm))
  simp only [id, div_eq_mul_inv, neg_one_mul, Finset.sum_neg_distrib] at h
  linarith

/-- The derivative of real digamma (trigamma) is positive at every regular real point. -/
theorem deriv_digamma_pos {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) : 0 < deriv digamma x := by
  -- Shift by `n ≥ 1` into the positive axis; the recurrence sum then contains `(x ^ 2)⁻¹ > 0`.
  obtain ⟨n, hn⟩ := exists_nat_gt (max (-x) 0)
  have hpos : 0 < x + n := by linarith [le_max_left (-x) 0]
  have h := deriv_digamma_apply_add_nat hx n
  have hmono : 0 ≤ deriv digamma (x + n) := by
    rw [← derivWithin_of_isOpen isOpen_Ioi (Set.mem_Ioi.2 hpos)]
    exact monotoneOn_digamma.derivWithin_nonneg
  have hsum : 0 < ∑ k ∈ Finset.range n, ((x + k) ^ 2)⁻¹ :=
    Finset.sum_pos (fun k _ => inv_pos.2 (sq_pos_iff.2 fun h => hx k (by linarith)))
      ⟨0, Finset.mem_range.2 (by exact_mod_cast (le_max_right (-x) 0).trans_lt hn)⟩
  linarith

/-- The value `ψ(1/2) = -γ - 2 log 2`. -/
theorem digamma_one_half : digamma (1 / 2) = -eulerMascheroniConstant - 2 * log 2 := by
  apply Complex.ofReal_injective
  push_cast [← Complex.digamma_ofReal, Complex.ofReal_log zero_le_two]
  rw [Complex.digamma_one_half]
  ring

/-- `ψ(1/2) = -γ - 2 log 2` is negative. -/
theorem digamma_one_half_neg : digamma (1 / 2) < 0 := by
  rw [digamma_one_half]
  linarith [one_half_lt_eulerMascheroniConstant, log_pos one_lt_two]

/-- The value `ψ(3/2) = 2 - γ - 2 log 2`. -/
theorem digamma_three_halves : digamma (3 / 2) = 2 - eulerMascheroniConstant - 2 * log 2 := by
  -- `ψ(1/2 + 1) = ψ(1/2) + 2`.
  have h : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
  rw [h, digamma_apply_add_one (Complex.real_ne_neg_nat_of_pos one_half_pos), digamma_one_half]
  ring

/-- Euler's constant satisfies `γ + 2 log 2 < 2`. With `γ ≈ 0.57722` the gap is about
`0.03649`. -/
theorem eulerMascheroniConstant_add_two_mul_log_two_lt_two :
    eulerMascheroniConstant + 2 * log 2 < 2 := by
  -- `γ < harmonic 16 - log 16` and `log 2 > 0.6931471803` suffice.
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 16
  have h16 : eulerMascheroniSeq' 16 = (harmonic 16 : ℝ) - 4 * log 2 := by
    have h24 : ((16 : ℕ) : ℝ) = 2 ^ 4 := by norm_num
    rw [eulerMascheroniSeq', h24, log_pow]
    norm_num
  have hH : (harmonic 16 : ℝ) = 2436559 / 720720 := by
    rw [harmonic]
    norm_num [Finset.sum_range_succ]
  have hlog := log_two_gt_d9
  rw [h16, hH] at h
  norm_num at h hlog
  linarith

/-- `ψ(3/2) = 2 - γ - 2 log 2` is positive. -/
theorem digamma_three_halves_pos : 0 < digamma (3 / 2) := by
  rw [digamma_three_halves]
  linarith [eulerMascheroniConstant_add_two_mul_log_two_lt_two]

end Real

namespace Complex

/-- An explicit error bound for complex digamma on the positive real axis. -/
theorem norm_digamma_ofReal_sub_log_le {x : ℝ} (hx : 0 < x) :
    ‖digamma (x : ℂ) - log (x : ℂ)‖ ≤ x⁻¹ := by
  rw [digamma_ofReal, ← ofReal_log hx.le, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  simpa only [one_div] using Real.abs_digamma_sub_log_le hx

/-- Complex digamma differs from the principal logarithm by `O(1 / x)` on the positive axis. -/
theorem isBigO_digamma_ofReal_sub_log :
    (fun x : ℝ ↦ digamma (x : ℂ) - log (x : ℂ)) =O[atTop] (fun x : ℝ ↦ x⁻¹) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)] using
    norm_digamma_ofReal_sub_log_le hx

end Complex

namespace TauCeti

open scoped ContDiff

/-- Real digamma is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_digamma_Ioi : ContDiffOn ℝ ∞ Real.digamma (Ioi 0) :=
  differentiableOn_digamma_slitPlane.contDiffOn_ofReal isOpen_slitPlane
    (fun _ ht ↦ ofReal_mem_slitPlane.mpr ht) fun _ _ ↦ Complex.digamma_ofReal

/-- On `(0, ∞)`, every complex iterated derivative of `Complex.digamma` is the coercion of the
corresponding real iterated derivative of `Real.digamma`. -/
@[simp]
theorem iteratedDeriv_digamma_ofReal (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k Complex.digamma (x : ℂ) = ((iteratedDeriv k Real.digamma x : ℝ) : ℂ) :=
  differentiableOn_digamma_slitPlane.iteratedDeriv_ofReal isOpen_slitPlane isOpen_Ioi
    (fun _ ht ↦ ofReal_mem_slitPlane.mpr ht) (fun _ _ ↦ Complex.digamma_ofReal) k hx

end TauCeti
