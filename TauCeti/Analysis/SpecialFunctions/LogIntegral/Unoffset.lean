/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Bounds

/-!
# The unoffset logarithmic integral

This file defines the unoffset logarithmic integral

`li x = γ + log |log x| + ∑_{n ≥ 1} (log x)ⁿ / (n · n!)`,

where `γ` is the Euler–Mascheroni constant. It is the exponential integral `Ei` evaluated at
`log x`, and for `x > 1` it is the Cauchy principal value of `∫₀ˣ dt / log t`; that identity, which
needs `li x → 0` as `x → 0⁺`, is not proved here. Mathlib's `log` is `log |·|`, so the body is the
series for every `x > 0` with `x ≠ 1`; the value at `x = 1` is junk.
The series converges absolutely for every real `log x`, its terms being at most `|log x|ⁿ / n!`.

The function `li` is the normalisation of the logarithmic integral used in the explicit forms of
the prime number theorem of Schoenfeld, Büthe and later authors, for instance
`|π(x) - li x| < √x log x / (8π)` under the Riemann hypothesis. It differs from the offset
logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` (`TauCeti.Real.logIntegral`) by the constant
`li 2` on `(1, ∞)`, so that bounds stated with either normalisation convert into each other.

Termwise differentiation of the series gives `(e^y - 1) / y` at `y = log x`
(`Real.tsum_pow_div_factorial_succ`), and the chain rule
then gives `li' x = (log x)⁻¹` on `(0, 1)` and on `(1, ∞)`. Hence `li` is an antiderivative of
`(log t)⁻¹` on both intervals: it is strictly decreasing on `(0, 1)`, strictly increasing on
`(1, ∞)`, tends to `-∞` at `1` from either side and to `+∞` at infinity. From the lower bounds
`γ > 1 / 2` (Mathlib), `log (3 / 2) > 2 / 5` (`Real.two_fifths_lt_log_three_halves`) and the
first two terms of the series one gets
`li (3 / 2) > 0`, so `li` has exactly one zero in `(1, ∞)`, Soldner's constant, and it lies in
`(1, 3 / 2)`.

## Main declarations

* `TauCeti.Real.li`: the unoffset logarithmic integral, with defining equation `li_def`.
* `TauCeti.Real.liSeries`: its entire part `∑_{n ≥ 1} yⁿ / (n · n!)`, with defining equation
  `TauCeti.Real.liSeries_def`, `TauCeti.Real.li_eq_add_liSeries`, the summability
  `TauCeti.Real.summable_liSeries` and `TauCeti.Real.hasSum_liSeries`, the
  partial-sum lower bound `TauCeti.Real.sum_range_le_liSeries` for `y ≥ 0`, and the derivative
  `TauCeti.Real.hasDerivAt_liSeries`, which is `(e^y - 1) / y` for `y ≠ 0`
  (`TauCeti.Real.hasDerivAt_liSeries_of_ne_zero`) and `1` at `0`
  (`TauCeti.Real.hasDerivAt_liSeries_zero`).
* `TauCeti.Real.hasDerivAt_li`: `li' x = (log x)⁻¹` for `0 < x ≠ 1`.
* `TauCeti.Real.integral_inv_log_eq_li_sub_li`,
  `TauCeti.Real.integral_inv_log_eq_li_sub_li_of_lt_one`: `∫ t in a..b, (log t)⁻¹ = li b - li a`
  when `a` and `b` both lie in `(1, ∞)` or both in `(0, 1)`.
* `TauCeti.Real.logIntegral_eq_li_sub_li_two`: `Li x = li x - li 2` for `x > 1`.
* `TauCeti.Real.strictMonoOn_li`, `TauCeti.Real.strictAntiOn_li`: the monotonicity of `li` on
  `(1, ∞)` and on `(0, 1)`.
* `TauCeti.Real.tendsto_li_nhdsNE_one`, `TauCeti.Real.tendsto_li_atTop`: `li x → -∞` as `x → 1`,
  and `li x → +∞` as `x → ∞`.
* `TauCeti.Real.li_pos`: `0 < li x` for every `x ≥ 3 / 2`.
* `TauCeti.Real.existsUnique_li_eq_zero`: `li` has exactly one zero in `(1, ∞)`, Soldner's
  constant, and `TauCeti.Real.lt_three_halves_of_li_eq_zero` locates it below `3 / 2`.

## References

* L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
  (1976), 337–360, where `li` is the normalisation of the bounds under the Riemann hypothesis.
* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §5.1, formulas 5.1.3
  and 5.1.10, for `li x = Ei (log x)` and the series of `Ei`.
-/

public section

namespace TauCeti.Real

open Filter Set
open _root_.Real
open scoped Nat Topology

/-- The **unoffset logarithmic integral**
`li x = γ + log |log x| + ∑_{n ≥ 1} (log x)ⁿ / (n · n!)`, the exponential integral `Ei` at
`log x`.

For `x > 1` it is the Cauchy principal value of `∫₀ˣ dt / log t`, and it differs from the offset
logarithmic integral `TauCeti.Real.logIntegral` by `li 2` there
(`TauCeti.Real.logIntegral_eq_li_sub_li_two`). Mathlib's `log` is `log |·|`, so `log (log x)` is
`log |log x|`; the value at `x = 1` is the junk value `γ`. -/
noncomputable def li (x : ℝ) : ℝ :=
  eulerMascheroniConstant + log (log x) +
    ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `TauCeti.Real.li`. -/
theorem li_def (x : ℝ) :
    li x = eulerMascheroniConstant + log (log x) +
      ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-! ### The series `∑_{n ≥ 1} yⁿ / (n · n!)` -/

/-- The entire part `∑_{n ≥ 1} yⁿ / (n · n!)` of the exponential integral, so that
`li x = γ + log |log x| + liSeries (log x)`. -/
noncomputable def liSeries (y : ℝ) : ℝ :=
  ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `TauCeti.Real.liSeries`. -/
theorem liSeries_def (y : ℝ) :
    liSeries y = ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-- `li x = γ + log |log x| + liSeries (log x)`. -/
theorem li_eq_add_liSeries (x : ℝ) :
    li x = eulerMascheroniConstant + log (log x) + liSeries (log x) := (rfl)

/-- The series `liSeries y` converges absolutely for every real `y`; at `y = log x` its terms are
those of `li_def`. -/
theorem summable_liSeries (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  refine .of_norm_bounded ((summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial |y|))
    fun n ↦ ?_
  have hf : (0 : ℝ) < (n + 1)! := mod_cast (n + 1).factorial_pos
  rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (by positivity) hf (le_mul_of_one_le_left hf.le (by simp))

/-- The series `∑_{n ≥ 1} yⁿ / (n · n!)` sums to `liSeries y`. -/
theorem hasSum_liSeries (y : ℝ) :
    HasSum (fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) (liSeries y) :=
  (summable_liSeries y).hasSum

/-- The termwise derivative `∑_{n ≥ 0} yⁿ / (n + 1)!` of `liSeries`. -/
theorem hasDerivAt_liSeries (y : ℝ) :
    HasDerivAt liSeries (∑' n : ℕ, y ^ n / ((n + 1)! : ℝ)) y := by
  set R : ℝ := |y| + 1
  have hR : 0 < R := by positivity
  unfold liSeries
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n ↦ R ^ n / (n ! : ℝ))
    (g' := fun n z ↦ z ^ n / ((n + 1)! : ℝ))
    (Real.summable_pow_div_factorial R) Metric.isOpen_ball (convex_ball (0 : ℝ) R).isPreconnected
    (fun n z _ ↦ ?_) (fun n z hz ↦ ?_) (Metric.mem_ball_self hR) (by simp)
    (by simp [R])
  · have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    convert (hasDerivAt_pow (n + 1) z).div_const (((n : ℝ) + 1) * ((n + 1)! : ℝ)) using 1
    push_cast [Nat.factorial_succ, add_tsub_cancel_right]
    field_simp
  · have hz' : |z| ≤ R := by simpa [Real.dist_eq] using (Metric.mem_ball.1 hz).le
    have hf : (0 : ℝ) < n ! := mod_cast n.factorial_pos
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg z) hz' n) hf
      (mod_cast Nat.factorial_le n.le_succ)

/-- For `y ≠ 0`, the derivative of `liSeries` at `y` is `(e^y - 1) / y`. -/
theorem hasDerivAt_liSeries_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt liSeries ((exp y - 1) / y) y := by
  simpa [Real.tsum_pow_div_factorial_succ hy] using hasDerivAt_liSeries y

/-- The derivative of `liSeries` at `0` is `1`. -/
theorem hasDerivAt_liSeries_zero : HasDerivAt liSeries 1 0 := by
  convert hasDerivAt_liSeries 0 using 1
  rw [tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp

/-- The series `liSeries` is continuous. -/
theorem continuous_liSeries : Continuous liSeries :=
  continuous_iff_continuousAt.2 fun y ↦ (hasDerivAt_liSeries y).continuousAt

/-- The series `liSeries` vanishes at `0`. -/
@[simp]
theorem liSeries_zero : liSeries 0 = 0 := by
  simp [liSeries]

/-- The first `k` terms of `liSeries` bound it below for `y ≥ 0`. -/
theorem sum_range_le_liSeries {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    ∑ n ∈ Finset.range k, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) ≤ liSeries y :=
  (summable_liSeries y).sum_le_tsum _ fun n _ ↦ by positivity

/-! ### Derivative and antiderivative -/

/-- The unoffset logarithmic integral has derivative `(log x)⁻¹` at every `x > 0` with `x ≠ 1`. -/
theorem hasDerivAt_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt li (log x)⁻¹ x := by
  have hl : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  have hlog := Real.hasDerivAt_log hx.ne'
  have h := ((hlog.log hl).const_add eulerMascheroniConstant).add
    ((hasDerivAt_liSeries_of_ne_zero hl).comp x hlog)
  rw [Real.exp_log hx] at h
  convert h using 1
  · ext y
    exact li_eq_add_liSeries y
  · field_simp
    ring

/-- The unoffset logarithmic integral is differentiable at every `x > 0` with `x ≠ 1`. -/
theorem differentiableAt_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : DifferentiableAt ℝ li x :=
  (hasDerivAt_li hx hx1).differentiableAt

/-- The unoffset logarithmic integral is continuous at every `x > 0` with `x ≠ 1`. -/
theorem continuousAt_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : ContinuousAt li x :=
  (hasDerivAt_li hx hx1).continuousAt

/-- The derivative of the unoffset logarithmic integral at `x > 0`, `x ≠ 1`. -/
theorem deriv_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : deriv li x = (log x)⁻¹ :=
  (hasDerivAt_li hx hx1).deriv

/-- The fundamental theorem of calculus for `li` on an interval avoiding `0` and `1`. -/
private theorem integral_inv_log_eq_li_sub_li_of_subset {a b : ℝ} {s : Set ℝ}
    (hs : uIcc a b ⊆ s) (hs0 : s ⊆ Ioi 0) (hs1 : (1 : ℝ) ∉ s) :
    ∫ t in a..b, (log t)⁻¹ = li b - li a := by
  have hpos : ∀ t ∈ uIcc a b, 0 < t := fun t ht ↦ hs0 (hs ht)
  have hne : ∀ t ∈ uIcc a b, t ≠ 1 := fun t ht h ↦ hs1 (h ▸ hs ht)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_li (hpos t ht) (hne t ht)) (ContinuousOn.intervalIntegrable ?_)
  exact (Real.continuousOn_log.mono fun t ht ↦ (hpos t ht).ne').inv₀ fun t ht ↦
    Real.log_ne_zero_of_pos_of_ne_one (hpos t ht) (hne t ht)

/-- On `(1, ∞)`, `li` is an antiderivative of `(log t)⁻¹`:
`∫ t in a..b, (log t)⁻¹ = li b - li a` for `a, b > 1`. -/
theorem integral_inv_log_eq_li_sub_li {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, (log t)⁻¹ = li b - li a :=
  integral_inv_log_eq_li_sub_li_of_subset (ordConnected_Ioi.uIcc_subset ha hb)
    (Ioi_subset_Ioi zero_le_one) (lt_irrefl 1)

/-- On `(0, 1)`, `li` is an antiderivative of `(log t)⁻¹`:
`∫ t in a..b, (log t)⁻¹ = li b - li a` for `a, b ∈ (0, 1)`. -/
theorem integral_inv_log_eq_li_sub_li_of_lt_one {a b : ℝ} (ha₀ : 0 < a) (ha : a < 1)
    (hb₀ : 0 < b) (hb : b < 1) :
    ∫ t in a..b, (log t)⁻¹ = li b - li a :=
  integral_inv_log_eq_li_sub_li_of_subset (ordConnected_Ioo.uIcc_subset ⟨ha₀, ha⟩ ⟨hb₀, hb⟩)
    Ioo_subset_Ioi_self fun h ↦ lt_irrefl 1 h.2

/-- The offset and unoffset logarithmic integrals differ by `li 2` on `(1, ∞)`:
`Li x = li x - li 2`. -/
theorem logIntegral_eq_li_sub_li_two {x : ℝ} (hx : 1 < x) : logIntegral x = li x - li 2 := by
  rw [logIntegral_def, integral_inv_log_eq_li_sub_li one_lt_two hx]

/-! ### Monotonicity and limits -/

/-- The unoffset logarithmic integral is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_li : StrictMonoOn li (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (fun x hx ↦ (continuousAt_li (zero_lt_one.trans hx) (ne_of_gt hx)).continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [deriv_li (zero_lt_one.trans hx) (ne_of_gt hx)]
  exact inv_pos.2 (Real.log_pos hx)

/-- The unoffset logarithmic integral is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_li : StrictAntiOn li (Ioo 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
    (fun x hx ↦ (continuousAt_li hx.1 (ne_of_lt hx.2)).continuousWithinAt) fun x hx ↦ ?_
  rw [interior_Ioo] at hx
  rw [deriv_li hx.1 (ne_of_lt hx.2)]
  exact inv_lt_zero.2 (Real.log_neg hx.1 hx.2)

/-- The unoffset logarithmic integral tends to `-∞` at `1`, from either side. -/
theorem tendsto_li_nhdsNE_one : Tendsto li (𝓝[≠] 1) atBot := by
  have hlog : Tendsto log (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [inter_mem_nhdsWithin _ (Ioi_mem_nhds zero_lt_one), self_mem_nhdsWithin]
        with x hx hx1 using Real.log_ne_zero_of_pos_of_ne_one hx.2 hx1
  have hser : Tendsto (fun x ↦ liSeries (log x)) (𝓝[≠] 1) (𝓝 0) := by
    rw [← liSeries_zero]
    exact (continuous_liSeries.tendsto 0).comp (hlog.mono_right nhdsWithin_le_nhds)
  exact ((tendsto_atBot_add_const_left _ eulerMascheroniConstant
    (Real.tendsto_log_nhdsNE_zero.comp hlog)).atBot_add hser).congr
    fun x ↦ (li_eq_add_liSeries x).symm

/-- The unoffset logarithmic integral tends to `+∞` at infinity. -/
theorem tendsto_li_atTop : Tendsto li atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_left _ eulerMascheroniConstant Real.tendsto_log_atTop)
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx0 : 0 < x := (exp_pos 1).trans_le hx
  have hl : 1 ≤ log x := by rwa [Real.le_log_iff_exp_le hx0]
  have hll : 0 ≤ log (log x) := Real.log_nonneg hl
  have hs := sum_range_le_liSeries (zero_le_one.trans hl) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.factorial_one,
    Nat.cast_one, CharP.cast_eq_zero, mul_one, div_one] at hs
  rw [li_eq_add_liSeries]
  linarith

/-! ### Positivity and Soldner's constant -/

/-- `li (3 / 2) > 0`: with `y = log (3 / 2) > 2 / 5`, the bounds `γ > 1 / 2` and
`liSeries y ≥ y + y² / 4` reduce it to `1 < y e^(1 / 2 + y + y² / 4)`, and
`e^(47 / 50) > 5 / 2` by the first four terms of the exponential series. -/
private theorem li_three_halves_pos : 0 < li (3 / 2) := by
  set y := log (3 / 2) with hy_def
  have hy := Real.two_fifths_lt_log_three_halves
  rw [← hy_def] at hy
  have hy0 : 0 < y := by linarith
  have hs := sum_range_le_liSeries hy0.le 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hs
  norm_num [Nat.factorial] at hs
  have he : (5 / 2 : ℝ) < exp (47 / 50) := by
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 4)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he' : exp (47 / 50) ≤ exp (1 / 2 + y + y ^ 2 / 4) := Real.exp_le_exp.2 (by nlinarith)
  have hlog : -(1 / 2 + y + y ^ 2 / 4) < log y := by
    rw [Real.lt_log_iff_exp_lt hy0, Real.exp_neg, inv_lt_iff_one_lt_mul₀ (exp_pos _)]
    nlinarith
  rw [li_eq_add_liSeries]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- The unoffset logarithmic integral is positive from `3 / 2` on. -/
theorem li_pos {x : ℝ} (hx : 3 / 2 ≤ x) : 0 < li x := by
  rcases hx.eq_or_lt with rfl | hx
  · exact li_three_halves_pos
  · exact li_three_halves_pos.trans
      (strictMonoOn_li (by norm_num : (1 : ℝ) < 3 / 2) (by simp only [mem_Ioi]; linarith) hx)

/-- Every zero of the unoffset logarithmic integral lies below `3 / 2`. -/
theorem lt_three_halves_of_li_eq_zero {μ : ℝ} (hμ : li μ = 0) : μ < 3 / 2 := by
  by_contra! h
  exact (li_pos h).ne' hμ

/-- **Soldner's constant**: the unoffset logarithmic integral has exactly one zero in `(1, ∞)`. -/
theorem existsUnique_li_eq_zero : ∃! μ, 1 < μ ∧ li μ = 0 := by
  obtain ⟨a, ha, hla⟩ : ∃ a ∈ Ioo (1 : ℝ) (3 / 2), li a < 0 := by
    have h : ∀ᶠ x in 𝓝[>] (1 : ℝ), x ∈ Ioo (1 : ℝ) (3 / 2) ∧ li x < 0 :=
      (eventually_mem_set.2 (Ioo_mem_nhdsGT (by norm_num))).and
        ((tendsto_li_nhdsNE_one.mono_left (nhdsWithin_mono _ fun x hx ↦ ne_of_gt hx)).eventually
          (eventually_lt_atBot 0))
    exact h.exists
  have hcont : ContinuousOn li (Icc a (3 / 2)) := fun x hx ↦
    (continuousAt_li (by linarith [ha.1, hx.1])
      (ne_of_gt (by linarith [ha.1, hx.1]))).continuousWithinAt
  obtain ⟨μ, hμ, hμ0⟩ := intermediate_value_Icc ha.2.le hcont ⟨hla.le, li_three_halves_pos.le⟩
  refine ⟨μ, ⟨ha.1.trans_le hμ.1, hμ0⟩, fun ν hν ↦ ?_⟩
  exact strictMonoOn_li.injOn hν.1 (ha.1.trans_le hμ.1) (hν.2.trans hμ0.symm)

end TauCeti.Real
