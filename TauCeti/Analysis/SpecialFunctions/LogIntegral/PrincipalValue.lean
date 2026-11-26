/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Exp.ExpIntegralSeries
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.InvLog
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Principal-value and regularized integral representations of `li`

This file recovers the classical Cauchy principal-value and exponential-integral (`Ei (log x)`)
characterizations of `TauCeti.Real.li` from the globally convergent series definition in
`TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset`, and supplies pole-subtracted and
symmetrically folded Lebesgue integrals that avoid principal-value limits when evaluating `li x`
and `li 2`:

* On `(0, 1)`, `li x = ∫ t in 0..x, (log t)⁻¹` as an ordinary Lebesgue interval integral.
* On `(1, ∞)`, `li x` is the Cauchy principal value
  `lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)`.
* In exponential-integral coordinates `t = e^u`, `∫ u in Iic y, exp u / u = li (exp y)` for
  `y < 0`, `li (exp y) = γ + log |y| + ∫ u in 0..y, (exp u - 1) / u` for all `y : ℝ`, and
  `∫ u in (-ε⁻¹)..(-ε), exp u / u + ∫ u in ε..y, exp u / u → li (exp y)` as `ε → 0⁺` for `y > 0`.
* Subtracting `(t - 1)⁻¹` cancels the pole at `t = 1` and gives the absolutely convergent
  representation `li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)` for all `x > 0`,
  `x ≠ 1`.
* Folding around `t = 1` gives the symmetric integral
  `li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`.

## Main declarations

* `TauCeti.Real.li_eq_integral_inv_log` — ordinary integral on `(0, 1)`.
* `TauCeti.Real.tendsto_li_sub_of_tendsto_abs_log_div`,
  `TauCeti.Real.tendsto_li_one_add_sub_one_sub`, and
  `TauCeti.Real.tendsto_integral_inv_log_principalValue` — cancellation of logarithmic divergences
  and Cauchy principal value on `(1, ∞)`.
* `TauCeti.Real.hasDerivAt_li_exp`, `TauCeti.Real.tendsto_li_exp_atBot`,
  `TauCeti.Real.integral_exp_div_eq_li_exp_sub`, `TauCeti.Real.integral_Iic_exp_div_eq_li_exp`,
  `TauCeti.Real.li_exp`, and `TauCeti.Real.tendsto_integral_exp_div_principalValue` —
  exponential-integral forms.
* `TauCeti.Real.li_eq_log_abs_sub_one_add_integral` — absolutely convergent regularized integral.
* `TauCeti.Real.li_two_eq_integral_inv_log_one_add_add_inv_log_one_sub` — symmetric integral for
  `li 2`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2 (Exponential,
  Logarithmic, Sine, and Cosine Integrals).
* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
-/

public section

open Filter MeasureTheory Set Real
open scoped Topology Nat

namespace TauCeti.Real

/-! ### Principal value and exponential-integral representations -/

/-- On `(0, 1)`, the unoffset logarithmic integral is the ordinary integral
`li x = ∫ t in 0..x, (log t)⁻¹`. -/
theorem li_eq_integral_inv_log {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li x = ∫ t in (0 : ℝ)..x, (log t)⁻¹ := by
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx0
    (fun t ht ↦ hasDerivAt_li ht.1 (ht.2.trans hx1).ne)
    (intervalIntegrable_inv_log_of_lt_one le_rfl one_pos hx0.le hx1)
    tendsto_li_nhdsGT_zero
    ((continuousAt_li hx0 hx1.ne).tendsto.mono_left nhdsWithin_le_nhds)).symm

/-- If `f x → 1`, `g x → 1`, and `|log (f x)| / |log (g x)| → 1` along a filter `l`, then the
logarithmic divergences and entire-part series cancel so `li (f x) - li (g x) → 0`. -/
theorem tendsto_li_sub_of_tendsto_abs_log_div {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : Tendsto f l (𝓝 1)) (hg : Tendsto g l (𝓝 1))
    (hr : Tendsto (fun x ↦ |log (f x)| / |log (g x)|) l (𝓝 1)) :
    Tendsto (fun x ↦ li (f x) - li (g x)) l (𝓝 0) := by
  have hlog_diff : Tendsto (fun x ↦ log |log (f x)| - log |log (g x)|) l (𝓝 0) := by
    have hcomp : Tendsto (fun x ↦ log (|log (f x)| / |log (g x)|)) l (𝓝 0) := by
      simpa [Function.comp_def, log_one] using (continuousAt_log one_ne_zero).tendsto.comp hr
    refine hcomp.congr' ?_
    filter_upwards [hr.eventually (Ioi_mem_nhds zero_lt_one)] with x hx
    have hdiv := div_ne_zero_iff.mp hx.ne'
    exact log_div hdiv.1 hdiv.2
  have hser_diff : Tendsto
      (fun x ↦
        (∑' n : ℕ, log (f x) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
        (∑' n : ℕ, log (g x) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))) l (𝓝 0) := by
    simpa only [Function.comp_def, sub_zero] using
      (tendsto_tsum_log_pow_div_mul_factorial_nhds_one.comp hf).sub
        (tendsto_tsum_log_pow_div_mul_factorial_nhds_one.comp hg)
  have hsum := hlog_diff.add hser_diff
  rw [add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [li_eq_add_log_abs, li_eq_add_log_abs]
  ring

/-- Symmetric cancellation of the logarithmic divergences of `li (1 + ε)` and `li (1 - ε)` as
`ε → 0⁺`: `li (1 + ε) - li (1 - ε) → 0`. -/
theorem tendsto_li_one_add_sub_one_sub :
    Tendsto (fun ε : ℝ ↦ li (1 + ε) - li (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
  have hp_lim : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((continuous_const_add (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hm_lim : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((continuous_sub_left (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlog_ratio : Tendsto (fun ε : ℝ ↦ |log (1 + ε)| / |log (1 - ε)|) (𝓝[>] 0) (𝓝 1) := by
    have hp : Tendsto (fun ε : ℝ ↦ log (1 + ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hd : HasDerivAt (fun t : ℝ ↦ log (1 + t)) 1 0 := by
        simpa using ((hasDerivAt_id' (0 : ℝ)).const_add (1 : ℝ)).log (by norm_num)
      exact (hd.tendsto_slope_zero.congr fun ε ↦ by simp [log_one, div_eq_inv_mul]).mono_left
        (nhdsGT_le_nhdsNE 0)
    have hm : Tendsto (fun ε : ℝ ↦ -log (1 - ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hd : HasDerivAt (fun t : ℝ ↦ -log (1 - t)) 1 0 := by
        simpa using (((hasDerivAt_id' (0 : ℝ)).const_sub (1 : ℝ)).log (by norm_num)).fun_neg
      exact (hd.tendsto_slope_zero.congr fun ε ↦ by simp [log_one, div_eq_inv_mul]).mono_left
        (nhdsGT_le_nhdsNE 0)
    have hdiv : Tendsto (fun ε : ℝ ↦ (log (1 + ε) / ε) / (-log (1 - ε) / ε)) (𝓝[>] 0) (𝓝 1) := by
      simpa [Pi.div_def] using hp.div hm one_ne_zero
    refine hdiv.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε ⟨hε0, hε1⟩
    rw [abs_of_pos (log_pos (by linarith)), abs_of_neg (log_neg (by linarith) (by linarith))]
    field_simp [hε0.ne']
  exact tendsto_li_sub_of_tendsto_abs_log_div hp_lim hm_lim hlog_ratio

/-- **Cauchy principal value representation of `li` on `(1, ∞)`**:
`∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹ → li x` as `ε → 0⁺`. -/
theorem tendsto_integral_inv_log_principalValue {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), (log t)⁻¹) + ∫ t in (1 + ε)..x, (log t)⁻¹)
      (𝓝[>] 0) (𝓝 (li x)) := by
  have hlim : Tendsto (fun ε : ℝ ↦ li x - (li (1 + ε) - li (1 - ε))) (𝓝[>] 0) (𝓝 (li x)) := by
    simpa using tendsto_const_nhds.sub tendsto_li_one_add_sub_one_sub
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx))] with ε ⟨hε0, hεm⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
  rw [← li_eq_integral_inv_log (by linarith) (by linarith),
    integral_inv_log_eq_li_sub_li (by linarith) hx]
  ring

/-- In exponential coordinates, `t ↦ li (exp t)` has derivative `exp u / u` at every `u ≠ 0`. -/
theorem hasDerivAt_li_exp {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ li (exp t)) (exp u / u) u := by
  have hne : exp u ≠ 1 := fun h ↦ hu (by simpa [log_exp] using congrArg log h)
  have h := (hasDerivAt_li (exp_pos u) hne).comp u (hasDerivAt_exp u)
  simpa only [Function.comp_def, log_exp, div_eq_mul_inv, mul_comm] using h

/-- `li (exp t) → 0` as `t → -∞`. -/
theorem tendsto_li_exp_atBot : Tendsto (fun t : ℝ ↦ li (exp t)) atBot (𝓝 0) :=
  tendsto_li_nhdsGT_zero.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_exp_atBot (Eventually.of_forall exp_pos))

/-- On any closed interval avoiding `0`, `∫ u in a..b, exp u / u = li (exp b) - li (exp a)`. -/
theorem integral_exp_div_eq_li_exp_sub {a b : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) :
    (∫ u in a..b, exp u / u) = li (exp b) - li (exp a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ li (exp t))
    (fun u hu ↦ hasDerivAt_li_exp fun h ↦ h0 (h ▸ hu))
    (ContinuousOn.intervalIntegrable fun u hu ↦ ?_)
  have hu0 : u ≠ 0 := fun h ↦ h0 (h ▸ hu)
  fun_prop (disch := assumption)

/-- Exponential-integral form of `li` on `(0, 1)`: for `y < 0`,
`∫ u in Iic y, exp u / u = li (exp y)`. -/
theorem integral_Iic_exp_div_eq_li_exp {y : ℝ} (hy : y < 0) :
    (∫ u in Iic y, exp u / u) = li (exp y) := by
  simpa using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun u hu ↦ hasDerivAt_li_exp (lt_of_le_of_lt hu hy).ne)
    (integrableOn_exp_div_Iic hy) tendsto_li_exp_atBot

/-- **Exponential-integral representation via the regularized integrand** `(exp u - 1) / u`:
for every `y : ℝ`, `li (exp y) = γ + log |y| + ∫ u in 0..y, (exp u - 1) / u`. -/
theorem li_exp (y : ℝ) :
    li (exp y) = eulerMascheroniConstant + log |y| + ∫ u in (0 : ℝ)..y, (exp u - 1) / u := by
  rw [li_eq_add_log_abs, log_exp, integral_exp_sub_one_div_eq_tsum]

/-- **Exponential-integral principal value representation of `li` on `(1, ∞)`**: for `y > 0`,
`∫ u in (-ε⁻¹)..(-ε), exp u / u + ∫ u in ε..y, exp u / u → li (exp y)` as `ε → 0⁺`. -/
theorem tendsto_integral_exp_div_principalValue {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun ε : ℝ ↦ (∫ u in (-ε⁻¹)..(-ε), exp u / u) + ∫ u in ε..y, exp u / u)
      (𝓝[>] 0) (𝓝 (li (exp y))) := by
  have hneg_inv : Tendsto (fun ε : ℝ ↦ li (exp (-ε⁻¹))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_li_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero)
  have hsymm : Tendsto (fun ε : ℝ ↦ li (exp (-ε)) - li (exp ε)) (𝓝[>] 0) (𝓝 0) := by
    have hf : Tendsto (fun ε : ℝ ↦ exp (-ε)) (𝓝[>] 0) (𝓝 1) := by
      have h : Continuous (fun ε : ℝ ↦ exp (-ε)) := continuous_exp.comp continuous_neg
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    have hg : Tendsto (fun ε : ℝ ↦ exp ε) (𝓝[>] 0) (𝓝 1) := by
      simpa using (continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds
    have hr : Tendsto (fun ε : ℝ ↦ |log (exp (-ε))| / |log (exp ε)|) (𝓝[>] 0) (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      simp [log_exp, abs_neg, div_self (abs_pos.mpr hε.ne').ne']
    exact tendsto_li_sub_of_tendsto_abs_log_div hf hg hr
  have hlim : Tendsto
      (fun ε : ℝ ↦ li (exp y) - li (exp (-ε⁻¹)) + (li (exp (-ε)) - li (exp ε)))
      (𝓝[>] 0) (𝓝 (li (exp y))) := by
    simpa using (tendsto_const_nhds.sub hneg_inv).add hsymm
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hy)] with ε ⟨hε0, hεm⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hεy : ε < y := lt_of_lt_of_le hεm (min_le_right _ _)
  have hle_neg : -ε⁻¹ ≤ -ε := by linarith [(one_le_inv₀ hε0).mpr hε1.le]
  have h1 : (∫ u in (-ε⁻¹)..(-ε), exp u / u) = li (exp (-ε)) - li (exp (-ε⁻¹)) :=
    integral_exp_div_eq_li_exp_sub fun h ↦ by
      rw [uIcc_of_le hle_neg] at h
      linarith [h.2]
  have h2 : (∫ u in ε..y, exp u / u) = li (exp y) - li (exp ε) :=
    integral_exp_div_eq_li_exp_sub fun h ↦ by
      rw [uIcc_of_le hεy.le] at h
      linarith [h.1]
  rw [h1, h2]
  ring

/-! ### Absolutely convergent integral representations -/

/-- **Absolutely convergent integral representation of `li`**: for every `x > 0`, `x ≠ 1`,
`li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`. -/
theorem li_eq_log_abs_sub_one_add_integral {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    li x = log |x - 1| + ∫ t in (0 : ℝ)..x, ((log t)⁻¹ - (t - 1)⁻¹) := by
  rcases lt_or_gt_of_ne hx1 with hx_lt | hx_gt
  · have h1 : (1 : ℝ) ∉ uIcc 0 x := by rw [uIcc_of_le hx0.le]; intro h; linarith [h.2]
    have hdiff := intervalIntegral.integral_sub
      (intervalIntegrable_inv_log_of_lt_one le_rfl one_pos hx0.le hx_lt)
      (intervalIntegrable_sub_inv_iff.mpr (Or.inr h1))
    rw [← li_eq_integral_inv_log hx0 hx_lt, integral_sub_inv h1, zero_sub, abs_neg, abs_one,
      log_one, sub_zero] at hdiff
    linarith
  · have h1 := (TauCeti.intervalIntegral.tendsto_integral_excise (c := 1)
      (by rw [uIoo_of_le hx0.le]; exact ⟨one_pos, hx_gt⟩)
      (intervalIntegrable_inv_log_sub_inv_sub_one le_rfl hx0.le)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    have h2 : Tendsto
        (fun ε : ℝ ↦
          (∫ t in (0 : ℝ)..(1 - ε), ((log t)⁻¹ - (t - 1)⁻¹)) +
            ∫ t in (1 + ε)..x, ((log t)⁻¹ - (t - 1)⁻¹))
        (𝓝[>] 0) (𝓝 (li x - log |x - 1|)) := by
      refine ((tendsto_integral_inv_log_principalValue hx_gt).sub_const
        (log |x - 1|)).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx_gt))] with ε ⟨hε0, hεm⟩
      have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
      have hεx : 1 + ε < x := by linarith [lt_of_lt_of_le hεm (min_le_right _ _)]
      have hnot1 : (1 : ℝ) ∉ uIcc 0 (1 - ε) := by
        rw [uIcc_of_le (by linarith)]; intro h; linarith [h.2]
      have hnot2 : (1 : ℝ) ∉ uIcc (1 + ε) x := by
        rw [uIcc_of_le hεx.le]; intro h; linarith [h.1]
      rw [intervalIntegral.integral_sub
            (intervalIntegrable_inv_log_of_lt_one le_rfl one_pos (by linarith) (by linarith))
            (intervalIntegrable_sub_inv_iff.mpr (Or.inr hnot1)),
          intervalIntegral.integral_sub
            (by simpa [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith) hx_gt)
            (intervalIntegrable_sub_inv_iff.mpr (Or.inr hnot2)),
          integral_sub_inv hnot1, integral_sub_inv hnot2]
      have hε_sub : |1 - ε - 1| = ε := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
      have hε_add : |1 + ε - 1| = ε := by rw [add_sub_cancel_left, abs_of_pos hε0]
      rw [hε_sub, hε_add]
      norm_num [log_one]
      ring
    linarith [tendsto_nhds_unique h1 h2]

/-! ### Symmetric integral representation for `li 2` -/

/-- **Symmetric absolutely convergent integral for `li 2`**:
`li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`. -/
theorem li_two_eq_integral_inv_log_one_add_add_inv_log_one_sub :
    li 2 = ∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹) := by
  have hreg := li_eq_log_abs_sub_one_add_integral two_pos (by norm_num)
  norm_num [log_one] at hreg
  have heq : (∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)) =
      (∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ - u⁻¹)) +
        ∫ u in (0 : ℝ)..1, ((log (1 - u))⁻¹ + u⁻¹) := by
    rw [← intervalIntegral.integral_add intervalIntegrable_inv_log_one_add_sub_inv
      intervalIntegrable_inv_log_one_sub_add_inv]
    exact intervalIntegral.integral_congr fun u _ ↦ by ring
  have hshift1 : (∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ - u⁻¹)) =
      ∫ t in (1 : ℝ)..2, ((log t)⁻¹ - (t - 1)⁻¹) := by
    simpa [add_zero, add_sub_cancel_left, one_add_one_eq_two] using
      intervalIntegral.integral_comp_add_left (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) (1 : ℝ)
        (a := (0 : ℝ)) (b := 1)
  have hshift2 : (∫ u in (0 : ℝ)..1, ((log (1 - u))⁻¹ + u⁻¹)) =
      ∫ t in (0 : ℝ)..1, ((log t)⁻¹ - (t - 1)⁻¹) := by
    simpa [sub_zero, sub_self, sub_sub_cancel_left, inv_neg, sub_neg_eq_add] using
      intervalIntegral.integral_comp_sub_left (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) (1 : ℝ)
        (a := (0 : ℝ)) (b := 1)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log_sub_inv_sub_one (a := (0 : ℝ)) (b := 1) le_rfl zero_le_one)
    (intervalIntegrable_inv_log_sub_inv_sub_one (a := (1 : ℝ)) (b := 2) zero_le_one (by norm_num))
  rw [heq, hshift1, hshift2, add_comm, hsplit, ← hreg]

end TauCeti.Real
