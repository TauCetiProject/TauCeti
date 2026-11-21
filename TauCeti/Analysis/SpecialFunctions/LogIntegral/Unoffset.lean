/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.NumberTheory.Harmonic.GammaDeriv

/-!
# The unoffset logarithmic integral

This file defines the unoffset logarithmic integral

```text
li x = γ + log |log x| + ∑' n : ℕ, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)
```

for real `x > 0`, `x ≠ 1` (the exponential integral `Ei` evaluated at `log x`). For `x ≤ 0` and
at `x = 1` the values are junk: in particular `li 0 = li 1 = γ` (not `0`), and `li (-x) = li x`
for `x < 0`. Unlike the offset logarithmic integral `TauCeti.Real.logIntegral` (`Li x`, with
`Li 2 = 0`), `li` cannot be defined on `(1, ∞)` by a plain interval integral from `0` to `x`
because `(log t)⁻¹` has a nonintegrable singularity at `t = 1`. Defining `li` by the globally
convergent series avoids that singularity and lets the Cauchy principal value and exponential
integral representations (proved in `TauCeti.Analysis.SpecialFunctions.LogIntegral.PrincipalValue`)
follow as theorems.

## Main declarations

* `Real.li`, `Real.li_def`, `Real.li_eq_add_log_abs`, `Real.li_zero`, `Real.li_one`,
  `Real.li_neg_eq` — the unoffset logarithmic integral and its normalization lemmas.
* `Real.hasDerivAt_li`, `Real.deriv_li`, `Real.differentiableAt_li`, `Real.continuousAt_li`,
  `Real.measurable_li` — derivative `(log x)⁻¹` and regularity of `li`.
* `Real.tendsto_li_nhdsGT_zero` — `li x → 0` as `x → 0⁺`.
* `Real.logIntegral_eq_li_sub_li_two` and `Real.li_eq_logIntegral_add_li_two` — the offset
  identity `Li x = li x - li 2` for `x > 1`.
* `Real.strictAntiOn_li_Ioo`, `Real.li_neg`, `Real.strictMonoOn_li_Ioi`,
  `Real.tendsto_li_nhdsNE_one`, `Real.tendsto_li_nhdsGT_one`, `Real.tendsto_li_nhdsLT_one`,
  `Real.tendsto_li_atTop`, `Real.li_pos_of_three_halves_le`, and `Real.existsUnique_li_eq_zero` —
  monotonicity, boundary limits, positivity for `x ≥ 3 / 2`, and Soldner's constant.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §§6.2, 6.6, and 6.13
  (Exponential, Logarithmic, Sine, and Cosine Integrals).
* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
-/

public section

open Filter MeasureTheory Set TauCeti.Real
open scoped Topology Nat

namespace Real

/-! ### Definition, derivative, and regularity of `li` -/

/-- The **unoffset logarithmic integral**
`li x = γ + log |log x| + ∑_{n ≥ 1} (log x)^n / (n * n!)`.

Mathlib's `Real.log` satisfies `log (-u) = log u`, so `log (log x)` equals `log |log x|`.
This series defines `li` on `(0, 1) ∪ (1, ∞)`. The values for `x ≤ 0` and at `x = 1` are junk:
in particular `li 0 = li 1 = γ` (not the classical value `0`), and `li (-x) = li x` for `x < 0`.
For `0 < x < 1` it equals `∫ t in 0..x, (log t)⁻¹`, and for `x > 1` it equals the Cauchy principal
value `lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)` and satisfies
`Li x = li x - li 2`. -/
noncomputable def li (x : ℝ) : ℝ :=
  eulerMascheroniConstant + log (log x) +
    ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `Real.li`. -/
theorem li_def (x : ℝ) :
    li x = eulerMascheroniConstant + log (log x) +
      ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-- Explicit absolute-value form of `Real.li`. -/
theorem li_eq_add_log_abs (x : ℝ) :
    li x = eulerMascheroniConstant + log |log x| +
      ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [li_def, log_abs]

/-- `li 0` takes the junk value `γ`. -/
@[simp]
theorem li_zero : li 0 = eulerMascheroniConstant := by
  simp [li_def]

/-- `li 1` takes the junk value `γ`. -/
@[simp]
theorem li_one : li 1 = eulerMascheroniConstant := by
  simp [li_def]

/-- `li` is symmetric in sign (for `x < 0`, `li x` takes the junk value `li (-x)`). -/
@[simp]
theorem li_neg_eq (x : ℝ) : li (-x) = li x := by
  simp [li_def]

/-- The unoffset logarithmic integral has derivative `(log x)⁻¹` for every `x > 0`, `x ≠ 1`. -/
theorem hasDerivAt_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt li (log x)⁻¹ x := by
  have hlog : log x ≠ 0 := log_ne_zero_of_pos_of_ne_one hx0 hx1
  have h1 : HasDerivAt (fun t ↦ eulerMascheroniConstant + log (log t))
      ((log x)⁻¹ * x⁻¹) x :=
    ((hasDerivAt_log hlog).comp x (hasDerivAt_log hx0.ne')).const_add eulerMascheroniConstant
  have h2 : HasDerivAt
      (fun t ↦ ∑' n : ℕ, log t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (dslope exp 0 (log x) * x⁻¹) x :=
    (hasDerivAt_tsum_pow_div_mul_factorial (log x)).comp x (hasDerivAt_log hx0.ne')
  refine (h1.add h2).congr_deriv ?_
  rw [dslope_exp_zero_of_ne hlog, exp_log hx0]
  have hxne : x ≠ 0 := hx0.ne'
  field_simp
  ring

/-- The derivative of `li` is `(log x)⁻¹` for every `x > 0`, `x ≠ 1`. -/
theorem deriv_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) : deriv li x = (log x)⁻¹ :=
  (hasDerivAt_li hx0 hx1).deriv

/-- `li` is differentiable at every `x > 0`, `x ≠ 1`. -/
@[fun_prop]
theorem differentiableAt_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) : DifferentiableAt ℝ li x :=
  (hasDerivAt_li hx0 hx1).differentiableAt

/-- `li` is continuous at every `x > 0`, `x ≠ 1`. -/
@[fun_prop]
theorem continuousAt_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) : ContinuousAt li x :=
  (hasDerivAt_li hx0 hx1).continuousAt

/-- `li` is measurable on `ℝ`. -/
@[fun_prop]
theorem measurable_li : Measurable li := by
  unfold li
  exact (measurable_const.add (measurable_log.comp measurable_log)).add
    (continuous_tsum_pow_div_mul_factorial.measurable.comp measurable_log)

/-- `li` is differentiable on `(0, 1)`. -/
theorem differentiableOn_li_Ioo : DifferentiableOn ℝ li (Ioo 0 1) :=
  fun _ hx ↦ (differentiableAt_li hx.1 hx.2.ne).differentiableWithinAt

/-- `li` is differentiable on `(1, ∞)`. -/
theorem differentiableOn_li_Ioi : DifferentiableOn ℝ li (Ioi 1) :=
  fun _ hx ↦ (differentiableAt_li (zero_lt_one.trans hx) (ne_of_gt hx)).differentiableWithinAt

/-- `li` is continuous on `(0, 1)`. -/
theorem continuousOn_li_Ioo : ContinuousOn li (Ioo 0 1) :=
  differentiableOn_li_Ioo.continuousOn

/-- `li` is continuous on `(1, ∞)`. -/
theorem continuousOn_li_Ioi : ContinuousOn li (Ioi 1) :=
  differentiableOn_li_Ioi.continuousOn

/-! ### Behaviour at `0⁺` -/

/-- `li x → 0` as `x → 0⁺`. -/
theorem tendsto_li_nhdsGT_zero : Tendsto li (𝓝[>] 0) (𝓝 0) := by
  have hformula (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
      li x = eulerMascheroniConstant +
        log (-log x) * exp (-(-log x)) +
        ∫ t in Ioc 0 (-log x), log t * exp (-t) := by
    set z : ℝ := -log x
    have hz : 0 < z := neg_pos.mpr (log_neg hx0 hx1)
    have hseries : (∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) =
        -(∫ t in (0 : ℝ)..z, (1 - exp (-t)) / t) := by
      rw [← integral_exp_sub_one_div_eq_tsum (log x)]
      have hsub := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
        (f := fun u : ℝ ↦ (exp u - 1) / u)
      have hneg_z : -z = log x := neg_neg (log x)
      rw [neg_zero, hneg_z, intervalIntegral.integral_symm (0 : ℝ) (log x)] at hsub
      have hneg : (∫ u in (0 : ℝ)..log x, (exp u - 1) / u) =
          -(∫ t in (0 : ℝ)..z, (exp (-t) - 1) / -t) := by linarith
      rw [hneg]
      congr 1
      refine intervalIntegral.integral_congr fun t _ ↦ by ring
    have hibp := one_sub_exp_neg_mul_log_eq hz.le
    have hlogz : log (log x) = log z := (log_neg_eq_log (log x)).symm
    rw [li_def, hseries, hlogz]
    linarith
  have hz_top : Tendsto (fun x : ℝ ↦ -log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have hterm2 : Tendsto (fun z : ℝ ↦ ∫ t in Ioc 0 z, log t * exp (-t)) atTop
      (𝓝 (∫ t in Ioi 0, log t * exp (-t))) := by
    refine (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      integrableOn_log_mul_exp_neg_Ioi tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact intervalIntegral.integral_of_le hz
  have hlim : Tendsto
      (fun x : ℝ ↦ eulerMascheroniConstant +
        log (-log x) * exp (-(-log x)) +
        ∫ t in Ioc 0 (-log x), log t * exp (-t))
      (𝓝[>] 0) (𝓝 0) := by
    have hsum := ((tendsto_const_nhds (x := eulerMascheroniConstant)).add
      (tendsto_log_mul_exp_neg_atTop.comp hz_top)).add (hterm2.comp hz_top)
    have hzero : eulerMascheroniConstant + 0 +
        ∫ t in Ioi (0 : ℝ), log t * exp (-t) = 0 := by
      rw [eulerMascheroniConstant_eq_neg_integral_log]
      ring
    rwa [hzero] at hsum
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with x ⟨hx0, hx1⟩
  exact (hformula x hx0 hx1).symm

/-! ### Relation with `Li`, monotonicity, sign, and Soldner's constant -/

/-- **Offset identity**: for every `x > 1`, `Li x = li x - li 2`. -/
theorem logIntegral_eq_li_sub_li_two {x : ℝ} (hx : 1 < x) :
    logIntegral x = li x - li 2 := by
  rw [logIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
    (by simpa [pow_one] using intervalIntegrable_inv_log_pow 1 one_lt_two hx)
  have ht1 : 1 < t := by
    rcases mem_uIcc.mp ht with h | h
    · exact one_lt_two.trans_le h.1
    · exact hx.trans_le h.1
  exact hasDerivAt_li (zero_lt_one.trans ht1) ht1.ne'

/-- Rearranged offset identity: for every `x > 1`, `li x = Li x + li 2`. -/
theorem li_eq_logIntegral_add_li_two {x : ℝ} (hx : 1 < x) :
    li x = logIntegral x + li 2 := by
  linarith [logIntegral_eq_li_sub_li_two hx]

/-- `li` is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_li_Ioo : StrictAntiOn li (Ioo 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1) continuousOn_li_Ioo fun x hx ↦ ?_
  rw [interior_Ioo] at hx
  rw [deriv_li hx.1 hx.2.ne]
  exact inv_lt_zero.mpr (log_neg hx.1 hx.2)

/-- `li` is strictly negative on `(0, 1)`. -/
theorem li_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : li x < 0 := by
  have hle : li (x / 2) ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds tendsto_li_nhdsGT_zero ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hx0)] with y ⟨hy0, hyx⟩
    exact (strictAntiOn_li_Ioo ⟨hy0, hyx.trans (by linarith)⟩
      ⟨half_pos hx0, by linarith⟩ hyx).le
  exact (strictAntiOn_li_Ioo ⟨half_pos hx0, by linarith⟩ ⟨hx0, hx1⟩ (by linarith)).trans_le hle

/-- `li` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_li_Ioi : StrictMonoOn li (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1) continuousOn_li_Ioi fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [deriv_li (zero_lt_one.trans hx) hx.ne']
  exact inv_pos.mpr (log_pos hx)

/-- `li x → -∞` as `x → 1`, `x ≠ 1`. -/
theorem tendsto_li_nhdsNE_one : Tendsto li (𝓝[≠] 1) atBot := by
  have hlog : Tendsto (fun x : ℝ ↦ log (log x)) (𝓝[≠] 1) atBot := by
    refine tendsto_log_nhdsNE_zero.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa [log_one] using (continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds)
      ?_
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin] with x hx0 hx1
    exact log_ne_zero_of_pos_of_ne_one hx0 hx1
  have hser : Tendsto
      (fun x : ℝ ↦ ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (𝓝[≠] 1) (𝓝 0) := by
    have hc : ContinuousAt
        (fun x : ℝ ↦ ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 1 :=
      continuous_tsum_pow_div_mul_factorial.continuousAt.comp (continuousAt_log one_ne_zero)
    simpa [log_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ((tendsto_atBot_add_const_left _ eulerMascheroniConstant hlog).atBot_add
    hser).congr fun x ↦ ?_
  rw [li_def]

/-- `li x → -∞` as `x → 1⁺`. -/
theorem tendsto_li_nhdsGT_one : Tendsto li (𝓝[>] 1) atBot :=
  tendsto_li_nhdsNE_one.mono_left (nhdsGT_le_nhdsNE 1)

/-- `li x → -∞` as `x → 1⁻`. -/
theorem tendsto_li_nhdsLT_one : Tendsto li (𝓝[<] 1) atBot :=
  tendsto_li_nhdsNE_one.mono_left (nhdsLT_le_nhdsNE 1)

/-- `li x → +∞` as `x → +∞`. -/
theorem tendsto_li_atTop : Tendsto li atTop atTop := by
  have hLi : Tendsto logIntegral atTop atTop :=
    logIntegral_isEquivalent_div_log.tendsto_atTop_iff.mpr tendsto_div_log_atTop
  refine (tendsto_atTop_add_const_right _ (li 2) hLi).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (li_eq_logIntegral_add_li_two hx).symm

/-- `li x > 0` for every `x ≥ 3 / 2`. -/
theorem li_pos_of_three_halves_le {x : ℝ} (hx : (3 : ℝ) / 2 ≤ x) : 0 < li x := by
  suffices h32 : 0 < li (3 / 2) by
    rcases eq_or_lt_of_le hx with rfl | hlt
    · exact h32
    · exact h32.trans (strictMonoOn_li_Ioi (by norm_num) (mem_Ioi.mpr (by linarith)) hlt)
  -- Show `0.4054 < log (3 / 2)` via `exp 0.4054 < 3 / 2`.
  have hlog32 : (0.4054 : ℝ) < log (3 / 2) := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have hb := exp_bound' (x := (0.4054 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by decide)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hb
    norm_num at hb ⊢
    linarith
  -- Show `-0.903 < log (log (3 / 2))` via `1 < 0.4054 * exp 0.903`.
  have hloglog : (-0.903 : ℝ) < log (log (3 / 2)) := by
    rw [lt_log_iff_exp_lt (by linarith)]
    have he := sum_le_exp_of_nonneg (x := (903 / 1000 : ℝ)) (by norm_num) 8
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at he
    norm_num at he
    have hexp_mul : exp (-(903 / 1000 : ℝ)) * exp (903 / 1000) = 1 := by
      rw [← exp_add]; norm_num
    have hlt : exp (-(903 / 1000 : ℝ)) < 4054 / 10000 := by nlinarith
    have hlt' : exp (-0.903) < 0.4054 := by norm_num at hlt ⊢; exact hlt
    exact hlt'.trans hlog32
  -- First two terms of the positive series at `log (3 / 2)`.
  have hser : (0.446 : ℝ) <
      ∑' n : ℕ, log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
    have hsum := summable_pow_div_mul_factorial (log (3 / 2))
    have hnonneg (n : ℕ) :
        0 ≤ log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
      have : 0 < log (3 / 2) := by linarith
      positivity
    have hge := hsum.sum_le_tsum (Finset.range 2) (fun n _ ↦ hnonneg n)
    have htwo : (0.446 : ℝ) <
        ∑ n ∈ Finset.range 2,
          log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        Nat.cast_zero, Nat.cast_one, Nat.factorial]
      norm_num
      nlinarith
    exact htwo.trans_le hge
  rw [li_def]
  linarith [one_half_lt_eulerMascheroniConstant]

/-- `li 2 > 0`. -/
theorem li_two_pos : 0 < li 2 :=
  li_pos_of_three_halves_le (by norm_num)

/-- The unoffset logarithmic integral `li` differs from the offset logarithmic integral `Li`. -/
theorem li_ne_logIntegral : li ≠ logIntegral := by
  intro h
  have h2 := congr_fun h 2
  rw [logIntegral_two] at h2
  linarith [li_two_pos]

/-- **Soldner's constant**: `li` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_li_eq_zero : ∃! μ ∈ Ioi (1 : ℝ), li μ = 0 := by
  obtain ⟨a, ha1, ha_lt⟩ : ∃ a ∈ Ioo (1 : ℝ) (3 / 2), li a < 0 := by
    have hmem : ∀ᶠ t in 𝓝[>] (1 : ℝ), li t < 0 :=
      tendsto_li_nhdsGT_one.eventually (eventually_lt_atBot 0)
    exact (hmem.and (Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 3 / 2))).exists.imp fun a ⟨h1, h2⟩ ↦
      ⟨h2, h1⟩
  have hcont : ContinuousOn li (Icc a (3 / 2)) :=
    continuousOn_li_Ioi.mono fun t ht ↦ ha1.1.trans_le ht.1
  have h0 : (0 : ℝ) ∈ Icc (li a) (li (3 / 2)) := ⟨ha_lt.le, (li_pos_of_three_halves_le le_rfl).le⟩
  obtain ⟨μ, hμ, hliμ⟩ := intermediate_value_Icc ha1.2.le hcont h0
  refine ⟨μ, ⟨ha1.1.trans_le hμ.1, hliμ⟩, fun y ⟨hy1, hliy⟩ ↦ ?_⟩
  exact strictMonoOn_li_Ioi.injOn hy1 (ha1.1.trans_le hμ.1) (hliy.trans hliμ.symm)

end Real
