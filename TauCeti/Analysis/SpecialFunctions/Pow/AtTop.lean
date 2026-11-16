/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Order.Filter.AtTopBot

/-!
# Behaviour of complex exponentials and principal powers at infinity

For a complex parameter `c`, the ray `t ↦ exp (c * t)` along `(0, ∞)` converges as `t → +∞` in
exactly two regimes: it tends to `0` when `re c < 0` (`TauCeti.tendsto_exp_mul_ofReal_atTop_zero`)
and is identically `1` when `c = 0`. Whenever `0 ≤ re c` and `c ≠ 0` it has no finite limit
(`TauCeti.not_tendsto_exp_mul_ofReal_atTop`): for `0 < re c` its norm grows exponentially, whereas
for purely imaginary `c = i u` (`u ≠ 0`) it oscillates on the unit circle and negates under the
translation `t ↦ t + π / u`.

Composing with `exp` transfers this dichotomy to real-base principal powers `x ↦ (x : ℂ) ^ s`, and
comparing `t ↦ ⌊exp t⌋₊` with `exp t` transfers it further to natural-number principal powers
`n ↦ (n : ℂ) ^ s`: each converges to a finite complex limit at `atTop` if and only if
`re s < 0 ∨ s = 0` (`TauCeti.exists_tendsto_ofReal_cpow_atTop_iff`,
`TauCeti.exists_tendsto_natCast_cpow_atTop_iff`).

## Main results

* `TauCeti.tendsto_exp_mul_ofReal_atTop_zero`, `TauCeti.not_tendsto_exp_mul_ofReal_atTop`,
  `TauCeti.exists_tendsto_exp_mul_ofReal_atTop_iff`: convergence dichotomy for `t ↦ exp (c * t)`
  as `t → +∞`.
* `TauCeti.tendsto_ofReal_cpow_atTop_zero`, `TauCeti.not_tendsto_ofReal_cpow_atTop`,
  `TauCeti.exists_tendsto_ofReal_cpow_atTop_iff`: convergence dichotomy for `x ↦ (x : ℂ) ^ s`
  as `x → +∞`.
* `TauCeti.tendsto_natCast_cpow_atTop_zero`, `TauCeti.not_tendsto_natCast_cpow_atTop`,
  `TauCeti.exists_tendsto_natCast_cpow_atTop_iff`: convergence dichotomy for `n ↦ (n : ℂ) ^ s`
  as `n → ∞`.
-/

public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-! ### Complex exponentials along the positive real ray -/

/-- When `re c < 0`, `exp (c * t)` tends to `0` as the real parameter `t` tends to `+∞`. -/
theorem tendsto_exp_mul_ofReal_atTop_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun t : ℝ ↦ Complex.exp (c * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_exp, Complex.re_mul_ofReal]
  exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)

/-- When `0 ≤ re c` and `c ≠ 0`, `exp (c * t)` has no finite limit in `ℂ` as `t → +∞`. -/
theorem not_tendsto_exp_mul_ofReal_atTop {c L : ℂ} (hre : 0 ≤ c.re) (hc : c ≠ 0) :
    ¬ Tendsto (fun t : ℝ ↦ Complex.exp (c * t)) atTop (𝓝 L) := by
  intro h
  rcases hre.lt_or_eq with hpos | hzero
  · have hnorm : Tendsto (fun t : ℝ ↦ ‖Complex.exp (c * t)‖) atTop atTop := by
      simp_rw [Complex.norm_exp, Complex.re_mul_ofReal]
      exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hpos)
    exact not_tendsto_nhds_of_tendsto_atTop hnorm _ h.norm
  · -- For purely imaginary `c ≠ 0`, translating by `π / im c` negates `exp (c * t)`.
    have him : c.im ≠ 0 := fun him ↦ hc (Complex.ext hzero.symm him)
    have hc_eq : c = (c.im : ℂ) * I := Complex.ext (by simp [← hzero]) (by simp)
    have hshift : Tendsto (fun t : ℝ ↦ t + Real.pi / c.im) atTop atTop :=
      tendsto_atTop_add_const_right atTop (Real.pi / c.im) tendsto_id
    have hneg_fn : ∀ t : ℝ,
        Complex.exp (c * ((t + Real.pi / c.im : ℝ) : ℂ)) = -Complex.exp (c * t) := fun t ↦ by
      have him' : (c.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr him
      have harg : c * ((t + Real.pi / c.im : ℝ) : ℂ) = c * t + Real.pi * I := by
        rw [ofReal_add, ofReal_div, mul_add]
        congr 1
        nth_rw 1 [hc_eq]
        field_simp [him']
      rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
    have hL_neg : L = -L := tendsto_nhds_unique ((h.comp hshift).congr hneg_fn) h.neg
    have hL_zero : L = 0 := CharZero.eq_neg_self_iff.mp hL_neg
    have hnorm_one : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 ‖L‖) := by
      refine h.norm.congr fun t ↦ ?_
      rw [Complex.norm_exp, Complex.re_mul_ofReal, ← hzero, zero_mul, Real.exp_zero]
    have h10 : (1 : ℝ) = 0 := by
      simpa [hL_zero] using tendsto_nhds_unique hnorm_one tendsto_const_nhds
    exact one_ne_zero h10

/-- The function `t ↦ exp (c * t)` converges in `ℂ` as `t → +∞` if and only if `re c < 0` or
`c = 0`. -/
theorem exists_tendsto_exp_mul_ofReal_atTop_iff {c : ℂ} :
    (∃ L : ℂ, Tendsto (fun t : ℝ ↦ Complex.exp (c * t)) atTop (𝓝 L)) ↔ c.re < 0 ∨ c = 0 := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, ?_⟩
  · by_contra! h
    exact not_tendsto_exp_mul_ofReal_atTop h.1 h.2 hL
  · rintro (hc | rfl)
    · exact ⟨0, tendsto_exp_mul_ofReal_atTop_zero hc⟩
    · exact ⟨1, by simp⟩

/-! ### Principal complex powers along the reals and natural numbers -/

/-- When `re s < 0`, `(x : ℂ) ^ s` tends to `0` as the real base `x` tends to `+∞`. -/
theorem tendsto_ofReal_cpow_atTop_zero {s : ℂ} (hs : s.re < 0) :
    Tendsto (fun x : ℝ ↦ (x : ℂ) ^ s) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_rpow_neg_atTop (neg_pos.mpr hs)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_neg]

/-- When `0 ≤ re s` and `s ≠ 0`, `(x : ℂ) ^ s` has no finite limit in `ℂ` as `x → +∞`. -/
theorem not_tendsto_ofReal_cpow_atTop {s L : ℂ} (hre : 0 ≤ s.re) (hs : s ≠ 0) :
    ¬ Tendsto (fun x : ℝ ↦ (x : ℂ) ^ s) atTop (𝓝 L) := by
  intro h
  refine not_tendsto_exp_mul_ofReal_atTop hre hs ((h.comp Real.tendsto_exp_atTop).congr fun t ↦ ?_)
  rw [Function.comp_apply, ofReal_exp_cpow, mul_comm]

/-- The real-base principal power `x ↦ (x : ℂ) ^ s` converges in `ℂ` as `x → +∞` if and only if
`re s < 0` or `s = 0`. -/
theorem exists_tendsto_ofReal_cpow_atTop_iff {s : ℂ} :
    (∃ L : ℂ, Tendsto (fun x : ℝ ↦ (x : ℂ) ^ s) atTop (𝓝 L)) ↔ s.re < 0 ∨ s = 0 := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, ?_⟩
  · by_contra! h
    exact not_tendsto_ofReal_cpow_atTop h.1 h.2 hL
  · rintro (hs | rfl)
    · exact ⟨0, tendsto_ofReal_cpow_atTop_zero hs⟩
    · exact ⟨1, by simp⟩

/-- When `re s < 0`, `(n : ℂ) ^ s` tends to `0` as `n → ∞`. -/
theorem tendsto_natCast_cpow_atTop_zero {s : ℂ} (hs : s.re < 0) :
    Tendsto (fun n : ℕ ↦ (n : ℂ) ^ s) atTop (𝓝 0) :=
  (tendsto_ofReal_cpow_atTop_zero hs).comp tendsto_natCast_atTop_atTop

/-- The logarithmic rounding error `t - log ⌊exp t⌋₊` tends to `0` as `t → +∞`. -/
private theorem tendsto_sub_log_floor_exp_atTop :
    Tendsto (fun t : ℝ ↦ t - Real.log ⌊Real.exp t⌋₊) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m : ℕ ↦ Real.log (1 + 1 / (m : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ ↦ (1 : ℝ) + 1 / (m : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h1
    simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  have hupper_exp : Tendsto (fun t : ℝ ↦ Real.log (1 + 1 / (⌊Real.exp t⌋₊ : ℝ))) atTop (𝓝 0) :=
    (tendsto_comp_natFloor_iff.mpr hupper).comp Real.tendsto_exp_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_exp ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with t ht
    have hm1 : 1 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp ht)
    have hm_pos : (0 : ℝ) < ⌊Real.exp t⌋₊ := Nat.cast_pos.mpr hm1
    have hle : Real.log ⌊Real.exp t⌋₊ ≤ t :=
      (Real.log_le_iff_le_exp hm_pos).mpr (Nat.floor_le (Real.exp_nonneg t))
    linarith
  · filter_upwards [eventually_ge_atTop 0] with t ht
    have hm1 : 1 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp ht)
    have hm_pos : (0 : ℝ) < ⌊Real.exp t⌋₊ := Nat.cast_pos.mpr hm1
    have hlt : t ≤ Real.log (⌊Real.exp t⌋₊ + 1) := by
      simpa only [Real.log_exp] using
        Real.log_le_log (Real.exp_pos t) (Nat.lt_floor_add_one (Real.exp t)).le
    have hlog : Real.log (⌊Real.exp t⌋₊ + 1) - Real.log ⌊Real.exp t⌋₊ =
        Real.log (1 + 1 / (⌊Real.exp t⌋₊ : ℝ)) := by
      rw [← Real.log_div (by positivity) hm_pos.ne', add_div, div_self hm_pos.ne']
    linarith

/-- When `0 ≤ re s` and `s ≠ 0`, `(n : ℂ) ^ s` has no finite limit in `ℂ` as `n → ∞`. -/
theorem not_tendsto_natCast_cpow_atTop {s L : ℂ} (hre : 0 ≤ s.re) (hs : s ≠ 0) :
    ¬ Tendsto (fun n : ℕ ↦ (n : ℂ) ^ s) atTop (𝓝 L) := by
  intro h
  have hfloor : Tendsto (fun t : ℝ ↦ (⌊Real.exp t⌋₊ : ℂ) ^ s) atTop (𝓝 L) :=
    (tendsto_comp_natFloor_iff.mpr h).comp Real.tendsto_exp_atTop
  have herr : Tendsto (fun t : ℝ ↦ Complex.exp (((t - Real.log ⌊Real.exp t⌋₊ : ℝ) : ℂ) * s))
      atTop (𝓝 1) := by
    have hcont : Continuous fun y : ℝ ↦ Complex.exp ((y : ℂ) * s) := by fun_prop
    simpa [Function.comp_def] using (hcont.tendsto 0).comp tendsto_sub_log_floor_exp_atTop
  have hexp : Tendsto (fun t : ℝ ↦ Complex.exp (s * t)) atTop (𝓝 L) := by
    have hmul := hfloor.mul herr
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have hm1 : 1 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp ht)
    have hm0 : ⌊Real.exp t⌋₊ ≠ 0 := Nat.one_le_iff_ne_zero.mp hm1
    have hc : (⌊Real.exp t⌋₊ : ℂ) ^ s = Complex.exp ((Real.log ⌊Real.exp t⌋₊ : ℂ) * s) := by
      simpa using natCast_cpow_ofReal_mul hm0 1 s
    rw [hc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  exact not_tendsto_exp_mul_ofReal_atTop hre hs hexp

/-- The natural-base principal power `n ↦ (n : ℂ) ^ s` converges in `ℂ` as `n → ∞` if and only if
`re s < 0` or `s = 0`. -/
theorem exists_tendsto_natCast_cpow_atTop_iff {s : ℂ} :
    (∃ L : ℂ, Tendsto (fun n : ℕ ↦ (n : ℂ) ^ s) atTop (𝓝 L)) ↔ s.re < 0 ∨ s = 0 := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, ?_⟩
  · by_contra! h
    exact not_tendsto_natCast_cpow_atTop h.1 h.2 hL
  · rintro (hs | rfl)
    · exact ⟨0, tendsto_natCast_cpow_atTop_zero hs⟩
    · exact ⟨1, by simp⟩

end TauCeti
