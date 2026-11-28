/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
public import TauCeti.NumberTheory.Mertens.Basic
import TauCeti.Data.Nat.Totient.LowerBound

/-!
# The minimal order of the totient

Euler's product formula gives `n / φ(n) = ∏_{p ∣ n} (1 - p⁻¹)⁻¹`. Splitting the prime divisors of
`n` at a real `y > 1` bounds this by `∏_{p ≤ y} (1 - p⁻¹)⁻¹ * exp (2 log n / (y log y))`
(`Nat.div_totient_le_prod_primesLE_mul_exp`), and Mertens's third theorem evaluates the Euler
product as `e^γ log y + O(1)`. The choice `y = log n` gives

`n / φ(n) ≤ (e^γ log log n + C) exp (2 / log log n)`

with an absolute constant `C`. Hence `n / φ(n) ≤ C' log log n` for all `n ≥ 3`, and
`n / φ(n) ≤ (e^γ + ε) log log n` for all large `n`, which is the upper half of Landau's theorem
`limsup n / (φ(n) log log n) = e^γ`.

## Main results

* `TauCeti.exists_div_totient_le_add_mul_exp`: `n / φ(n) ≤ (e^γ log log n + C) *
  exp (2 / log log n)` with an absolute constant `C`.
* `TauCeti.exists_div_totient_le_mul_log_log`, `TauCeti.exists_one_div_totient_le_mul_log_log_div`:
  `n / φ(n) ≤ C log log n` and `1 / φ(n) ≤ C log log n / n` for `n ≥ 3`.
* `TauCeti.eventually_div_totient_le_mul_log_log`: `n / φ(n) ≤ (e^γ + ε) log log n` for all large
  `n`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Theorem 2.9.
* A. N. Skorobogatov and E. Sofos, *Schinzel Hypothesis on average and rational points*,
  Invent. Math. 231 (2023), equation (3.7).
-/

public section

open Filter Finset
open scoped Nat Topology

namespace TauCeti

/-- **The minimal order of the totient, with the sharp constant.** There is an absolute constant
`C` with `n / φ(n) ≤ (e^γ log log n + C) exp (2 / log log n)` for every `n`. The estimate has
content for `log n ≥ 2`, where it comes from Mertens's third theorem; the finitely many smaller
`n` are absorbed in `C`. -/
theorem exists_div_totient_le_add_mul_exp :
    ∃ C : ℝ, ∀ n : ℕ,
      (n : ℝ) / φ n ≤
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) + C) *
          Real.exp (2 / Real.log (Real.log n)) := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le
  obtain ⟨M, hM⟩ := ((range ⌈Real.exp 2⌉₊).image fun n : ℕ ↦
    (n : ℝ) / φ n * Real.exp (-(2 / Real.log (Real.log n))) -
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)).exists_le
  refine ⟨max C₁ M, fun n ↦ ?_⟩
  rcases lt_or_ge (Real.log n) 2 with hn | hn
  · have hmem : n ∈ range ⌈Real.exp 2⌉₊ := by
      rcases eq_or_ne n 0 with rfl | hn0
      · simpa using Real.exp_pos 2
      · exact mem_range.2 (Nat.lt_ceil.2 ((Real.log_lt_iff_lt_exp (by positivity)).1 hn))
    have h := hM _ (mem_image_of_mem _ hmem)
    calc (n : ℝ) / φ n
        = (n : ℝ) / φ n * Real.exp (-(2 / Real.log (Real.log n))) *
            Real.exp (2 / Real.log (Real.log n)) := by
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ _ := by gcongr; linarith [le_max_right C₁ M]
  · have hlog : 0 < Real.log n := zero_lt_two.trans_le hn
    have h := Nat.div_totient_le_prod_primesLE_mul_exp n (one_lt_two.trans_le hn)
    rw [mul_comm 2, mul_div_mul_left _ _ hlog.ne'] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    linarith [(abs_le.1 (hC₁ _ hn)).2, le_max_left C₁ M]

/-- **The minimal order of the totient.** There is an absolute constant `C > 0` with
`n / φ(n) ≤ C log log n` for every `n ≥ 3`. -/
theorem exists_div_totient_le_mul_log_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → (n : ℝ) / φ n ≤ C * Real.log (Real.log n) := by
  obtain ⟨C₁, hC₁⟩ := exists_div_totient_le_add_mul_exp
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hA : 0 < (Real.exp Real.eulerMascheroniConstant + |C₁|) * Real.exp 2 := by positivity
  have hB : 0 < Real.exp (Real.exp 1) / Real.log (Real.log 3) := div_pos (Real.exp_pos _) hll3
  refine ⟨(Real.exp Real.eulerMascheroniConstant + |C₁|) * Real.exp 2 +
    Real.exp (Real.exp 1) / Real.log (Real.log 3), add_pos hA hB, fun n hn ↦ ?_⟩
  have hn3 : (3 : ℝ) ≤ n := mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log n :=
    zero_lt_one.trans (hlog3.trans_le (Real.log_le_log (by norm_num) hn3))
  have hL3 : Real.log (Real.log 3) ≤ Real.log (Real.log n) :=
    Real.log_le_log (zero_lt_one.trans hlog3) (Real.log_le_log (by norm_num) hn3)
  have hL0 : 0 < Real.log (Real.log n) := hll3.trans_le hL3
  rw [add_mul]
  rcases le_or_gt 1 (Real.log (Real.log n)) with hL | hL
  · calc (n : ℝ) / φ n
        ≤ (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) + C₁) *
            Real.exp (2 / Real.log (Real.log n)) := hC₁ n
      _ ≤ (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) +
            |C₁| * Real.log (Real.log n)) * Real.exp 2 := by
          gcongr
          · exact (le_abs_self C₁).trans (le_mul_of_one_le_right (abs_nonneg C₁) hL)
          · exact div_le_self zero_le_two hL
      _ = (Real.exp Real.eulerMascheroniConstant + |C₁|) * Real.exp 2 *
            Real.log (Real.log n) := by ring
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hB.le hL0.le)
  · have hn_lt : (n : ℝ) < Real.exp (Real.exp 1) :=
      (Real.log_lt_iff_lt_exp hn0).1 ((Real.log_lt_iff_lt_exp hlogn).1 hL)
    have hφ : (1 : ℝ) ≤ φ n := mod_cast Nat.totient_pos.2 (by omega)
    calc (n : ℝ) / φ n ≤ n := div_le_self hn0.le hφ
      _ ≤ Real.exp (Real.exp 1) / Real.log (Real.log 3) * Real.log (Real.log 3) := by
          rw [div_mul_cancel₀ _ hll3.ne']
          exact hn_lt.le
      _ ≤ Real.exp (Real.exp 1) / Real.log (Real.log 3) * Real.log (Real.log n) := by gcongr
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hA.le hL0.le)

/-- **The size of `1 / φ(n)`.** There is an absolute constant `C > 0` with
`1 / φ(n) ≤ C log log n / n` for every `n ≥ 3`. -/
theorem exists_one_div_totient_le_mul_log_log_div :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → 1 / (φ n : ℝ) ≤ C * Real.log (Real.log n) / n := by
  obtain ⟨C, hC, h⟩ := exists_div_totient_le_mul_log_log
  refine ⟨C, hC, fun n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) < n := mod_cast (by omega : 0 < n)
  rw [le_div_iff₀ hn0, one_div_mul_eq_div]
  exact h n hn

/-- **The upper half of Landau's theorem on the totient.** For every `ε > 0`,
`n / φ(n) ≤ (e^γ + ε) log log n` for all sufficiently large `n`. -/
theorem eventually_div_totient_le_mul_log_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / φ n ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log n) := by
  obtain ⟨C, hC⟩ := exists_div_totient_le_add_mul_exp
  have hlim : Tendsto (fun L : ℝ ↦ (Real.exp Real.eulerMascheroniConstant + C / L) *
      Real.exp (2 / L)) atTop (𝓝 ((Real.exp Real.eulerMascheroniConstant + 0) * Real.exp 0)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).mul
      ((Real.continuous_exp.tendsto 0).comp (tendsto_const_nhds.div_atTop tendsto_id))
  rw [add_zero, Real.exp_zero, mul_one] at hlim
  have hL : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hL.eventually (hlim.eventually_lt_const (lt_add_of_pos_right _ hε)),
    hL.eventually_gt_atTop 0] with n hn hL0
  calc (n : ℝ) / φ n
      ≤ (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) + C) *
          Real.exp (2 / Real.log (Real.log n)) := hC n
    _ = (Real.exp Real.eulerMascheroniConstant + C / Real.log (Real.log n)) *
          Real.exp (2 / Real.log (Real.log n)) * Real.log (Real.log n) := by
        field_simp
    _ ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log n) := by gcongr

end TauCeti
