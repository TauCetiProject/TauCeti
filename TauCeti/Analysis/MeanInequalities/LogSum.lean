/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The log-sum inequality

For a finset `s`, nonnegative reals `a i` and positive reals `b i` on `s`, the **log-sum
inequality** is

`(∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * log (a i / b i)`,

with equality exactly when `a` is proportional to `b` on `s`. A zero `a i` contributes
`0 * log 0 = 0` to the right side, which is the intended value. For the empty finset both sides
are `0` and the proportionality condition holds.

For the finite measures `μ` and `ν` with masses `a` and `b` on `s`, the Kullback-Leibler
divergence `InformationTheory.klDiv μ ν` is `∑ i ∈ s, a i * log (a i / b i) + ∑ b - ∑ a`, so
adding `∑ b - ∑ a` to both sides of the log-sum inequality gives the real form
`InformationTheory.mul_log_le_toReal_klDiv` of Mathlib's `InformationTheory.mul_log_le_klDiv`.
When `∑ a = ∑ b` the log-sum inequality is the Gibbs inequality.

## Main results

* `TauCeti.sum_mul_log_div_le`: the log-sum inequality.
* `TauCeti.sum_mul_log_div_eq_iff`: equality holds if and only if `a i = c * b i` on `s` for
  some real `c`.

The proofs are Jensen's inequality for the strictly convex function `x ↦ x * log x`
(`Real.strictConvexOn_mul_log`) with weights `b i / ∑ b` at the points `a i / b i`, and its
equality case `StrictConvexOn.eq_of_le_map_sum`.

## References

* T. M. Cover, J. A. Thomas, *Elements of Information Theory*, Theorem 2.7.1.
-/

public section

open Finset Real

namespace TauCeti

variable {κ : Type*} {s : Finset κ} {a b : κ → ℝ}

/- The two sides of the log-sum inequality are `∑ b` times the two sides of Jensen's inequality
for `x ↦ x * log x` with weights `b i / ∑ b` at the points `a i / b i`. -/
private theorem sum_mul_log_div_eq_mul_jensen (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) =
        (∑ i ∈ s, b i) * ((∑ i ∈ s, (b i / ∑ j ∈ s, b j) • (a i / b i)) *
          log (∑ i ∈ s, (b i / ∑ j ∈ s, b j) • (a i / b i))) ∧
      ∑ i ∈ s, a i * log (a i / b i) =
        (∑ i ∈ s, b i) * ∑ i ∈ s, (b i / ∑ j ∈ s, b j) • (a i / b i * log (a i / b i)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hB : 0 < ∑ i ∈ s, b i := sum_pos hb hs
  have hmean : ∑ i ∈ s, (b i / ∑ j ∈ s, b j) • (a i / b i) = (∑ i ∈ s, a i) / ∑ i ∈ s, b i := by
    rw [sum_div]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [smul_eq_mul]
    field_simp [(hb i hi).ne']
  refine ⟨by rw [hmean]; field_simp, ?_⟩
  rw [mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  simp only [smul_eq_mul]
  field_simp [(hb i hi).ne']

/-- The **log-sum inequality**: for `a ≥ 0` and `b > 0` on a finset `s`,
`(∑ a) * log ((∑ a) / ∑ b) ≤ ∑ a i * log (a i / b i)`. -/
theorem sum_mul_log_div_le (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤
      ∑ i ∈ s, a i * log (a i / b i) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hB : 0 < ∑ i ∈ s, b i := sum_pos hb hs
  obtain ⟨h₁, h₂⟩ := sum_mul_log_div_eq_mul_jensen (a := a) hb
  rw [h₁, h₂]
  gcongr
  exact convexOn_mul_log.map_sum_le (fun i hi ↦ div_nonneg (hb i hi).le hB.le)
    (by rw [← sum_div, div_self hB.ne'])
    fun i hi ↦ Set.mem_Ici.2 (div_nonneg (ha i hi) (hb i hi).le)

/-- The equality case of the **log-sum inequality**: for `a ≥ 0` and `b > 0` on a finset `s`,
`(∑ a) * log ((∑ a) / ∑ b) = ∑ a i * log (a i / b i)` if and only if `a = c * b` on `s` for some
real `c`. -/
theorem sum_mul_log_div_eq_iff (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) =
        ∑ i ∈ s, a i * log (a i / b i) ↔
      ∃ c : ℝ, ∀ i ∈ s, a i = c * b i := by
  constructor
  · intro h
    rcases s.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
    · simp
    have hB : 0 < ∑ i ∈ s, b i := sum_pos hb ⟨j, hj⟩
    obtain ⟨h₁, h₂⟩ := sum_mul_log_div_eq_mul_jensen (a := a) hb
    rw [h₁, h₂] at h
    have hp := strictConvexOn_mul_log.eq_of_le_map_sum
      (fun i hi ↦ div_pos (hb i hi) hB) (by rw [← sum_div, div_self hB.ne'])
      (fun i hi ↦ Set.mem_Ici.2 (div_nonneg (ha i hi) (hb i hi).le))
      (mul_left_cancel₀ hB.ne' h).ge
    refine ⟨a j / b j, fun i hi ↦ ?_⟩
    rw [hp hj hi, div_mul_cancel₀ _ (hb i hi).ne']
  · rintro ⟨c, hc⟩
    have hA : ∑ i ∈ s, a i = c * ∑ i ∈ s, b i := by
      rw [mul_sum]
      exact sum_congr rfl hc
    have hR : ∑ i ∈ s, a i * log (a i / b i) = c * (∑ i ∈ s, b i) * log c := by
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun i hi ↦ ?_
      rw [hc i hi, mul_div_assoc, div_self (hb i hi).ne', mul_one]
    rw [hA, hR]
    rcases eq_or_ne (∑ i ∈ s, b i) 0 with hB | hB
    · simp [hB]
    · rw [mul_div_assoc, div_self hB, mul_one]

end TauCeti
