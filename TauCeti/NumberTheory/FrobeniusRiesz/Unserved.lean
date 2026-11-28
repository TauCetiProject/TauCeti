/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.PrimePowerBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Full contributions of unserved Frobenius Riesz terms

When a divisibility bound does not cover a prime, or covers only some of its tops, charge the
entire Riesz contribution from the other tops. The sum in `sum_unserved_frobenius_ramps_le` has one
odd-power contribution per lift and selected top; its bound uses the logarithmically weighted
count of those tops. At the exceptional ramified prime the coefficient is `log d` rather than
`2 log d`, with all positive powers included. When `d ≥ x²` and `x ≥ 4`, a top weight at most
`(x + 1) * b` costs at most `b` per lift and top.
These are the two full-contribution estimates used in L. Alpöge's
`Formalism.RankGapBounds.WeightedMeanData.Data.LoP`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Finset

namespace TauCeti

/-- Bound the entire odd-power contribution for any selection `T p` of tops at each base `p`.
The bounds on the caps and top sizes concern only the terms being charged. In particular, using
a constant `T` charges every top for each selected prime. -/
theorem sum_unserved_frobenius_ramps_le {ι τ : Type*} (P : Finset ℕ) (J : Finset ι)
    (T : ℕ → Finset τ) (L : ℕ → ℕ) (a : τ → ℝ) (w : ℕ → ι → τ → ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ p ∈ P, ∀ t ∈ T p, a t ≤ A)
    (hw : ∀ p ∈ P, ∀ j ∈ J, ∀ t ∈ T p, ∀ k ∈ (Icc 1 (L p)).filter Odd,
      0 ≤ w p j t k) :
    (∑ p ∈ P, (2 * Real.log p) * ∑ j ∈ J, ∑ t ∈ T p, ∑ k ∈ (Icc 1 (L p)).filter Odd,
      max (a t / (p : ℝ) ^ k - w p j t k) 0) ≤
      (8 / 3 : ℝ) * J.card * A * ∑ p ∈ P, (Real.log p / p) * (T p).card := by
  rw [mul_sum]
  refine sum_le_sum fun p hP ↦ ?_
  by_cases hp : p < 2
  · have hp' : p = 0 ∨ p = 1 := by omega
    rcases hp' with rfl | rfl <;> simp
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast Nat.le_of_not_gt hp
  have hp₁ : (1 : ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp₁.le
  have hrat : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ (4 / 3) / p := by
    have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    have hp₀ : (0 : ℝ) < p := by linarith
    rw [div_le_div_iff₀ hden hp₀]
    nlinarith
  calc
    _ ≤ (2 * Real.log p) * ∑ j ∈ J, ∑ t ∈ T p, A * ((4 / 3) / p) := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun j hj ↦ sum_le_sum fun t ht ↦ ?_)
        (mul_nonneg (by norm_num) hlog)
      calc
        _ ≤ ∑ k ∈ (Icc 1 (L p)).filter Odd, max (A / (p : ℝ) ^ k - w p j t k) 0 :=
          sum_le_sum fun _ _ ↦ by gcongr; exact ha p hP t ht
        _ ≤ A * (p : ℝ) / ((p : ℝ) ^ 2 - 1) :=
          sum_max_div_odd_pow_sub_le _ hA hp₁ (fun _ hk ↦ (mem_filter.mp hk).2) _
            (hw p hP j hj t ht)
        _ ≤ _ := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hrat hA
    _ = _ := by simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv]; ring

/-- The exceptional ramified term in the split-ramification formula costs at most `b` per lift
and top. The estimate allows all positive exponents and arbitrary nonnegative caps, including
ones obtained by evaluating the cap function on the exceptional Frobenius coset. -/
theorem sum_exceptional_frobenius_ramps_le {ι τ : Type*} (J : Finset ι) (T : Finset τ) (L : ℕ)
    (a : τ → ℝ) (w : ι → τ → ℕ → ℝ) {x b : ℝ} {d : ℕ}
    (hx : 4 ≤ x) (hd : x ^ 2 ≤ d) (hb : 0 ≤ b) (ha : ∀ t ∈ T, a t ≤ (x + 1) * b)
    (hw : ∀ j ∈ J, ∀ t ∈ T, ∀ k ∈ Icc 1 L, 0 ≤ w j t k) :
    Real.log d * (∑ j ∈ J, ∑ t ∈ T, ∑ k ∈ Icc 1 L, max (a t / (d : ℝ) ^ k - w j t k) 0) ≤
      J.card * T.card * b := by
  have hd₁ : (1 : ℝ) < d := by nlinarith
  have hlog : 0 ≤ Real.log d := Real.log_nonneg hd₁.le
  have hxb : 0 ≤ (x + 1) * b := mul_nonneg (by linarith) hb
  -- At `y = √d ≥ 4`, the tangent bound for log at 4 gives `2 log y ≤ y - 1`.
  have hcost : (x + 1) * (Real.log d / (d - 1)) ≤ 1 := by
    let y := √(d : ℝ)
    have hxy : x ≤ y := (Real.le_sqrt (by linarith) (by positivity)).2 hd
    have hy : 4 ≤ y := hx.trans hxy
    have hy₂ : y ^ 2 = d := Real.sq_sqrt (by positivity)
    have hlogd : Real.log d ≤ y - 1 := by
      have ht := Real.log_le_sub_one_of_pos (x := y / 4) (by linarith)
      have htwo : (2 : ℝ) ^ 2 = 4 := by norm_num
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        simpa only [Nat.cast_ofNat, htwo] using Real.log_pow 2 2
      rw [Real.log_div (by linarith) (by norm_num), hlog4] at ht
      rw [← hy₂, Real.log_pow]
      norm_num at ht ⊢
      linarith only [ht, hy, Real.log_two_lt_d9]
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < (d : ℝ) - 1), one_mul]
    calc
      _ ≤ (y + 1) * (y - 1) :=
        mul_le_mul (by linarith) hlogd hlog (by linarith)
      _ = _ := by nlinarith only [hy₂]
  calc
    Real.log d * (∑ j ∈ J, ∑ t ∈ T, ∑ k ∈ Icc 1 L,
        max (a t / (d : ℝ) ^ k - w j t k) 0) ≤
        Real.log d * (∑ j ∈ J, ∑ t ∈ T, ((x + 1) * b) / (d - 1)) := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun j hj ↦ sum_le_sum fun t ht ↦ ?_) hlog
      calc
        _ ≤ ∑ k ∈ Icc 1 L, max (((x + 1) * b) / (d : ℝ) ^ k - w j t k) 0 :=
          sum_le_sum fun _ _ ↦ by gcongr; exact ha t ht
        _ ≤ _ := sum_max_div_pow_sub_le _ hxb hd₁ (fun _ hk ↦ (mem_Icc.mp hk).1) _ (hw j hj t ht)
    _ = J.card * T.card * (b * ((x + 1) * (Real.log d / (d - 1)))) := by
      simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv]
      ring
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hb hcost)
        (mul_nonneg (Nat.cast_nonneg J.card) (Nat.cast_nonneg T.card) :
          0 ≤ (J.card : ℝ) * T.card)

end TauCeti
