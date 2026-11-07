/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Elementary Gamma upper bounds on the positive real axis

Monotonicity and the factorial values bound Gamma by `exp (O(x log x))`.
The recurrence extends this to every half-line with positive lower endpoint.
Consequently the Gamma moments arising from exponentially decaying Mellin kernels
are bounded by `exp (C (1+R) log (2+R))` uniformly for `R ≥ 0`.

These estimates suffice for order-one growth of split Mellin integrals.
They require no sectorial asymptotic expansion.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1.
-/

public section

open Real Set

namespace Real

/-- For real arguments at least two, Gamma is bounded by the next power of the argument. -/
theorem Gamma_le_add_one_rpow {x : ℝ} (hx : 2 ≤ x) :
    Gamma x ≤ (x + 1) ^ (x + 1) := by
  have hxc : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hcx : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
  have hn : Gamma x ≤ Gamma ((⌈x⌉₊ : ℝ) + 1) :=
    Gamma_strictMonoOn_Ici.monotoneOn hx (show 2 ≤ (⌈x⌉₊ : ℝ) + 1 by linarith)
      (show x ≤ (⌈x⌉₊ : ℝ) + 1 by linarith)
  rw [Gamma_nat_eq_factorial] at hn
  calc
    Gamma x ≤ (⌈x⌉₊.factorial : ℝ) := hn
    _ ≤ (⌈x⌉₊ : ℝ) ^ ⌈x⌉₊ := by exact_mod_cast Nat.factorial_le_pow ⌈x⌉₊
    _ = (⌈x⌉₊ : ℝ) ^ (⌈x⌉₊ : ℝ) := (rpow_natCast _ _).symm
    _ ≤ (x + 1) ^ (⌈x⌉₊ : ℝ) := rpow_le_rpow (Nat.cast_nonneg _) hcx (Nat.cast_nonneg _)
    _ ≤ (x + 1) ^ (x + 1) := rpow_le_rpow_of_exponent_le (by linarith) hcx

/-- For real arguments at least two, Gamma is bounded by `exp ((x+1) log (x+1))`. -/
theorem Gamma_le_exp_mul_log {x : ℝ} (hx : 2 ≤ x) :
    Gamma x ≤ exp ((x + 1) * log (x + 1)) := by
  simpa only [rpow_def_of_pos (by linarith : 0 < x + 1), mul_comm] using
    Gamma_le_add_one_rpow hx

/-- A positive lower bound on the argument gives a uniform Gamma upper bound. -/
theorem Gamma_le_exp_mul_log_add {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    Gamma x ≤ exp ((x + 3) * log (x + 3) + (a * (a + 1))⁻¹) := by
  have hx : 0 < x := ha.trans_le hax
  have hden : 0 < a * (a + 1) := by positivity
  have hr : Gamma (x + 2) = x * (x + 1) * Gamma x := by
    rw [show x + 2 = (x + 1) + 1 by ring, Gamma_add_one (by positivity), Gamma_add_one hx.ne']
    ring
  have hG : Gamma x ≤ Gamma (x + 2) / (a * (a + 1)) := by
    apply (le_div_iff₀ hden).mpr
    rw [hr]
    nlinarith [Gamma_pos_of_pos hx, mul_le_mul hax (show a + 1 ≤ x + 1 by linarith)
      (by positivity : 0 ≤ a + 1) hx.le]
  calc
    Gamma x ≤ Gamma (x + 2) / (a * (a + 1)) := hG
    _ ≤ exp ((x + 3) * log (x + 3)) / (a * (a + 1)) := by
      gcongr
      convert Gamma_le_exp_mul_log (x := x + 2) (by linarith) using 1; ring_nf
    _ ≤ exp ((x + 3) * log (x + 3)) * exp ((a * (a + 1))⁻¹) := by
      rw [div_eq_mul_inv]
      gcongr
      linarith [add_one_le_exp ((a * (a + 1))⁻¹)]
    _ = _ := (exp_add _ _).symm

/-- A scaled Gamma moment has logarithmic-exponential growth in its nonnegative exponent. -/
theorem exists_rpow_mul_Gamma_div_le_exp_mul_log {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    ∃ C > 0, ∀ R ≥ 0,
      c ^ (-(R + 1) / α) * Gamma ((R + 1) / α) / α ≤
        exp (C * (1 + R) * log (2 + R)) := by
  let a := α⁻¹
  have ha : 0 < a := inv_pos.mpr hα
  let K := a + 3
  have hK : 0 < K := by dsimp [K]; positivity
  let B := (a * (a + 1))⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  let D := B + a
  have hD : 0 < D := add_pos hB ha
  let C := 2 * D + 2 * |log c| * a + K * (2 * K + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun R hR ↦ ?_⟩
  let x := (R + 1) / α
  have hax : a ≤ x := by
    dsimp [a, x]
    exact (le_div_iff₀ hα).mpr (by rw [inv_mul_cancel₀ hα.ne']; linarith)
  have hx : 0 < x := ha.trans_le hax
  have hxeq : x = a * (1 + R) := by dsimp [x, a]; ring
  have hy : 0 < x + 3 := by positivity
  have hyK : x + 3 ≤ K * (1 + R) := by dsimp [K]; rw [hxeq]; nlinarith
  have hL : (1 / 2 : ℝ) ≤ log (2 + R) := by
    have h2 : (1 / 2 : ℝ) ≤ log 2 := by
      convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
    exact h2.trans (log_le_log (by norm_num) (by linarith))
  have hlog : log (x + 3) ≤ log K + log (2 + R) := by
    rw [← log_mul hK.ne' (by positivity : 2 + R ≠ 0)]
    apply log_le_log hy
    exact hyK.trans (mul_le_mul_of_nonneg_left (by linarith : 1 + R ≤ 2 + R) hK.le)
  have hlogK : log K ≤ K := (log_le_sub_one_of_pos hK).trans (by linarith)
  have hlog' : log (x + 3) ≤ (2 * K + 1) * log (2 + R) := by
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * K)]
  have hylog : (x + 3) * log (x + 3) ≤
      K * (2 * K + 1) * (1 + R) * log (2 + R) := by
    calc
      _ ≤ (K * (1 + R)) * ((2 * K + 1) * log (2 + R)) :=
        mul_le_mul hyK hlog' (log_nonneg (by linarith)) (by positivity)
      _ = _ := by ring
  have hpref : c ^ (-(R + 1) / α) ≤ exp (|log c| * x) := by
    rw [rpow_def_of_pos hc]
    apply exp_le_exp.mpr
    have he : -(R + 1) / α = -x := by dsimp [x]; ring
    rw [he, mul_neg, ← neg_mul]
    exact mul_le_mul_of_nonneg_right (neg_le_abs (log c)) hx.le
  have hGi := Gamma_le_exp_mul_log_add ha hax
  have hai : α⁻¹ ≤ exp a := by change a ≤ exp a; linarith [add_one_le_exp a]
  have hbound : c ^ (-(R + 1) / α) * Gamma x / α ≤
      exp (|log c| * x + (x + 3) * log (x + 3) + D) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (exp (|log c| * x) * exp ((x + 3) * log (x + 3) + B)) * exp a :=
        mul_le_mul (mul_le_mul hpref hGi (Gamma_pos_of_pos hx).le (by positivity)) hai
          (inv_nonneg.mpr hα.le) (by positivity)
      _ = _ := by dsimp [D]; rw [← exp_add, ← exp_add]; congr 1; ring
  apply hbound.trans
  apply exp_le_exp.mpr
  have hD' : D ≤ 2 * D * (1 + R) * log (2 + R) := by
    have hRL : (1 / 2 : ℝ) ≤ (1 + R) * log (2 + R) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hRL (by positivity : 0 ≤ 2 * D)]
  have hx' : |log c| * x ≤ 2 * |log c| * a * (1 + R) * log (2 + R) := by
    rw [hxeq]
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * |log c| * a * (1 + R) by positivity)]
  dsimp [C]
  nlinarith

end Real
