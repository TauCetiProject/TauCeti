/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers of a ratio of radii

Scaling arguments compare a quantity on a ball of radius `r` with the same quantity on a larger
ball of radius `R`, and the comparison is expressed through real powers of the ratio `r / R`.
This file collects the rearrangements of such powers that these arguments need.

* A power of `r` is a power of `r / R` times a power of `R`. So a bound `c R^a ≤ M` on a
  dimensionless constant gives `r^{2a} c² ≤ (r / R)^{2a} M²`, and a bound `c² R^{d+2a} ≤ V` gives
  `r^{2a} c² r^d ≤ V (r / R)^{d+2a}`.
* For `b ≤ a`, such a quantity also decays like `(r / R)^{d+2b}`, with the constant
  `(R^{a-b} c)² R^{d+2b}`.
* A power `(r / R)^γ` of the ratio splits as `R^{-γ} r^γ`, and shrinking the outer radius by a
  factor `θ` multiplies it by `θ^{-γ}`.
* A constant of the form `(R^{d/2+a} Q)²`, which is the natural scale of an `L²` quantity on a
  ball of radius `R` in dimension `d`, equals `R^d (R^a Q)²` and bounds `c² R^{d+2a}` for
  `0 ≤ c ≤ Q`.
-/

public section

namespace Real

/-- `r^{2a} c² ≤ (r / R)^{2a} M²` when `c R^a ≤ M`. -/
theorem rpow_mul_sq_le {r R c M a : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 ≤ c)
    (hM : c * R ^ a ≤ M) : r ^ (2 * a) * c ^ 2 ≤ (r / R) ^ (2 * a) * M ^ 2 := by
  have h1 : r ^ (2 * a) = (r / R) ^ (2 * a) * (R ^ a) ^ 2 := by
    rw [div_rpow hr.le hR.le, ← rpow_natCast, ← rpow_mul hR.le, Nat.cast_two,
      mul_comm a 2, div_mul_cancel₀ _ (rpow_pos_of_pos hR _).ne']
  rw [h1, mul_assoc, ← mul_pow, mul_comm (R ^ a)]
  gcongr

/-- `r^{2a} c² r^d ≤ V (r / R)^{d+2a}` when `c² R^{d+2a} ≤ V`. -/
theorem rpow_mul_mul_rpow_le {r R c V a d : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hc : c ^ 2 * R ^ (d + 2 * a) ≤ V) :
    r ^ (2 * a) * (c ^ 2 * r ^ d) ≤ V * (r / R) ^ (d + 2 * a) := by
  have h1 : r ^ (2 * a) * (c ^ 2 * r ^ d) =
      (r / R) ^ (d + 2 * a) * (c ^ 2 * R ^ (d + 2 * a)) := by
    rw [div_rpow hr.le hR.le, add_comm d, rpow_add hr]
    field_simp
  rw [h1, mul_comm V]
  gcongr

/-- `r^{2a} c² r^d ≤ (R^{a-b} c)² R^{d+2b} (r / R)^{d+2b}` for `0 < r ≤ R` and `b ≤ a`: a quantity
of order `r^{d+2a}` decays at least with the smaller exponent `d + 2b`, at the cost of the
dimensionless factor `R^{a-b}`. -/
theorem rpow_mul_mul_rpow_le_mul_rpow_of_le {r R c a b d : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hba : b ≤ a) :
    r ^ (2 * a) * (c ^ 2 * r ^ d) ≤
      (R ^ (a - b) * c) ^ 2 * R ^ (d + 2 * b) * (r / R) ^ (d + 2 * b) := by
  have hR : 0 < R := hr.trans_le hrR
  have hc : (R ^ (a - b) * c) ^ 2 * R ^ (d + 2 * b) = c ^ 2 * R ^ (d + 2 * a) := by
    rw [mul_pow, ← rpow_mul_natCast hR.le, mul_right_comm, ← rpow_add hR]
    ring_nf
  rw [hc]
  refine (rpow_mul_mul_rpow_le hr hR le_rfl).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact rpow_le_rpow_of_exponent_ge (div_pos hr hR) (div_le_one_of_le₀ hrR hR.le) (by linarith)

/-- `(r / R)^γ = R^{-γ} r^γ`. -/
theorem div_rpow_eq_rpow_neg_mul_rpow {r R γ : ℝ} (hr : 0 ≤ r) (hR : 0 < R) :
    (r / R) ^ γ = R ^ (-γ) * r ^ γ := by
  rw [div_rpow hr hR.le, rpow_neg hR.le, div_eq_inv_mul]

/-- `(r / (θ R))^γ = θ^{-γ} (r / R)^γ`. -/
theorem div_mul_rpow_eq {r θ R γ : ℝ} (hr : 0 ≤ r) (hθ : 0 < θ) (hR : 0 < R) :
    (r / (θ * R)) ^ γ = θ ^ (-γ) * (r / R) ^ γ := by
  rw [div_mul_eq_div_div_swap, div_eq_inv_mul (r / R), mul_rpow (inv_nonneg.2 hθ.le)
    (div_nonneg hr hR.le), inv_rpow hθ.le, rpow_neg hθ.le]

/-- `(R^{d/2+a} Q)² = R^d (R^a Q)²`. -/
theorem rpow_div_two_add_mul_sq {R d a : ℝ} (Q : ℝ) (hR : 0 < R) :
    (R ^ (d / 2 + a) * Q) ^ 2 = R ^ d * (R ^ a * Q) ^ 2 := by
  rw [mul_pow, mul_pow, ← rpow_mul_natCast hR.le, ← rpow_mul_natCast hR.le, Nat.cast_two,
    add_mul, div_mul_cancel₀ _ two_ne_zero, rpow_add hR]
  ring

/-- `c² R^{d+2a} ≤ (R^{d/2+a} Q)²` when `0 ≤ c ≤ Q`. -/
theorem sq_mul_rpow_add_two_mul_le {R c Q d a : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hcQ : c ≤ Q) :
    c ^ 2 * R ^ (d + 2 * a) ≤ (R ^ (d / 2 + a) * Q) ^ 2 := by
  have h : R ^ (d + 2 * a) = (R ^ (d / 2 + a)) ^ 2 := by
    rw [← rpow_mul_natCast hR.le, Nat.cast_two, add_mul, div_mul_cancel₀ _ two_ne_zero, mul_comm]
  rw [h, mul_pow, mul_comm]
  gcongr

end Real
