/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.Taylor.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# First- and second-order forward differences of real powers

For every real exponent `α` and real numbers `0 ≤ h ≤ x`, the first- and second-order forward
differences of `t ↦ t ^ α` satisfy the explicit uniform bounds
`|(x + h) ^ α - x ^ α| ≤ max 1 (2 ^ (α - 1)) * |α| * x ^ (α - 1) * h` and
`|((x + h) ^ α - x ^ α) - α * h * x ^ (α - 1)| ≤
  2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * x ^ (α - 2) * h ^ 2`.
At `h = 0` both sides vanish for every `x` (including `x ≤ 0`), while for `0 < h ≤ x` positivity of
`x` holds automatically; the factor `max 1 (2 ^ β)` accounts uniformly for both signs of the
derivative exponent `β` across `[x, x + h] ⊆ [x, 2 * x]`.

Specializing to unit step `h = 1` gives the forward-difference expansion
`(x ^ α - (x + 1) ^ α) + α * x ^ (α - 1) = O(α * (α - 1) * x ^ (α - 2))` uniformly on `[1, ∞)`,
hence as `x → ∞` and along natural indices `j → ∞`. Retaining the scalar factor `α * (α - 1)` on
the right-hand side makes the asymptotic estimate valid for every real `α`, including `α = 0` and
`α = 1` where both sides vanish identically. This avoids a spurious logarithmic term when summing
the second-order remainder at `α = 1` in summation by parts.

## Main results

* `Real.abs_add_rpow_sub_rpow_le`: explicit first-order increment bound for `0 ≤ h ≤ x`.
* `Real.abs_add_rpow_sub_rpow_sub_mul_le`: explicit second-order Taylor remainder bound with the
  sharp constant `1 / 2` for `0 ≤ h ≤ x`.
* `Real.abs_rpow_sub_add_one_rpow_le` and `Real.abs_rpow_sub_add_one_rpow_add_mul_le`:
  unit-step specializations for `1 ≤ x`.
* `Real.isBigO_rpow_sub_add_one_rpow_atTop`: `x ^ α - (x + 1) ^ α = O(α * x ^ (α - 1))`.
* `Real.isBigO_rpow_sub_add_one_rpow_add_mul_principal_Ici`,
  `Real.isBigO_rpow_sub_add_one_rpow_add_mul_atTop`, and
  `Real.isBigO_natCast_rpow_sub_add_one_rpow_add_mul_atTop`: uniform and asymptotic forms of
  `(x ^ α - (x + 1) ^ α) + α * x ^ (α - 1) = O(α * (α - 1) * x ^ (α - 2))`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(ii), formula 2.10.15.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
-/

public section

open Asymptotics Filter Set

namespace Real

/-- **First-order forward difference of a real power.** For every real `α` and `0 ≤ h ≤ x`,
`|(x + h) ^ α - x ^ α| ≤ max 1 (2 ^ (α - 1)) * |α| * x ^ (α - 1) * h`. -/
theorem abs_add_rpow_sub_rpow_le (α : ℝ) {x h : ℝ} (hh₀ : 0 ≤ h) (hhx : h ≤ x) :
    |(x + h) ^ α - x ^ α| ≤ max 1 (2 ^ (α - 1)) * |α| * x ^ (α - 1) * h := by
  rcases hh₀.eq_or_lt with rfl | hh
  · simp
  have hx : 0 < x := hh.trans_le hhx
  let C : ℝ := max 1 (2 ^ (α - 1)) * |α| * x ^ (α - 1)
  have hderiv : ∀ t ∈ Icc 0 h,
      HasDerivWithinAt (fun s : ℝ ↦ (x + s) ^ α) (α * (x + t) ^ (α - 1)) (Icc 0 h) t := by
    intro t ht
    have hxt : 0 < x + t := add_pos_of_pos_of_nonneg hx ht.1
    have hd := (Real.hasDerivAt_rpow_const (x := x + t) (p := α) (Or.inl hxt.ne')).comp t
      ((hasDerivAt_id t).const_add x)
    simpa only [Function.comp_def, id_eq, mul_one] using hd.hasDerivWithinAt
  have hbound : ∀ t ∈ Icc 0 h, ‖α * (x + t) ^ (α - 1)‖ ≤ C := by
    intro t ht
    have hxt : 0 < x + t := add_pos_of_pos_of_nonneg hx ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hxt _), mul_comm |α|]
    have hle := Real.add_rpow_le_max_two_rpow_mul (α - 1) ht.1 (ht.2.trans hhx)
    calc (x + t) ^ (α - 1) * |α| ≤ (max 1 (2 ^ (α - 1)) * x ^ (α - 1)) * |α| :=
          mul_le_mul_of_nonneg_right hle (abs_nonneg α)
      _ = C := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc 0 h)
    (left_mem_Icc.mpr hh₀) (right_mem_Icc.mpr hh₀)
  simpa only [Real.norm_eq_abs, add_zero, sub_zero, abs_of_nonneg hh₀, C] using hmvt

/-- **Second-order forward difference of a real power.** For every real `α` and `0 ≤ h ≤ x`,
`|((x + h) ^ α - x ^ α) - α * h * x ^ (α - 1)| ≤
  2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * x ^ (α - 2) * h ^ 2`. -/
theorem abs_add_rpow_sub_rpow_sub_mul_le (α : ℝ) {x h : ℝ} (hh₀ : 0 ≤ h) (hhx : h ≤ x) :
    |((x + h) ^ α - x ^ α) - α * h * x ^ (α - 1)| ≤
      2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * x ^ (α - 2) * h ^ 2 := by
  rcases hh₀.eq_or_lt with rfl | hh
  · simp
  have hx : 0 < x := hh.trans_le hhx
  let M : ℝ := max 1 (2 ^ (α - 2)) * |α * (α - 1)| * x ^ (α - 2)
  have htaylor := TauCeti.abs_sub_taylorWithinEval_le (f := fun s : ℝ ↦ s ^ α) (n := 1) (M := M)
    (x₀ := x) (x := x + h)
    (by
      rw [uIcc_of_le (by linarith)]
      exact fun t ht ↦ Real.contDiffAt_rpow_const_of_ne (hx.trans_le ht.1).ne')
    (by
      rw [uIoo_of_le (by linarith)]
      intro t ht
      have ht₀ : 0 < t := hx.trans ht.1
      rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_rpow_const', deriv_const_mul_field,
        Real.deriv_rpow_const]
      have hexp : α - 1 - 1 = α - 2 := by ring
      rw [hexp, ← mul_assoc, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht₀ _)]
      have ht_eq : t = x + (t - x) := (add_sub_cancel x t).symm
      have hle : t ^ (α - 2) ≤ max 1 (2 ^ (α - 2)) * x ^ (α - 2) := by
        rw [ht_eq]
        exact Real.add_rpow_le_max_two_rpow_mul (α - 2) (by linarith [ht.1]) (by linarith [ht.2])
      calc |α * (α - 1)| * t ^ (α - 2)
          ≤ |α * (α - 1)| * (max 1 (2 ^ (α - 2)) * x ^ (α - 2)) :=
            mul_le_mul_of_nonneg_left hle (abs_nonneg _)
        _ = M := by simp only [M]; ring)
  have hpoly : taylorWithinEval (fun s : ℝ ↦ s ^ α) 1 univ x (x + h) =
      x ^ α + α * h * x ^ (α - 1) := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
      iteratedDeriv_one, Real.deriv_rpow_const, Nat.factorial_zero, Nat.cast_one, zero_add,
      pow_one, smul_eq_mul]
    ring
  have hlhs : ((x + h) ^ α - x ^ α) - α * h * x ^ (α - 1) =
      (x + h) ^ α - taylorWithinEval (fun s : ℝ ↦ s ^ α) 1 univ x (x + h) := by
    rw [hpoly]
    ring
  have hrhs : M * |(x + h) - x| ^ (1 + 1) / (Nat.factorial (1 + 1) : ℝ) =
      2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * x ^ (α - 2) * h ^ 2 := by
    rw [add_sub_cancel_left, abs_of_nonneg hh₀, Nat.factorial_two, Nat.cast_ofNat]
    simp only [M]
    ring
  rwa [← hlhs, hrhs] at htaylor

/-- For every real `α` and `1 ≤ x`,
`|x ^ α - (x + 1) ^ α| ≤ max 1 (2 ^ (α - 1)) * |α| * x ^ (α - 1)`. -/
theorem abs_rpow_sub_add_one_rpow_le (α : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |x ^ α - (x + 1) ^ α| ≤ max 1 (2 ^ (α - 1)) * |α| * x ^ (α - 1) := by
  rw [abs_sub_comm]
  simpa only [mul_one] using abs_add_rpow_sub_rpow_le α zero_le_one hx

/-- **Unit-step second-order forward difference of a real power (DLMF 2.10.15, explicit form).**
For every real `α` and `1 ≤ x`,
`|(x ^ α - (x + 1) ^ α) + α * x ^ (α - 1)| ≤
  2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * x ^ (α - 2)`. -/
theorem abs_rpow_sub_add_one_rpow_add_mul_le (α : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |(x ^ α - (x + 1) ^ α) + α * x ^ (α - 1)| ≤
      2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * x ^ (α - 2) := by
  have h := abs_add_rpow_sub_rpow_sub_mul_le α zero_le_one hx
  have heq : (x ^ α - (x + 1) ^ α) + α * x ^ (α - 1) =
      -(((x + 1) ^ α - x ^ α) - α * 1 * x ^ (α - 1)) := by ring
  rw [heq, abs_neg]
  simpa only [one_pow, mul_one] using h

/-- For every real `α`, `x ^ α - (x + 1) ^ α = O(α * x ^ (α - 1))` as `x → ∞`. -/
theorem isBigO_rpow_sub_add_one_rpow_atTop (α : ℝ) :
    (fun x : ℝ ↦ x ^ α - (x + 1) ^ α) =O[atTop] fun x : ℝ ↦ α * x ^ (α - 1) := by
  refine .of_bound (max 1 (2 ^ (α - 1))) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx₀ _),
    ← mul_assoc]
  exact abs_rpow_sub_add_one_rpow_le α hx

/-- Uniformly on `[1, ∞)`, `(x ^ α - (x + 1) ^ α) + α * x ^ (α - 1) = O(α * (α - 1) * x ^ (α - 2))`
for every real `α`. -/
theorem isBigO_rpow_sub_add_one_rpow_add_mul_principal_Ici (α : ℝ) :
    (fun x : ℝ ↦ (x ^ α - (x + 1) ^ α) + α * x ^ (α - 1)) =O[𝓟 (Ici 1)]
      fun x : ℝ ↦ α * (α - 1) * x ^ (α - 2) := by
  refine .of_bound (2⁻¹ * max 1 (2 ^ (α - 2))) ?_
  rw [eventually_principal]
  intro x hx
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx₀ _),
    ← mul_assoc]
  exact abs_rpow_sub_add_one_rpow_add_mul_le α hx

/-- For every real `α`, `(x ^ α - (x + 1) ^ α) + α * x ^ (α - 1) = O(α * (α - 1) * x ^ (α - 2))`
as `x → ∞`. -/
theorem isBigO_rpow_sub_add_one_rpow_add_mul_atTop (α : ℝ) :
    (fun x : ℝ ↦ (x ^ α - (x + 1) ^ α) + α * x ^ (α - 1)) =O[atTop]
      fun x : ℝ ↦ α * (α - 1) * x ^ (α - 2) :=
  (isBigO_rpow_sub_add_one_rpow_add_mul_principal_Ici α).mono
    (le_principal_iff.mpr (eventually_ge_atTop 1))

/-- **Second-order forward difference of natural powers (DLMF 2.10.15).** For every real `α`,
`(j ^ α - (j + 1) ^ α) + α * j ^ (α - 1) = O(α * (α - 1) * j ^ (α - 2))` as `j → ∞` in `ℕ`. -/
theorem isBigO_natCast_rpow_sub_add_one_rpow_add_mul_atTop (α : ℝ) :
    (fun j : ℕ ↦ ((j : ℝ) ^ α - (j + 1 : ℝ) ^ α) + α * (j : ℝ) ^ (α - 1)) =O[atTop]
      fun j : ℕ ↦ α * (α - 1) * (j : ℝ) ^ (α - 2) :=
  (isBigO_rpow_sub_add_one_rpow_add_mul_atTop α).comp_tendsto tendsto_natCast_atTop_atTop

end Real
