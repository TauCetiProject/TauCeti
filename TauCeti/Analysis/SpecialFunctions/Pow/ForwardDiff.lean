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

* `TauCeti.abs_add_rpow_sub_rpow_le`: explicit first-order increment bound for `0 ≤ h ≤ x`.
* `TauCeti.abs_add_rpow_sub_rpow_sub_mul_le`: explicit second-order Taylor remainder bound with the
  sharp constant `1 / 2` for `0 ≤ h ≤ x`.
* `TauCeti.abs_rpow_sub_add_one_rpow_le` and `TauCeti.abs_rpow_sub_add_one_rpow_add_mul_le`:
  unit-step specializations for `1 ≤ x`.
* `TauCeti.isBigO_rpow_sub_add_one_rpow_atTop`: `x ^ α - (x + 1) ^ α = O(α * x ^ (α - 1))`.
* `TauCeti.isBigO_rpow_sub_add_one_rpow_add_mul_principal_Ici`,
  `TauCeti.isBigO_rpow_sub_add_one_rpow_add_mul_atTop`, and
  `TauCeti.isBigO_natCast_rpow_sub_add_one_rpow_add_mul_atTop`: uniform and asymptotic forms of
  `(x ^ α - (x + 1) ^ α) + α * x ^ (α - 1) = O(α * (α - 1) * x ^ (α - 2))`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(ii), formula 2.10.15.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
-/

public section

open Asymptotics Filter Set

namespace TauCeti

/-- On `[x, 2 * x]` with `0 < x`, a real power `y ^ β` of either sign is bounded above by
`max 1 (2 ^ β) * x ^ β`. -/
private theorem add_rpow_le_max_two_rpow_mul (β : ℝ) {x t : ℝ} (hx : 0 < x) (ht₀ : 0 ≤ t)
    (htx : t ≤ x) :
    (x + t) ^ β ≤ max 1 (2 ^ β) * x ^ β := by
  have hxt : 0 < x + t := by linarith
  rcases le_total 0 β with hβ | hβ
  · calc (x + t) ^ β ≤ (2 * x) ^ β := Real.rpow_le_rpow hxt.le (by linarith) hβ
      _ = 2 ^ β * x ^ β := Real.mul_rpow zero_le_two hx.le
      _ ≤ max 1 (2 ^ β) * x ^ β :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx.le β)
  · calc (x + t) ^ β ≤ x ^ β := Real.rpow_le_rpow_of_nonpos hx (by linarith) hβ
      _ = 1 * x ^ β := (one_mul _).symm
      _ ≤ max 1 (2 ^ β) * x ^ β :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le β)

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
    have hle := add_rpow_le_max_two_rpow_mul (α - 1) hx ht.1 (ht.2.trans hhx)
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
  let g : ℝ → ℝ := fun t ↦ (x + t) ^ α - α * x ^ (α - 1) * t
  have hgderiv : ∀ t ∈ Icc 0 h,
      HasDerivAt g (α * ((x + t) ^ (α - 1) - x ^ (α - 1))) t := by
    intro t ht
    have hxt : 0 < x + t := add_pos_of_pos_of_nonneg hx ht.1
    have hd₁ : HasDerivAt (fun s : ℝ ↦ (x + s) ^ α) (α * (x + t) ^ (α - 1) * 1) t :=
      (Real.hasDerivAt_rpow_const (x := x + t) (p := α) (Or.inl hxt.ne')).comp t
        ((hasDerivAt_id t).const_add x)
    have hd₂ : HasDerivAt (fun s : ℝ ↦ α * x ^ (α - 1) * s) (α * x ^ (α - 1) * 1) t :=
      (hasDerivAt_id t).const_mul (α * x ^ (α - 1))
    exact (hd₁.sub hd₂).congr_deriv (by ring)
  have hgbound : ∀ t ∈ Icc 0 h, |α * ((x + t) ^ (α - 1) - x ^ (α - 1))| ≤ M * t := by
    intro t ht
    have hstep := abs_add_rpow_sub_rpow_le (α - 1) ht.1 (ht.2.trans hhx)
    have hexp : α - 1 - 1 = α - 2 := by ring
    rw [hexp] at hstep
    calc |α * ((x + t) ^ (α - 1) - x ^ (α - 1))|
        = |α| * |(x + t) ^ (α - 1) - x ^ (α - 1)| := abs_mul _ _
      _ ≤ |α| * (max 1 (2 ^ (α - 2)) * |α - 1| * x ^ (α - 2) * t) :=
          mul_le_mul_of_nonneg_left hstep (abs_nonneg α)
      _ = M * t := by simp only [M, abs_mul]; ring
  have hsign (σ : ℝ) (hσ : |σ| = 1) : σ * (g h - g 0) ≤ 2⁻¹ * M * h ^ 2 := by
    have hq : ∀ t, HasDerivAt (fun s : ℝ ↦ 2⁻¹ * M * (s * s)) (M * t) t := fun t ↦
      (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (2⁻¹ * M)).congr_deriv
        (by simp only [id_eq]; ring)
    have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 h)
      (f := fun s ↦ σ * g s - 2⁻¹ * M * (s * s))
      (f' := fun t ↦ σ * (α * ((x + t) ^ (α - 1) - x ^ (α - 1))) - M * t)
      (fun t ht ↦ (((hgderiv t ht).const_mul σ).sub (hq t)).continuousAt.continuousWithinAt)
      (fun t ht ↦ (((hgderiv t (interior_subset ht)).const_mul σ).sub (hq t)).hasDerivWithinAt)
      (fun t ht ↦ by
        have hle := le_abs_self (σ * (α * ((x + t) ^ (α - 1) - x ^ (α - 1))))
        rw [abs_mul, hσ, one_mul] at hle
        linarith [hgbound t (interior_subset ht)])
      (left_mem_Icc.mpr hh₀) (right_mem_Icc.mpr hh₀) hh₀
    nlinarith [sq h]
  have hdiff : ((x + h) ^ α - x ^ α) - α * h * x ^ (α - 1) = g h - g 0 := by
    simp only [g, add_zero, mul_zero, sub_zero]
    ring
  rw [hdiff, abs_le]
  exact ⟨by linarith [hsign (-1) (by norm_num)], by linarith [hsign 1 (by norm_num)]⟩

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

end TauCeti
