/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.AbsoluteValue.FiniteOrder
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Rigidity of complex absolute values restricting to the standard real absolute value

An absolute value `v : AbsoluteValue ℂ ℝ` that agrees with `|·|` on `ℝ` is the standard complex
norm `‖·‖` (`AbsoluteValue.eq_norm_of_apply_ofReal`). Since `Complex.I` has order `4`, every
absolute value on `ℂ` sends `Complex.I` to `1` (`AbsoluteValue.map_I`), so decomposing `z` into its
real and imaginary parts bounds `v z` above by `2 * ‖z‖`. Applying this bound to `z ^ n` and letting
`n → ∞` forces `v z ≤ ‖z‖`, and applying the resulting inequality to `z⁻¹` gives `‖z‖ ≤ v z`.

This closes the metric gap in the real Gelfand–Mazur theorem: any `ℝ`-algebra isomorphism between a
normed field over `ℝ` and `ℂ` pulls the norm back to an absolute value on `ℂ` restricting to `|·|`
on `ℝ`, and is therefore an isometry. Without the normalization on `ℝ`, positive real powers
`z ↦ ‖z‖ ^ t` with `0 < t < 1` give distinct archimedean absolute values on `ℂ`, as witnessed at the
end of the file for `t = 1 / 2`.

## Main results

* `AbsoluteValue.map_I`: every absolute value on `ℂ` takes the value `1` at `Complex.I`.
* `AbsoluteValue.eq_norm_of_apply_ofReal` and `AbsoluteValue.eq_toAbsoluteValue_of_apply_ofReal`:
  an absolute value on `ℂ` agreeing with `|·|` on `ℝ` is `‖·‖`.
* `AbsoluteValue.eq_norm_of_liesOver`, `AbsoluteValue.eq_toAbsoluteValue_of_liesOver`, and
  `AbsoluteValue.liesOver_abs_iff`: the corresponding characterization in terms of
  `AbsoluteValue.LiesOver`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2.
-/

public section

namespace AbsoluteValue

/-- Every absolute value on `ℂ` takes the value `1` at `Complex.I`, since `Complex.I ^ 4 = 1`. -/
@[simp]
theorem map_I {S : Type*} [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
    (v : AbsoluteValue ℂ S) : v Complex.I = 1 :=
  v.map_eq_one_of_isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.mpr ⟨4, four_pos, Complex.I_pow_four⟩

private theorem apply_le_two_mul_norm {v : AbsoluteValue ℂ ℝ}
    (h : ∀ r : ℝ, v r = |r|) (z : ℂ) : v z ≤ 2 * ‖z‖ := by
  calc
    v z = v ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by rw [Complex.re_add_im]
    _ ≤ v z.re + v ((z.im : ℂ) * Complex.I) := v.add_le _ _
    _ = |z.re| + |z.im| := by rw [v.map_mul, map_I, mul_one, h, h]
    _ ≤ ‖z‖ + ‖z‖ := add_le_add (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
    _ = 2 * ‖z‖ := (two_mul ‖z‖).symm

private theorem apply_le_norm_of_apply_ofReal {v : AbsoluteValue ℂ ℝ}
    (h : ∀ r : ℝ, v r = |r|) (z : ℂ) : v z ≤ ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  by_contra! hlt
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : 1 < v z / ‖z‖ := (one_lt_div hnorm_pos).mpr hlt
  have hbdd (n : ℕ) : (v z / ‖z‖) ^ n ≤ 2 := by
    rw [div_pow, ← v.map_pow, div_le_iff₀ (pow_pos hnorm_pos n), ← norm_pow]
    exact apply_le_two_mul_norm h (z ^ n)
  obtain ⟨n, hn⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop (2 : ℝ)).exists
  exact (hbdd n).not_gt hn

/-- An absolute value on `ℂ` that agrees with `|·|` on `ℝ` is the standard complex norm `‖·‖`. -/
theorem eq_norm_of_apply_ofReal {v : AbsoluteValue ℂ ℝ} (h : ∀ r : ℝ, v r = |r|) (z : ℂ) :
    v z = ‖z‖ := by
  refine le_antisymm (apply_le_norm_of_apply_ofReal h z) ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hinv : (v z)⁻¹ ≤ ‖z‖⁻¹ := by
    simpa only [map_inv₀, norm_inv] using apply_le_norm_of_apply_ofReal h z⁻¹
  exact (inv_le_inv₀ (v.pos hz) (norm_pos_iff.mpr hz)).mp hinv

/-- An absolute value on `ℂ` that agrees with `|·|` on `ℝ` equals
`NormedField.toAbsoluteValue ℂ`. -/
theorem eq_toAbsoluteValue_of_apply_ofReal {v : AbsoluteValue ℂ ℝ} (h : ∀ r : ℝ, v r = |r|) :
    v = NormedField.toAbsoluteValue ℂ :=
  ext <| eq_norm_of_apply_ofReal h

/-- An absolute value on `ℂ` lying over `AbsoluteValue.abs` on `ℝ` agrees with `‖·‖`. -/
theorem eq_norm_of_liesOver (v : AbsoluteValue ℂ ℝ) [v.LiesOver AbsoluteValue.abs] (z : ℂ) :
    v z = ‖z‖ :=
  eq_norm_of_apply_ofReal (fun r ↦ LiesOver.apply_algebraMap AbsoluteValue.abs r) z

/-- An absolute value on `ℂ` lying over `AbsoluteValue.abs` on `ℝ` equals
`NormedField.toAbsoluteValue ℂ`. -/
theorem eq_toAbsoluteValue_of_liesOver (v : AbsoluteValue ℂ ℝ) [v.LiesOver AbsoluteValue.abs] :
    v = NormedField.toAbsoluteValue ℂ :=
  ext <| eq_norm_of_liesOver v

instance : (NormedField.toAbsoluteValue ℂ).LiesOver AbsoluteValue.abs :=
  ⟨ext fun r ↦ Complex.norm_real r |>.trans (Real.norm_eq_abs r)⟩

/-- An absolute value on `ℂ` lies over `AbsoluteValue.abs` on `ℝ` if and only if it is
`NormedField.toAbsoluteValue ℂ`. -/
theorem liesOver_abs_iff {v : AbsoluteValue ℂ ℝ} :
    v.LiesOver AbsoluteValue.abs ↔ v = NormedField.toAbsoluteValue ℂ :=
  ⟨fun _ ↦ eq_toAbsoluteValue_of_liesOver v, fun h ↦ h ▸ inferInstance⟩

end AbsoluteValue

/- Without the normalization on `ℝ`, `z ↦ √‖z‖` is an absolute value on `ℂ` distinct from `‖·‖`. -/
example : ∃ v : AbsoluteValue ℂ ℝ, v ≠ NormedField.toAbsoluteValue ℂ := by
  have hsqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  refine ⟨{
    toFun z := √‖z‖
    map_mul' x y := by rw [norm_mul, Real.sqrt_mul (norm_nonneg x)]
    nonneg' x := Real.sqrt_nonneg _
    eq_zero' x := by rw [Real.sqrt_eq_zero (norm_nonneg x), norm_eq_zero]
    add_le' x y := (Real.sqrt_le_sqrt (norm_add_le x y)).trans
      (hsqrt ‖x‖ ‖y‖ (norm_nonneg x) (norm_nonneg y)) }, fun h ↦ ?_⟩
  have h4 := congrArg (fun v : AbsoluteValue ℂ ℝ ↦ v 4) h
  have hsq : √(4 : ℝ) ^ 2 = 4 := Real.sq_sqrt (by positivity)
  norm_num at h4
  nlinarith
