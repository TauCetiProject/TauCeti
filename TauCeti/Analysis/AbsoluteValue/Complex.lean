/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import TauCeti.Analysis.AbsoluteValue.FiniteOrder

/-!
# Rigidity of real-valued absolute values on `ℂ`

An absolute value on `ℂ` whose restriction to `ℝ` is `|·| ^ t` (with `t > 0`) equals `‖·‖ ^ t` on
all of `ℂ` (`AbsoluteValue.eq_norm_rpow_of_apply_ofReal`). In particular, an absolute value on `ℂ`
agreeing with `|·|` on `ℝ` is the complex norm (`AbsoluteValue.eq_norm_of_apply_ofReal`), so at
most one absolute value on `ℂ` restricts to `|·|` on `ℝ` (`AbsoluteValue.ext_of_apply_ofReal`).

Because `Complex.I` has multiplicative order `4`, every absolute value on `ℂ` takes the value `1`
at `Complex.I` (`AbsoluteValue.map_I`). Writing `w = w.re + w.im * I` then bounds `v w` by
`2 * ‖w‖ ^ t`; applying this bound to all powers `w ^ n` eliminates the factor `2` and yields
`v w ≤ ‖w‖ ^ t`. Finally, `z * conj z = ‖z‖ ^ 2` lies in `ℝ`, so
`v z * v (conj z) = (‖z‖ ^ t) ^ 2`, forcing `v z = ‖z‖ ^ t`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2.
-/

public section

namespace AbsoluteValue

/-- Every absolute value on `ℂ` takes the value `1` at `Complex.I`, since `I ^ 4 = 1`. -/
@[simp]
theorem map_I {S : Type*} [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
    (v : AbsoluteValue ℂ S) : v Complex.I = 1 :=
  v.map_eq_one_of_isOfFinOrder
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by positivity, Complex.I_pow_four⟩)

/-- An absolute value on `ℂ` whose restriction to `ℝ` is `|·| ^ t` (for `t > 0`) equals `‖·‖ ^ t`
everywhere on `ℂ`. -/
theorem eq_norm_rpow_of_apply_ofReal (v : AbsoluteValue ℂ ℝ) {t : ℝ} (ht : 0 < t)
    (hv : ∀ r : ℝ, v r = |r| ^ t) (z : ℂ) : v z = ‖z‖ ^ t := by
  have hle2 (w : ℂ) : v w ≤ 2 * ‖w‖ ^ t := by
    calc v w = v ((w.re : ℂ) + (w.im : ℂ) * Complex.I) := by nth_rw 1 [← Complex.re_add_im w]
      _ ≤ v w.re + v ((w.im : ℂ) * Complex.I) := v.add_le _ _
      _ = |w.re| ^ t + |w.im| ^ t := by rw [map_mul, v.map_I, mul_one, hv, hv]
      _ ≤ ‖w‖ ^ t + ‖w‖ ^ t := add_le_add
          (Real.rpow_le_rpow (abs_nonneg _) (Complex.abs_re_le_norm w) ht.le)
          (Real.rpow_le_rpow (abs_nonneg _) (Complex.abs_im_le_norm w) ht.le)
      _ = 2 * ‖w‖ ^ t := (two_mul _).symm
  -- Applying the coarse bound to `w ^ n` removes the factor `2`.
  have hle (w : ℂ) : v w ≤ ‖w‖ ^ t := by
    rcases eq_or_ne w 0 with rfl | hw
    · simp [Real.zero_rpow ht.ne']
    have hpos : 0 < ‖w‖ ^ t := Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) t
    rw [← div_le_one hpos]
    by_contra! hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 hgt
    have hpow : (v w / ‖w‖ ^ t) ^ n ≤ 2 := by
      rw [div_pow, ← map_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
        mul_comm t, Real.rpow_mul (norm_nonneg _), Real.rpow_natCast, ← norm_pow]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (pow_ne_zero n hw)) t)).mpr
        (hle2 (w ^ n))
    exact not_le_of_gt hn hpow
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow ht.ne']
  have hpos : 0 < ‖z‖ ^ t := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) t
  refine le_antisymm (hle z) (le_of_mul_le_mul_right ?_ hpos)
  have hconj : v (starRingEnd ℂ z) ≤ ‖z‖ ^ t := by
    simpa only [Complex.norm_conj] using hle (starRingEnd ℂ z)
  calc ‖z‖ ^ t * ‖z‖ ^ t = |(‖z‖ ^ 2 : ℝ)| ^ t := by
        rw [abs_of_nonneg (sq_nonneg _), sq, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    _ = v (z * starRingEnd ℂ z) := by
        rw [← hv, Complex.ofReal_pow, Complex.mul_conj']
    _ = v z * v (starRingEnd ℂ z) := map_mul v _ _
    _ ≤ v z * ‖z‖ ^ t := mul_le_mul_of_nonneg_left hconj (v.nonneg z)

/-- An absolute value on `ℂ` agreeing with `|·|` on `ℝ` is the complex norm `‖·‖`. -/
theorem eq_norm_of_apply_ofReal (v : AbsoluteValue ℂ ℝ) (hv : ∀ r : ℝ, v r = |r|) (z : ℂ) :
    v z = ‖z‖ := by
  simpa only [Real.rpow_one] using
    v.eq_norm_rpow_of_apply_ofReal one_pos (fun r ↦ by rw [hv, Real.rpow_one]) z

/-- Two absolute values on `ℂ` agreeing with `|·|` on `ℝ` are equal. -/
theorem ext_of_apply_ofReal {v w : AbsoluteValue ℂ ℝ}
    (hv : ∀ r : ℝ, v r = |r|) (hw : ∀ r : ℝ, w r = |r|) : v = w := by
  ext z
  rw [v.eq_norm_of_apply_ofReal hv, w.eq_norm_of_apply_ofReal hw]

end AbsoluteValue

/-! For `t > 1` no absolute value on `ℂ` can restrict to `|·| ^ t` on `ℝ`, since the triangle
inequality fails already at `1 + 1`. -/

example : ¬ ∃ v : AbsoluteValue ℂ ℝ, ∀ r : ℝ, v r = |r| ^ (2 : ℝ) := by
  rintro ⟨v, hv⟩
  have h := v.add_le (1 : ℝ) (1 : ℝ)
  rw [← Complex.ofReal_add, hv, hv] at h
  norm_num [Real.rpow_two] at h
