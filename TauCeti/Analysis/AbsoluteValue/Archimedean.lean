/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The absolute values of `ℂ` extending `|·|`

An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the norm
(`AbsoluteValue.eq_norm_of_apply_ofReal`). Such an absolute value `f` satisfies
`f (a + b i) ≤ |a| + |b| ≤ 2 ‖a + b i‖`, the power trick applied to `f (z ^ n) ≤ 2 ‖z‖ ^ n`
removes the factor `2`, and the reverse inequality is the same bound for `z⁻¹`. This is the
uniqueness statement behind the isometric Gelfand–Mazur theorem
`NormedAlgebra.Real.exists_algHom_complex_isometry`.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value of `ℂ` that restricts to `|·|` on
  `ℝ` is the norm.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.2 (Ostrowski's theorem).
-/

public section

namespace AbsoluteValue

/-- An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the norm. -/
theorem eq_norm_of_apply_ofReal (f : AbsoluteValue ℂ ℝ) (h : ∀ r : ℝ, f r = |r|) :
    ⇑f = norm := by
  have hI : f Complex.I = 1 := by
    have hsq : f Complex.I ^ 2 = 1 := by
      rw [← map_pow, Complex.I_sq, ← Complex.ofReal_one, ← Complex.ofReal_neg, h]
      simp
    nlinarith [f.nonneg Complex.I]
  -- The crude bound `f z ≤ 2 ‖z‖` from the decomposition `z = re z + im z * I`.
  have hle (z : ℂ) : f z ≤ 2 * ‖z‖ := by
    calc f z = f (z.re + z.im * Complex.I) := by rw [Complex.re_add_im]
      _ ≤ f z.re + f (z.im * Complex.I) := f.add_le _ _
      _ = |z.re| + |z.im| := by rw [map_mul, hI, mul_one, h, h]
      _ ≤ 2 * ‖z‖ := by linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]
  -- The power trick removes the factor `2`.
  have hle' (z : ℂ) : f z ≤ ‖z‖ := by
    by_contra! hlt
    have hpos : 0 < f z := (norm_nonneg z).trans_lt hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2)
      ((div_lt_one hpos).mpr hlt)
    have hfn : f z ^ n ≤ 2 * ‖z‖ ^ n := by
      simpa only [map_pow, norm_pow] using hle (z ^ n)
    rw [div_pow, div_lt_iff₀ (pow_pos hpos n)] at hn
    linarith
  funext z
  refine le_antisymm (hle' z) ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hinv := hle' z⁻¹
  rw [map_inv₀, norm_inv] at hinv
  exact (inv_le_inv₀ (f.pos hz) (norm_pos_iff.mpr hz)).mp hinv

end AbsoluteValue
