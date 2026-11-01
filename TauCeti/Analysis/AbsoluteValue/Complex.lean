/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Absolute values on `ℂ` extending the absolute value of `ℝ`

The usual absolute value of `ℂ` is the only absolute value on `ℂ` which restricts to the usual
absolute value on `ℝ`, `AbsoluteValue.eq_norm_of_apply_ofReal`. This supplies the uniqueness
needed to make the real Gelfand–Mazur theorem isometric, as developed in
`TauCeti.Analysis.Normed.Algebra.GelfandMazur`, and hence to identify absolute values lying over
archimedean places with the absolute values of complex embeddings.

The statement `AbsoluteValue.eq_norm_of_apply_ofReal`, and its use to make Gelfand–Mazur
isometric, also appear in Ralf Stephan's `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file `DiophantineApproximation/PlacesOverInfinite.lean`
(Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

namespace AbsoluteValue

/-- An absolute value on `ℂ` which agrees with the usual absolute value on `ℝ` is the usual
absolute value of `ℂ`. -/
theorem eq_norm_of_apply_ofReal {f : AbsoluteValue ℂ ℝ} (h : ∀ r : ℝ, f r = |r|) (z : ℂ) :
    f z = ‖z‖ := by
  have hI : f Complex.I = 1 := by
    have : f Complex.I ^ 2 = 1 := by
      rw [← map_pow, Complex.I_sq, map_neg_eq_map, map_one]
    exact (pow_eq_one_iff_of_nonneg (f.nonneg _) two_ne_zero).mp this
  -- A first, crude comparison with the usual absolute value.
  have hle_two (z : ℂ) : f z ≤ 2 * ‖z‖ := by
    calc f z = f (z.re + z.im * Complex.I) := by rw [Complex.re_add_im]
      _ ≤ f z.re + f (z.im * Complex.I) := f.add_le _ _
      _ = |z.re| + |z.im| := by rw [map_mul, hI, mul_one, h, h]
      _ ≤ 2 * ‖z‖ := by linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]
  -- Applied to the powers of `z / ‖z‖`, the crude comparison loses its constant.
  have hle (z : ℂ) : f z ≤ ‖z‖ := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    have hz' : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hu : f (z / ‖z‖) = f z / ‖z‖ := by rw [map_div₀, h, abs_norm]
    have hnu : ‖z / ‖z‖‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hz'.ne']
    by_contra! hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 ((one_lt_div hz').mpr hlt)
    have := hle_two ((z / ‖z‖) ^ n)
    rw [map_pow, hu, norm_pow, hnu, one_pow, mul_one] at this
    exact hn.not_ge this
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  refine (hle z).antisymm ?_
  have := hle z⁻¹
  rw [map_inv₀, norm_inv] at this
  exact (inv_le_inv₀ (f.pos hz) (norm_pos_iff.mpr hz)).mp this

end AbsoluteValue
