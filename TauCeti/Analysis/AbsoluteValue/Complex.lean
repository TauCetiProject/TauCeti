/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur


/-!
# Absolute values of `ℂ` and the isometric Gelfand–Mazur theorem

An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the usual absolute
value, `AbsoluteValue.eq_norm_of_apply_ofReal`. No continuity is assumed: the bound
`N z ≤ |Re z| + |Im z| N i ≤ 2 ‖z‖`, applied to the powers of `z` and of `z⁻¹`, forces `N z = ‖z‖`.

This is what turns the Gelfand–Mazur theorem over `ℝ`, Mathlib's
`NormedAlgebra.Real.nonempty_algEquiv_or`, into a statement about norms: a normed field that is a
normed `ℝ`-algebra embeds into `ℂ` by an isometric `ℝ`-algebra homomorphism,
`NormedAlgebra.Real.exists_algHom_complex_isometry`. Gelfand–Mazur alone gives an `ℝ`-algebra
isomorphism with `ℝ` or `ℂ`, which says nothing about the norm; that the norm is then the usual
one is the lemma above. This is what identifies an absolute value of a field whose completion
contains `ℝ` isometrically with the absolute value of an infinite place, with no finiteness
hypothesis on the field.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value of `ℂ` that is `|·|` on `ℝ` is the
  complex norm.
* `NormedAlgebra.Real.exists_algHom_complex_isometry`: a normed field that is a normed
  `ℝ`-algebra has an isometric `ℝ`-algebra embedding into `ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2.

The argument through the bound `N z ≤ 2 ‖z‖` follows Ralf Stephan's `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file `DiophantineApproximation/PlacesOverInfinite.lean`
(Apache 2.0).
-/

public section

namespace AbsoluteValue

/-- An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the complex
norm. -/
theorem eq_norm_of_apply_ofReal {N : AbsoluteValue ℂ ℝ} (h : ∀ r : ℝ, N r = |r|) (z : ℂ) :
    N z = ‖z‖ := by
  have hI : N Complex.I = 1 := by
    have hI2 : N Complex.I ^ 2 = 1 := by
      rw [← map_pow, Complex.I_sq, ← Complex.ofReal_one, ← Complex.ofReal_neg, h, abs_neg,
        abs_one]
    nlinarith [N.nonneg Complex.I]
  -- A uniform bound, with constant `2`, against the complex norm.
  have hbound (y : ℂ) : N y ≤ 2 * ‖y‖ := by
    calc N y = N (y.re + y.im * Complex.I) := by rw [Complex.re_add_im]
      _ ≤ |y.re| + |y.im| := by
        simpa [hI, h] using N.add_le (y.re : ℂ) (y.im * Complex.I)
      _ ≤ 2 * ‖y‖ := by linarith [Complex.abs_re_le_norm y, Complex.abs_im_le_norm y]
  -- Applied to the powers of `y`, the bound loses its constant.
  have hle (y : ℂ) : N y ≤ ‖y‖ := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [← div_le_one hy']
    by_contra! hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 hlt
    have : (N y / ‖y‖) ^ n ≤ 2 := by
      rw [div_pow, div_le_iff₀ (pow_pos hy' n)]
      simpa using hbound (y ^ n)
    linarith
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  refine le_antisymm (hle z) ?_
  have := hle z⁻¹
  rwa [map_inv₀, norm_inv, inv_le_inv₀ (N.pos hz) (norm_pos_iff.mpr hz)] at this

end AbsoluteValue

namespace NormedAlgebra.Real

/-- **Gelfand–Mazur, isometric form.** A normed field that is a normed `ℝ`-algebra embeds into `ℂ`
by an `ℝ`-algebra homomorphism preserving the norm. -/
theorem exists_algHom_complex_isometry (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    ∃ ψ : F →ₐ[ℝ] ℂ, Isometry ψ := by
  rcases nonempty_algEquiv_or F with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine ⟨(Algebra.ofId ℝ ℂ).comp e.toAlgHom, AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_⟩
    obtain ⟨r, rfl⟩ := e.symm.surjective x
    have : e.symm r = algebraMap ℝ F r := e.symm.commutes r
    simp [this, norm_algebraMap']
  · -- The norm of `F`, carried to `ℂ` along `e`, is `|·|` on `ℝ`, hence the complex norm.
    let N : AbsoluteValue ℂ ℝ :=
      (IsAbsoluteValue.toAbsoluteValue (norm : F → ℝ)).comp
        (f := e.symm.toRingEquiv.toRingHom) e.symm.injective
    have hN (r : ℝ) : N r = |r| := by
      simp [N, ← Complex.coe_algebraMap]
    refine ⟨e.toAlgHom, AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_⟩
    rw [← AbsoluteValue.eq_norm_of_apply_ofReal hN]
    simp [N]

end NormedAlgebra.Real
