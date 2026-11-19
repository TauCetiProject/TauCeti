/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur

import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Normed fields over `ℝ` and the absolute values of `ℂ`

A normed field `E` that is a normed `ℝ`-algebra embeds into `ℂ` by an `ℝ`-algebra homomorphism
that preserves the norm (`NormedAlgebra.Real.exists_algHom_complex_isometry`). This is the
step that identifies an absolute value with an archimedean place: an absolute value whose
completion contains a copy of `ℝ` is the norm of a complex embedding.

Gelfand–Mazur (`NormedAlgebra.Real.nonempty_algEquiv_or`) gives `E ≃ₐ[ℝ] ℝ` or `E ≃ₐ[ℝ] ℂ` as
algebras, but says nothing about the norm. In the first case the norm is forced, since every
element of `E` is the image of a real number. In the second case it is forced by the uniqueness
of the absolute value of `ℂ` extending `|·|` (`AbsoluteValue.eq_norm_of_apply_ofReal`): such an
absolute value `f` satisfies `f (a + b i) ≤ |a| + |b| ≤ 2 ‖a + b i‖`, the power trick applied to
`f (z ^ n) ≤ 2 ‖z‖ ^ n` removes the factor `2`, and the reverse inequality is the same bound for
`z⁻¹`.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value of `ℂ` that restricts to `|·|` on
  `ℝ` is the norm.
* `NormedAlgebra.Real.exists_algHom_complex_isometry`: a normed field that is a normed
  `ℝ`-algebra embeds isometrically into `ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.2 (Ostrowski's theorem) and Proposition 1.3.1.
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

namespace NormedAlgebra.Real

/-- A normed field that is a normed `ℝ`-algebra embeds into `ℂ` by an `ℝ`-algebra homomorphism
preserving the norm. This strengthens the Gelfand–Mazur theorem
`NormedAlgebra.Real.nonempty_algEquiv_or`, which identifies the field with `ℝ` or `ℂ` as an
algebra only. -/
theorem exists_algHom_complex_isometry (E : Type*) [NormedField E] [NormedAlgebra ℝ E] :
    ∃ ψ : E →ₐ[ℝ] ℂ, Isometry ψ := by
  rcases nonempty_algEquiv_or E with h | h
  · obtain ⟨φ⟩ := h
    refine ⟨(Algebra.ofId ℝ ℂ).comp φ.toAlgHom, (AddMonoidHomClass.isometry_iff_norm _).mpr
      fun x ↦ ?_⟩
    have hx : algebraMap ℝ E (φ x) = x := by simpa using (φ.symm.commutes (φ x)).symm
    -- `‖(φ x : ℂ)‖ = |φ x| = ‖algebraMap ℝ E (φ x)‖ = ‖x‖`
    conv_rhs => rw [← hx]
    simp [norm_algebraMap']
  · obtain ⟨φ⟩ := h
    refine ⟨φ.toAlgHom, (AddMonoidHomClass.isometry_iff_norm _).mpr fun x ↦ ?_⟩
    let f : AbsoluteValue ℂ ℝ :=
      (NormedField.toAbsoluteValue E).comp (f := (φ.symm : ℂ →+* E)) φ.symm.injective
    have hfz (z : ℂ) : f z = ‖φ.symm z‖ := rfl
    have hf : ⇑f = norm := AbsoluteValue.eq_norm_of_apply_ofReal f fun r ↦ by
      rw [hfz, ← Complex.coe_algebraMap, AlgEquiv.commutes, norm_algebraMap', Real.norm_eq_abs]
    simpa [hfz] using (congrFun hf (φ x)).symm

end NormedAlgebra.Real
