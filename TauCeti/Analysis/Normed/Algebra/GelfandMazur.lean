/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur

import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import TauCeti.Analysis.AbsoluteValue.Archimedean

/-!
# An isometric Gelfand–Mazur theorem over `ℝ`

A normed field `E` that is a normed `ℝ`-algebra embeds into `ℂ` by an `ℝ`-algebra homomorphism
that preserves the norm (`NormedAlgebra.Real.exists_algHom_complex_isometry`). This is the
step that identifies an absolute value with an archimedean place: an absolute value whose
completion contains a copy of `ℝ` is the norm of a complex embedding.

Gelfand–Mazur (`NormedAlgebra.Real.nonempty_algEquiv_or`) gives `E ≃ₐ[ℝ] ℝ` or `E ≃ₐ[ℝ] ℂ` as
algebras, but says nothing about the norm. In the first case the norm is forced, since every
element of `E` is the image of a real number. In the second case it is forced by the uniqueness
of the absolute value of `ℂ` extending `|·|` (`AbsoluteValue.eq_norm_of_apply_ofReal`).

## Main results

* `NormedAlgebra.Real.exists_algHom_complex_isometry`: a normed field that is a normed
  `ℝ`-algebra embeds isometrically into `ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.2 (Ostrowski's theorem) and Proposition 1.3.1.
-/

public section

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
