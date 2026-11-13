/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import TauCeti.Analysis.AbsoluteValue.Complex

/-!
# Normed fields over `ℝ` embed isometrically into `ℂ`

Mathlib's Gelfand–Mazur theorem `NormedAlgebra.Real.nonempty_algEquiv_or` says that a normed field
which is a normed `ℝ`-algebra is isomorphic to `ℝ` or to `ℂ` as an `ℝ`-algebra. This file upgrades
the isomorphism to an isometry: the norm is then the absolute value of `ℝ` or the norm of `ℂ`.
In the real case this is the compatibility of the norm with `algebraMap ℝ`; in the complex case it
is `AbsoluteValue.eq_norm_of_apply_ofReal`, applied to the norm transported to `ℂ`. Neither
completeness nor finite dimension is assumed.

This is the step that identifies an absolute value of a field lying over an archimedean place with
an embedding into `ℂ`, applied to the completion at that absolute value.

## Main results

* `NormedAlgebra.Real.exists_algHom_complex_norm_eq`: a normed field which is a normed `ℝ`-algebra
  has a norm-preserving `ℝ`-algebra homomorphism into `ℂ`.

## References

* A. Ostrowski, *Über einige Lösungen der Funktionalgleichung φ(x)⋅φ(y)=φ(xy)*, Acta Math. 41
  (1916).
-/

public section

namespace NormedAlgebra.Real

/-- **Ostrowski's theorem**, isometric form: a normed field which is a normed `ℝ`-algebra has a
norm-preserving `ℝ`-algebra homomorphism into `ℂ`. -/
theorem exists_algHom_complex_norm_eq (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    ∃ φ : F →ₐ[ℝ] ℂ, ∀ x, ‖φ x‖ = ‖x‖ := by
  rcases nonempty_algEquiv_or F with h | h
  · obtain ⟨e⟩ := h
    refine ⟨(Algebra.ofId ℝ ℂ).comp (e : F →ₐ[ℝ] ℝ), fun x ↦ ?_⟩
    have hx : algebraMap ℝ F (e x) = x := by
      rw [← e.symm.commutes, Algebra.algebraMap_self_apply, e.symm_apply_apply]
    rw [AlgHom.comp_apply, Algebra.ofId_apply, norm_algebraMap', AlgEquiv.coe_toAlgHom]
    conv_rhs => rw [← hx]
    rw [norm_algebraMap']
  · obtain ⟨e⟩ := h
    have hN (z : ℂ) : ‖e.symm z‖ = ‖z‖ := by
      refine ((NormedField.toAbsoluteValue F).comp (f := (e.symm : ℂ →+* F))
        (RingHom.injective _)).eq_norm_of_apply_ofReal (fun r ↦ ?_) z
      rw [AbsoluteValue.comp_apply, NormedField.toAbsoluteValue_apply, RingHom.coe_coe,
        ← Complex.coe_algebraMap, e.symm.commutes, norm_algebraMap', Real.norm_eq_abs]
    exact ⟨e, fun x ↦ by rw [← hN, AlgEquiv.coe_toAlgHom, e.symm_apply_apply]⟩

end NormedAlgebra.Real
