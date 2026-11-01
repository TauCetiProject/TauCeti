/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import TauCeti.Analysis.AbsoluteValue.Complex

/-!
# Isometric real Gelfand–Mazur theorem

Every normed field which is a normed `ℝ`-algebra embeds isometrically into `ℂ`,
`NormedAlgebra.Real.exists_algHom_complex_isometry`. This upgrades Mathlib's algebraic
Gelfand–Mazur theorem `NormedAlgebra.Real.nonempty_algEquiv_or` using the uniqueness of the
absolute value on `ℂ` extending that of `ℝ`, `AbsoluteValue.eq_norm_of_apply_ofReal`.
It identifies a field completion containing `ℝ` isometrically with a subfield of `ℂ`, as needed
to classify absolute values over an archimedean place.

The same isometric refinement appears in Ralf Stephan's `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file `DiophantineApproximation/PlacesOverInfinite.lean`
(Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

namespace NormedAlgebra.Real

/-- **Gelfand–Mazur theorem**, isometric form: a normed field which is a normed `ℝ`-algebra
embeds isometrically into `ℂ` as an `ℝ`-algebra. -/
theorem exists_algHom_complex_isometry (E : Type*) [NormedField E] [NormedAlgebra ℝ E] :
    ∃ ψ : E →ₐ[ℝ] ℂ, Isometry ψ := by
  rcases nonempty_algEquiv_or E with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine ⟨(Algebra.ofId ℝ ℂ).comp e.toAlgHom, AddMonoidHomClass.isometry_of_norm _ fun y ↦ ?_⟩
    have hy : algebraMap ℝ E (e y) = y := by
      rw [← e.symm.commutes, Algebra.algebraMap_self_apply, AlgEquiv.symm_apply_apply]
    calc ‖(Algebra.ofId ℝ ℂ).comp e.toAlgHom y‖ = ‖e y‖ := by simp
      _ = ‖algebraMap ℝ E (e y)‖ := (norm_algebraMap' E _).symm
      _ = ‖y‖ := by rw [hy]
  · -- The norm of `E`, read on `ℂ` through `e`, is an absolute value extending that of `ℝ`.
    let f : AbsoluteValue ℂ ℝ :=
      { toFun z := ‖e.symm z‖
        map_mul' _ _ := by simp
        nonneg' _ := norm_nonneg _
        eq_zero' _ := by simp
        add_le' _ _ := by simpa using norm_add_le _ _ }
    have hf_apply (z : ℂ) : f z = ‖e.symm z‖ := rfl
    have hf (r : ℝ) : f r = |r| := by
      rw [hf_apply, ← Complex.coe_algebraMap, e.symm.commutes, norm_algebraMap',
        Real.norm_eq_abs]
    refine ⟨e.toAlgHom, AddMonoidHomClass.isometry_of_norm _ fun y ↦ ?_⟩
    have := AbsoluteValue.eq_norm_of_apply_ofReal hf (e y)
    rw [hf_apply, AlgEquiv.symm_apply_apply] at this
    simpa using this.symm

end NormedAlgebra.Real
