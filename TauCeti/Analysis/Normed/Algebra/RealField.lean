/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur

import Mathlib.Analysis.Normed.Field.WithAbs
import TauCeti.Analysis.AbsoluteValue.Complex

/-!
# Isometric embeddings of real normed fields

By the real Gelfand–Mazur theorem (`NormedAlgebra.Real.nonempty_algEquiv_or`), every field `F` that
is a normed `ℝ`-algebra is isomorphic as an `ℝ`-algebra either to `ℝ` or to `ℂ`. Combining this
with the rigidity of absolute values on `ℂ` restricting to `|·|` on `ℝ`
(`AbsoluteValue.eq_norm_of_apply_ofReal`) shows that every `ℝ`-algebra equivalence `F ≃ₐ[ℝ] ℝ` or
`F ≃ₐ[ℝ] ℂ` preserves the norm (`AlgEquiv.norm_apply_of_real`,
`AlgEquiv.norm_apply_of_complex`), and hence is an isometry.

Consequently every normed field `F` over `ℝ` admits a norm-preserving `ℝ`-algebra homomorphism
`F →ₐ[ℝ] ℂ` (`NormedAlgebra.Real.exists_algHom_complex_norm_eq`). More generally, any normed field
equipped with a norm-preserving ring homomorphism `ℝ →+* E` admits a norm-preserving ring
homomorphism `E →+* ℂ` compatible with `ℝ →+* ℂ`
(`NormedAlgebra.Real.exists_ringHom_complex_norm_eq`). Applied to the completion of a field at an
absolute value lying over an infinite place, this produces a complex embedding realizing that
absolute value.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2 (Theorem 1.2.4, Ostrowski's theorem).
-/

public section

namespace AlgEquiv

variable {F : Type*} [NormedField F] [NormedAlgebra ℝ F]

/-- Every `ℝ`-algebra equivalence from a normed field `ℝ`-algebra `F` to `ℝ` sends `x` to a real
number of absolute value `‖x‖`. -/
@[simp]
theorem abs_apply_of_real (e : F ≃ₐ[ℝ] ℝ) (x : F) : |e x| = ‖x‖ := by
  rw [← Real.norm_eq_abs]
  have hx : algebraMap ℝ F (e x) = x := by
    rw [← e.symm.commutes (e x), Algebra.algebraMap_self_apply, e.symm_apply_apply]
  nth_rw 2 [← hx]
  rw [norm_algebraMap']

/-- Every `ℝ`-algebra equivalence from a normed field `ℝ`-algebra `F` to `ℝ` preserves the norm. -/
theorem norm_apply_of_real (e : F ≃ₐ[ℝ] ℝ) (x : F) : ‖e x‖ = ‖x‖ :=
  (Real.norm_eq_abs _).trans (e.abs_apply_of_real x)

/-- Every `ℝ`-algebra equivalence from a normed field `ℝ`-algebra `F` to `ℝ` is an isometry. -/
theorem isometry_of_real (e : F ≃ₐ[ℝ] ℝ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_apply_of_real

/-- Every `ℝ`-algebra equivalence from a normed field `ℝ`-algebra `F` to `ℂ` preserves the norm:
pulling the norm of `F` back along `e.symm` gives an absolute value on `ℂ` restricting to `|·|` on
`ℝ`, which must equal the complex norm. -/
@[simp]
theorem norm_apply_of_complex (e : F ≃ₐ[ℝ] ℂ) (x : F) : ‖e x‖ = ‖x‖ := by
  have h := ((IsAbsoluteValue.toAbsoluteValue (norm : F → ℝ)).comp
    (f := e.symm.toRingHom) e.symm.injective).eq_norm_of_apply_ofReal
    (fun r ↦ by
      simp only [AbsoluteValue.comp_apply, IsAbsoluteValue.toAbsoluteValue_apply,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv, RingHom.coe_coe]
      have hr : (r : ℂ) = algebraMap ℝ ℂ r := rfl
      rw [hr, e.symm.commutes, norm_algebraMap', Real.norm_eq_abs]) (e x)
  simpa using h.symm

/-- Every `ℝ`-algebra equivalence from a normed field `ℝ`-algebra `F` to `ℂ` is an isometry. -/
theorem isometry_of_complex (e : F ≃ₐ[ℝ] ℂ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_apply_of_complex

end AlgEquiv

namespace NormedAlgebra.Real

/-- Every normed field `ℝ`-algebra admits a norm-preserving `ℝ`-algebra homomorphism into `ℂ`. -/
theorem exists_algHom_complex_norm_eq (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    ∃ φ : F →ₐ[ℝ] ℂ, ∀ x : F, ‖φ x‖ = ‖x‖ := by
  rcases nonempty_algEquiv_or F with h | h
  · obtain ⟨e⟩ := h
    refine ⟨(Algebra.ofId ℝ ℂ).comp e.toAlgHom, fun x ↦ ?_⟩
    rw [AlgHom.comp_apply, Algebra.ofId_apply, norm_algebraMap', AlgEquiv.coe_toAlgHom,
      e.norm_apply_of_real]
  · obtain ⟨e⟩ := h
    refine ⟨e.toAlgHom, fun x ↦ ?_⟩
    simpa only [AlgEquiv.coe_toAlgHom] using e.norm_apply_of_complex x

/-- Any normed field `E` equipped with a norm-preserving ring homomorphism `ι : ℝ →+* E` admits a
norm-preserving ring homomorphism `φ : E →+* ℂ` extending `Complex.ofRealHom` along `ι`. -/
theorem exists_ringHom_complex_norm_eq {E : Type*} [NormedField E] (ι : ℝ →+* E)
    (hι : ∀ r : ℝ, ‖ι r‖ = |r|) :
    ∃ φ : E →+* ℂ, φ.comp ι = Complex.ofRealHom ∧ ∀ x : E, ‖φ x‖ = ‖x‖ := by
  let hnorm : @NormedAlgebra ℝ E _ _ :=
    { toAlgebra := ι.toAlgebra
      norm_smul_le r x := by
        let := ι.toAlgebra
        rw [Algebra.smul_def, norm_mul, RingHom.algebraMap_toAlgebra, hι, Real.norm_eq_abs] }
  obtain ⟨⟨φ, hcomm⟩, hφ⟩ := @exists_algHom_complex_norm_eq E _ hnorm
  refine ⟨φ, RingHom.ext fun r ↦ ?_, hφ⟩
  simpa [RingHom.algebraMap_toAlgebra] using hcomm r

end NormedAlgebra.Real
