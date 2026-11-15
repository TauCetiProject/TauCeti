/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur

import TauCeti.Analysis.AbsoluteValue.Complex

/-!
# Isometric form of the real Gelfand–Mazur theorem

Mathlib's `NormedAlgebra.Real.nonempty_algEquiv_or` shows that any normed field `F` which is a
normed `ℝ`-algebra is isomorphic as an `ℝ`-algebra either to `ℝ` or to `ℂ`. Because the norm on
`ℂ` is the unique absolute value restricting to `|·|` on `ℝ`
(`AbsoluteValue.eq_norm_of_apply_ofReal`), every such `ℝ`-algebra isomorphism is automatically an
isometry. Consequently every normed field over `ℝ` admits an isometric `ℝ`-algebra embedding into
`ℂ`, and more generally any normed field receiving a norm-nonincreasing ring homomorphism from `ℝ`
embeds isometrically into `ℂ`.

## Main results

* `AlgEquiv.norm_apply_of_real` and `AlgEquiv.isometry_of_real`: an `ℝ`-algebra isomorphism
  `F ≃ₐ[ℝ] ℝ` on a normed field over `ℝ` preserves norms and is an isometry.
* `AlgEquiv.norm_apply_of_complex` and `AlgEquiv.isometry_of_complex`: an `ℝ`-algebra isomorphism
  `F ≃ₐ[ℝ] ℂ` on a normed field over `ℝ` preserves norms and is an isometry.
* `NormedAlgebra.Real.exists_algHom_complex_norm_eq`: every normed field over `ℝ` admits an
  isometric `ℝ`-algebra homomorphism into `ℂ`.
* `NormedAlgebra.Real.exists_ringHom_complex_norm_eq_of_ringHom`: any normed field receiving a
  norm-nonincreasing ring homomorphism `ℝ →+* F` admits an isometric ring homomorphism into `ℂ`
  compatible with `ℝ →+* ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Theorem 1.2.4.
-/

public section

namespace AlgEquiv

variable {F : Type*} [NormedField F] [NormedAlgebra ℝ F]

/-- Every `ℝ`-algebra isomorphism from a normed field over `ℝ` to `ℝ` preserves the norm. -/
theorem norm_apply_of_real (e : F ≃ₐ[ℝ] ℝ) (x : F) : ‖e x‖ = ‖x‖ := by
  have hx : e.symm (e x) = e x • (1 : F) := by
    rw [Algebra.smul_def, mul_one]
    simpa using e.symm.commutes (e x)
  calc
    ‖e x‖ = ‖e x‖ * ‖(1 : F)‖ := by rw [norm_one, mul_one]
    _ = ‖e x • (1 : F)‖ := (norm_smul (e x) (1 : F)).symm
    _ = ‖x‖ := by rw [← hx, e.symm_apply_apply]

/-- Every `ℝ`-algebra isomorphism from a normed field over `ℝ` to `ℝ` sends each element to a real
number whose absolute value is its norm. -/
@[simp]
theorem abs_apply_of_real (e : F ≃ₐ[ℝ] ℝ) (x : F) : |e x| = ‖x‖ := by
  rw [← Real.norm_eq_abs, e.norm_apply_of_real]

/-- Every `ℝ`-algebra isomorphism from a normed field over `ℝ` to `ℝ` is an isometry. -/
theorem isometry_of_real (e : F ≃ₐ[ℝ] ℝ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_apply_of_real

/-- Every `ℝ`-algebra isomorphism from a normed field over `ℝ` to `ℂ` preserves the norm. -/
@[simp]
theorem norm_apply_of_complex (e : F ≃ₐ[ℝ] ℂ) (x : F) : ‖e x‖ = ‖x‖ := by
  let v : AbsoluteValue ℂ ℝ :=
    (NormedField.toAbsoluteValue F).comp (f := e.symm.toRingHom) e.symm.injective
  have hv (r : ℝ) : v r = |r| := by
    have hr : e.symm (r : ℂ) = r • (1 : F) := by
      rw [Algebra.smul_def, mul_one]
      exact e.symm.commutes r
    calc
      v r = ‖e.symm (r : ℂ)‖ := rfl
      _ = ‖r • (1 : F)‖ := by rw [hr]
      _ = |r| := by rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one]
  calc
    ‖e x‖ = v (e x) := (AbsoluteValue.eq_norm_of_apply_ofReal hv (e x)).symm
    _ = ‖e.symm (e x)‖ := rfl
    _ = ‖x‖ := by rw [e.symm_apply_apply]

/-- Every `ℝ`-algebra isomorphism from a normed field over `ℝ` to `ℂ` is an isometry. -/
theorem isometry_of_complex (e : F ≃ₐ[ℝ] ℂ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_apply_of_complex

end AlgEquiv

namespace NormedAlgebra.Real

/-- **Isometric Gelfand–Mazur theorem over `ℝ`.** Every normed field `F` that is a normed
`ℝ`-algebra admits an isometric `ℝ`-algebra homomorphism `F →ₐ[ℝ] ℂ`. -/
theorem exists_algHom_complex_norm_eq (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    ∃ φ : F →ₐ[ℝ] ℂ, ∀ x : F, ‖φ x‖ = ‖x‖ := by
  cases nonempty_algEquiv_or F with
  | inl h =>
    obtain ⟨e⟩ := h
    exact ⟨(Algebra.ofId ℝ ℂ).comp e.toAlgHom, fun x ↦ by simp⟩
  | inr h =>
    obtain ⟨e⟩ := h
    exact ⟨e.toAlgHom, e.norm_apply_of_complex⟩

/-- Any normed field `F` equipped with a norm-nonincreasing ring homomorphism `f : ℝ →+* F` admits
an isometric ring homomorphism `φ : F →+* ℂ` extending `f`. -/
theorem exists_ringHom_complex_norm_eq_of_ringHom {F : Type*} [NormedField F]
    (f : ℝ →+* F) (hf : ∀ r : ℝ, ‖f r‖ ≤ ‖r‖) :
    ∃ φ : F →+* ℂ, (∀ r : ℝ, φ (f r) = r) ∧ ∀ x : F, ‖φ x‖ = ‖x‖ := by
  let : Algebra ℝ F := f.toAlgebra
  have hsmul (r : ℝ) (x : F) : ‖r • x‖ ≤ ‖r‖ * ‖x‖ := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, norm_mul]
    exact mul_le_mul_of_nonneg_right (hf r) (norm_nonneg x)
  let : NormedAlgebra ℝ F := { f.toAlgebra with norm_smul_le := hsmul }
  obtain ⟨φ, hφ⟩ := exists_algHom_complex_norm_eq F
  exact ⟨φ.toRingHom, fun r ↦ φ.commutes r, hφ⟩

end NormedAlgebra.Real
