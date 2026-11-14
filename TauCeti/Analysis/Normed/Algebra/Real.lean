/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import TauCeti.Analysis.AbsoluteValue.Complex

/-!
# Isometric Gelfand–Mazur over `ℝ`

Mathlib's `NormedAlgebra.Real.nonempty_algEquiv_or` shows that any field `F` carrying a
`NormedField` and `NormedAlgebra ℝ F` structure is isomorphic as an `ℝ`-algebra either to `ℝ` or
to `ℂ`, requiring neither completeness nor finite dimensionality. Because the unique absolute
value on `ℂ` extending `|·|` on `ℝ` is the complex modulus
(`AbsoluteValue.eq_norm_of_apply_ofReal`), every `ℝ`-algebra homomorphism out of `ℂ` into a normed
division `ℝ`-algebra is automatically an isometry, and hence every `ℝ`-algebra equivalence
`F ≃ₐ[ℝ] ℝ` or `F ≃ₐ[ℝ] ℂ` preserves norms.

## Main results

* `AlgHom.norm_apply_of_real` and `AlgHom.isometry_of_real`: any `ℝ`-algebra homomorphism from `ℂ`
  into a normed division `ℝ`-algebra preserves norms.
* `AlgEquiv.norm_apply_real`, `AlgEquiv.abs_apply_real`, `AlgEquiv.isometry_real`, and
  `AlgEquiv.toLinearIsometryEquivReal`: any `ℝ`-algebra equivalence `F ≃ₐ[ℝ] ℝ` on a normed
  division `ℝ`-algebra is an isometry.
* `AlgEquiv.norm_apply_complex`, `AlgEquiv.isometry_complex` and
  `AlgEquiv.toLinearIsometryEquivComplex`: any `ℝ`-algebra equivalence `F ≃ₐ[ℝ] ℂ` on a normed
  division `ℝ`-algebra is an isometry.
* `NormedAlgebra.Real.nonempty_linearIsometryEquiv_or`: a normed field over `ℝ` is linearly
  isometric either to `ℝ` or to `ℂ`.
* `NormedAlgebra.Real.exists_ringHom_complex_norm_eq`: every normed field over `ℝ` admits a
  norm-preserving ring embedding into `ℂ` extending the canonical inclusion `ℝ → ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Theorem 1.2.4 (Ostrowski / Gelfand–Mazur).
* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, Theorem 4.2.
-/

public section
noncomputable section

namespace AlgHom

/-- Any `ℝ`-algebra homomorphism from `ℂ` into a normed division `ℝ`-algebra preserves norms. -/
@[simp]
theorem norm_apply_of_real {A : Type*} [NormedDivisionRing A] [NormedAlgebra ℝ A]
    (f : ℂ →ₐ[ℝ] A) (z : ℂ) : ‖f z‖ = ‖z‖ := by
  refine f.toRingHom.norm_apply_of_norm_ofReal (fun r ↦ ?_) z
  have hr : (r : ℂ) = algebraMap ℝ ℂ r := rfl
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hr, f.commutes, norm_algebraMap',
    Real.norm_eq_abs]

/-- Any `ℝ`-algebra homomorphism from `ℂ` into a normed division `ℝ`-algebra is an isometry. -/
theorem isometry_of_real {A : Type*} [NormedDivisionRing A] [NormedAlgebra ℝ A]
    (f : ℂ →ₐ[ℝ] A) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm f f.norm_apply_of_real

end AlgHom

namespace AlgEquiv

section Real

variable {F : Type*} [NormedDivisionRing F] [NormedAlgebra ℝ F]

/-- Any `ℝ`-algebra equivalence from a normed division `ℝ`-algebra to `ℝ` preserves norms. -/
theorem norm_apply_real (e : F ≃ₐ[ℝ] ℝ) (x : F) : ‖e x‖ = ‖x‖ := by
  have hx : algebraMap ℝ F (e x) = x := by
    rw [← e.symm.commutes (e x), Algebra.algebraMap_self_apply, e.symm_apply_apply]
  conv_rhs => rw [← hx, norm_algebraMap']

/-- The absolute value of `e x` under an `ℝ`-algebra equivalence `e : F ≃ₐ[ℝ] ℝ` on a normed
division `ℝ`-algebra equals `‖x‖`. -/
@[simp]
theorem abs_apply_real (e : F ≃ₐ[ℝ] ℝ) (x : F) : |e x| = ‖x‖ := by
  rw [← Real.norm_eq_abs, e.norm_apply_real]

/-- Any `ℝ`-algebra equivalence from a normed division `ℝ`-algebra to `ℝ` is an isometry. -/
theorem isometry_real (e : F ≃ₐ[ℝ] ℝ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_apply_real

/-- Upgrade an `ℝ`-algebra equivalence `F ≃ₐ[ℝ] ℝ` on a normed division `ℝ`-algebra to a linear
isometry equivalence. -/
def toLinearIsometryEquivReal (e : F ≃ₐ[ℝ] ℝ) : F ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := e.toLinearEquiv
  norm_map' := e.norm_apply_real

/-- Applying `e.toLinearIsometryEquivReal` agrees with `e`. -/
@[simp]
theorem toLinearIsometryEquivReal_apply (e : F ≃ₐ[ℝ] ℝ) (x : F) :
    e.toLinearIsometryEquivReal x = e x :=
  (rfl)

/-- Any `ℝ`-algebra equivalence from a normed division `ℝ`-algebra to `ℂ` preserves norms. -/
@[simp]
theorem norm_apply_complex (e : F ≃ₐ[ℝ] ℂ) (x : F) : ‖e x‖ = ‖x‖ := by
  have h := e.symm.toAlgHom.norm_apply_of_real (e x)
  simpa using h.symm

/-- Any `ℝ`-algebra equivalence from a normed division `ℝ`-algebra to `ℂ` is an isometry. -/
theorem isometry_complex (e : F ≃ₐ[ℝ] ℂ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_apply_complex

/-- Upgrade an `ℝ`-algebra equivalence `F ≃ₐ[ℝ] ℂ` on a normed division `ℝ`-algebra to a linear
isometry equivalence. -/
def toLinearIsometryEquivComplex (e : F ≃ₐ[ℝ] ℂ) : F ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := e.toLinearEquiv
  norm_map' := e.norm_apply_complex

/-- Applying `e.toLinearIsometryEquivComplex` agrees with `e`. -/
@[simp]
theorem toLinearIsometryEquivComplex_apply (e : F ≃ₐ[ℝ] ℂ) (x : F) :
    e.toLinearIsometryEquivComplex x = e x :=
  (rfl)

end Real

end AlgEquiv

namespace NormedAlgebra.Real

/-- **Isometric Gelfand–Mazur theorem over `ℝ`.** A normed field over `ℝ` is linearly isometric
either to `ℝ` or to `ℂ`. -/
theorem nonempty_linearIsometryEquiv_or (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    Nonempty (F ≃ₗᵢ[ℝ] ℝ) ∨ Nonempty (F ≃ₗᵢ[ℝ] ℂ) :=
  match nonempty_algEquiv_or F with
  | .inl ⟨e⟩ => .inl ⟨e.toLinearIsometryEquivReal⟩
  | .inr ⟨e⟩ => .inr ⟨e.toLinearIsometryEquivComplex⟩

/-- Every normed field over `ℝ` admits a norm-preserving ring embedding into `ℂ` sending real
scalars to themselves. -/
theorem exists_ringHom_complex_norm_eq (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    ∃ φ : F →+* ℂ, (∀ r : ℝ, φ (algebraMap ℝ F r) = r) ∧ ∀ x : F, ‖φ x‖ = ‖x‖ :=
  match nonempty_algEquiv_or F with
  | .inl ⟨e⟩ =>
    ⟨Complex.ofRealHom.comp e.toRingHom, fun r ↦ by simp [e.commutes r], fun _ ↦ by simp⟩
  | .inr ⟨e⟩ => ⟨e.toRingHom, e.commutes, e.norm_apply_complex⟩

end NormedAlgebra.Real
