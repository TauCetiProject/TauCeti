/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Coordinates for orthogonal groups of quadratic forms

This file relates the intrinsic orthogonal group of a quadratic form to its matrix
model in a chosen basis.  If `D` is the Gram matrix of `Q` and `A` is the matrix
of a linear automorphism, preservation of `Q` is exactly `Aᵀ * D * A = D`.
The determinant-one version gives the corresponding coordinate description of the
special orthogonal group.

In standard coordinates on `n → R`, the file also characterizes the matrix ranges of
`QuadraticMap.orthogonalToGeneralLinear` and `QuadraticMap.specialOrthogonalToGeneralLinear` inside
`GL(n, R)` by quadratic preservation, polar Gram-matrix preservation, and determinant one.
-/

open scoped Matrix
open Module

public section

namespace TauCeti.QuadraticMap

universe u v

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type v} [AddCommGroup V] [Module R V]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In a basis, an automorphism preserves a quadratic form exactly when its matrix
satisfies the usual Gram-matrix congruence equation. -/
theorem mem_orthogonalGroup_iff_toMatrix (Q : QuadraticForm R V) (b : Basis n R V)
    (g : V ≃ₗ[R] V) :
    g ∈ orthogonalGroup Q ↔
      (LinearMap.toMatrix b b g.toLinearMap)ᵀ * (QuadraticForm.toMatrix b Q) *
          LinearMap.toMatrix b b g.toLinearMap = QuadraticForm.toMatrix b Q := by
  have hinj : Function.Injective (fun Q' : QuadraticForm R V => Q'.toMatrix b) :=
    (LinearMap.toMatrix₂ b b).injective.comp (QuadraticMap.associated_rightInverse R).injective
  rw [mem_orthogonalGroup_iff]
  rw [show (∀ m, Q (g m) = Q m) ↔ Q.comp g.toLinearMap = Q by
    simp only [QuadraticMap.ext_iff, QuadraticMap.comp_apply, LinearEquiv.coe_coe]]
  rw [hinj.eq_iff.symm, QuadraticForm.toMatrix_comp b b Q g.toLinearMap]

/-- In a basis, a linear automorphism belongs to the special orthogonal group
exactly when its Gram-matrix congruence and determinant equations both hold. -/
theorem mem_specialOrthogonalGroup_iff_toMatrix (Q : QuadraticForm R V) (b : Basis n R V)
    (g : V ≃ₗ[R] V) :
    g ∈ specialOrthogonalGroup Q ↔
      (LinearMap.toMatrix b b g.toLinearMap)ᵀ * (QuadraticForm.toMatrix b Q) *
          LinearMap.toMatrix b b g.toLinearMap = QuadraticForm.toMatrix b Q ∧
        Matrix.det (LinearMap.toMatrix b b g.toLinearMap) = 1 := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff_toMatrix Q b g]
  simp [Units.ext_iff]

end TauCeti.QuadraticMap

namespace QuadraticMap

section Range

universe u v w

open TauCeti (matrixGeneralLinearEquiv matrixGeneralLinearEquiv_apply)
open TauCeti.QuadraticMap (orthogonalGroup mem_orthogonalGroup_iff mem_orthogonalGroup_iff_polar
  mem_specialOrthogonalGroup_iff det_coe_specialOrthogonalGroup)

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- A general-linear matrix lies in the coordinate range of `O(Q)` if and only if its
matrix-vector action preserves `Q`. -/
theorem mem_range_orthogonalToGeneralLinear_iff
    {R : Type u} [CommSemiring R] {N : Type w} [AddCommMonoid N] [Module R N]
    (Q : QuadraticMap R (n → R) N) (U : Matrix.GeneralLinearGroup n R) :
    U ∈ MonoidHom.range Q.orthogonalToGeneralLinear ↔
      ∀ x : n → R, Q ((U : Matrix n n R) *ᵥ x) = Q x := by
  constructor
  · rintro ⟨g, rfl⟩ x
    rw [coe_orthogonalToGeneralLinear, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    exact (mem_orthogonalGroup_iff.mp g.prop) x
  · intro hU
    refine ⟨⟨LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R)
        (matrixGeneralLinearEquiv U),
      mem_orthogonalGroup_iff.mpr fun x ↦ by
        rw [matrixGeneralLinearEquiv_apply, hU x]⟩, ?_⟩
    apply Units.ext
    ext i j
    rw [orthogonalToGeneralLinear_apply, Subtype.coe_mk, matrixGeneralLinearEquiv_apply,
      Matrix.mulVec_single_one, Matrix.col_apply]

/-- A general-linear matrix lies in the coordinate range of `SO(Q)` if and only if its
matrix-vector action preserves `Q` and its determinant is one. -/
theorem mem_range_specialOrthogonalToGeneralLinear_iff
    {R : Type u} [CommRing R] {N : Type w} [AddCommMonoid N] [Module R N]
    (Q : QuadraticMap R (n → R) N) (U : Matrix.GeneralLinearGroup n R) :
    U ∈ MonoidHom.range Q.specialOrthogonalToGeneralLinear ↔
      (∀ x : n → R, Q ((U : Matrix n n R) *ᵥ x) = Q x) ∧ (U : Matrix n n R).det = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun x ↦ ?_, ?_⟩
    · rw [specialOrthogonalToGeneralLinear_mulVec]
      exact (mem_orthogonalGroup_iff.mp (mem_specialOrthogonalGroup_iff.mp g.prop).1) x
    · rw [coe_specialOrthogonalToGeneralLinear, LinearMap.det_toMatrix',
        ← LinearEquiv.coe_det, det_coe_specialOrthogonalGroup, Units.val_one]
  · rintro ⟨hQ, hdet⟩
    obtain ⟨g, hg⟩ := (mem_range_orthogonalToGeneralLinear_iff Q U).mpr hQ
    have hgdet : LinearEquiv.det (g : (n → R) ≃ₗ[R] (n → R)) = 1 := by
      apply Units.ext
      rw [Units.val_one, LinearEquiv.coe_det, ← LinearMap.det_toMatrix',
        ← coe_orthogonalToGeneralLinear, hg, hdet]
    refine ⟨⟨(g : (n → R) ≃ₗ[R] (n → R)),
      mem_specialOrthogonalGroup_iff.mpr ⟨g.prop, hgdet⟩⟩, ?_⟩
    apply Units.ext
    ext i j
    rw [specialOrthogonalToGeneralLinear_apply, Subtype.coe_mk,
      ← orthogonalToGeneralLinear_apply, hg]

/-- When multiplication by `2` is injective on `R`, a general-linear matrix lies in the coordinate
range of `SO(Q)` if and only if it preserves the polar Gram matrix in standard coordinates and has
determinant one. -/
theorem mem_range_specialOrthogonalToGeneralLinear_iff_polarBilin
    {R : Type u} [CommRing R]
    (Q : QuadraticForm R (n → R)) (h2 : IsSMulRegular R (2 : R))
    (U : Matrix.GeneralLinearGroup n R) :
    U ∈ MonoidHom.range Q.specialOrthogonalToGeneralLinear ↔
      (U : Matrix n n R)ᵀ * LinearMap.BilinForm.toMatrix' Q.polarBilin * (U : Matrix n n R) =
          LinearMap.BilinForm.toMatrix' Q.polarBilin ∧
        (U : Matrix n n R).det = 1 := by
  rw [mem_range_specialOrthogonalToGeneralLinear_iff]
  refine and_congr_left fun _ ↦ ?_
  have hQ : (∀ x : n → R, Q ((U : Matrix n n R) *ᵥ x) = Q x) ↔
      LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R)
        (matrixGeneralLinearEquiv U) ∈ orthogonalGroup Q := by
    simp only [mem_orthogonalGroup_iff, matrixGeneralLinearEquiv_apply]
  rw [hQ, mem_orthogonalGroup_iff_polar h2]
  have hcomp :
      (U : Matrix n n R)ᵀ * LinearMap.BilinForm.toMatrix' Q.polarBilin * (U : Matrix n n R) =
        LinearMap.BilinForm.toMatrix'
          (LinearMap.BilinForm.comp Q.polarBilin (Matrix.toLin' (U : Matrix n n R))
            (Matrix.toLin' (U : Matrix n n R))) := by
    simpa only [Matrix.transpose_transpose] using
      LinearMap.BilinForm.mul_toMatrix'_mul Q.polarBilin (U : Matrix n n R)ᵀ (U : Matrix n n R)
  rw [hcomp, LinearMap.BilinForm.toMatrix'.injective.eq_iff, LinearMap.BilinForm.ext_iff]
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, matrixGeneralLinearEquiv_apply,
    polarBilin_apply_apply]

end Range

end QuadraticMap
