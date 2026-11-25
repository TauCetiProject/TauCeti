/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.GeneralLinear

/-!
# Checks for the standard integral model of `GL_n`

For `ℤ ⊂ ℚ`, the `ℚ`-point of `GL₁` with matrix `(2)` has an integral entry but is not an integral
point of the standard model `GL_{1,ℤ}`, because its inverse `1/2` is not integral; the criterion
`TauCeti.IntegralModel.SmoothModel.mem_integralPoints_generalLinear_iff` needs both the matrix and
its inverse to be integral.
-/

public section

namespace TauCeti.Examples

open CategoryTheory IntegralModel

/-- The `ℚ`-point of `GL₁` with matrix `(2)` has an integral entry but is not an integral point
of `GL_{1,ℤ}`: its inverse `1/2` is not integral. -/
example (two : GL (Fin 1) ℚ) (htwo : (two : Matrix (Fin 1) (Fin 1) ℚ) = !![2]) :
    WithConv.toConv ((GeneralLinear.generalLinearToPoint (R := ℚ) 1 two).ofConv.comp
      (eqToHom (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj ℚ 1)).hom.toAlgHom) ∉
      (SmoothModel.generalLinear ℤ ℚ 1).integralPoints := by
  rw [SmoothModel.mem_integralPoints_generalLinear_iff]
  rintro ⟨M, hM⟩
  have hcomp : ((GeneralLinear.generalLinearToPoint (R := ℚ) 1 two).ofConv.comp
      (eqToHom (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj ℚ 1)).hom.toAlgHom).comp
      (eqToHom (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj ℚ 1).symm).hom.toAlgHom =
      (GeneralLinear.generalLinearToPoint (R := ℚ) 1 two).ofConv := by
    ext x
    simp [← BialgHom.comp_apply, ← _root_.CommHopfAlgCat.hom_comp]
  rw [hcomp, WithConv.toConv_ofConv, GeneralLinear.pointToGeneralLinear_generalLinearToPoint]
    at hM
  have h00 : ((M : Matrix (Fin 1) (Fin 1) ℤ) 0 0 : ℚ) = 2 := by
    simpa [htwo] using congrArg (fun A : GL (Fin 1) ℚ ↦ (A : Matrix (Fin 1) (Fin 1) ℚ) 0 0) hM
  have hinv : (M : Matrix (Fin 1) (Fin 1) ℤ) * (M⁻¹ : GL (Fin 1) ℤ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 := congrFun (congrFun hinv 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq] at h1
  have h2 : (M : Matrix (Fin 1) (Fin 1) ℤ) 0 0 = 2 := by exact_mod_cast h00
  rw [h2] at h1
  omega
end TauCeti.Examples
