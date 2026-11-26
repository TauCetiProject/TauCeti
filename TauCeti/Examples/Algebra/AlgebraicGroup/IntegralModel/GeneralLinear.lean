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

For a ring `O` with `O → K` injective and a non-unit `ϖ ∈ O` (for example a uniformizer of a
discrete valuation ring), the `K`-point of `GL₁` with matrix `(ϖ)` has an integral entry but is not
an integral point of the standard model `GL_{1,O}`, because its inverse is not integral; the
criterion `TauCeti.IntegralModel.SmoothModel.mem_integralPoints_generalLinear_iff` needs both the
matrix and its inverse to be integral. For `ℤ ⊂ ℚ` and `ϖ = 2` the inverse is `1/2`.
-/

public section

namespace TauCeti.Examples

universe u

open CategoryTheory IntegralModel

/-- **An integral entry does not make an integral point**: over a ring `O` with `O → K`
injective, the `K`-point of `GL₁` with matrix `(ϖ)` for a non-unit `ϖ ∈ O` (for example a
uniformizer of a discrete valuation ring) has an integral entry but is not an integral point of
`GL_{1,O}`, because its inverse is not integral. -/
theorem notMem_integralPoints_generalLinear_one {O K : Type u} [CommRing O] [CommRing K]
    [Algebra O K] (hinj : Function.Injective (algebraMap O K)) {ϖ : O} (hϖ : ¬IsUnit ϖ)
    (g : GL (Fin 1) K) (hg : (g : Matrix (Fin 1) (Fin 1) K) = !![algebraMap O K ϖ]) :
    WithConv.toConv ((GeneralLinear.generalLinearToPoint (R := K) 1 g).ofConv.comp
      (eqToHom (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj K 1)).hom.toAlgHom) ∉
      (SmoothModel.generalLinear O K 1).integralPoints := by
  rw [SmoothModel.mem_integralPoints_generalLinear_iff]
  rintro ⟨M, hM⟩
  have hcomp : ((GeneralLinear.generalLinearToPoint (R := K) 1 g).ofConv.comp
      (eqToHom (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj K 1)).hom.toAlgHom).comp
      (eqToHom (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj K 1).symm).hom.toAlgHom =
      (GeneralLinear.generalLinearToPoint (R := K) 1 g).ofConv := by
    ext x
    simp [← BialgHom.comp_apply, ← _root_.CommHopfAlgCat.hom_comp]
  rw [hcomp, WithConv.toConv_ofConv, GeneralLinear.pointToGeneralLinear_generalLinearToPoint]
    at hM
  have h00 : algebraMap O K ((M : Matrix (Fin 1) (Fin 1) O) 0 0) = algebraMap O K ϖ := by
    simpa [hg] using congrArg (fun A : GL (Fin 1) K ↦ (A : Matrix (Fin 1) (Fin 1) K) 0 0) hM
  apply hϖ
  rw [← hinj h00, ← Matrix.det_fin_one (M : Matrix (Fin 1) (Fin 1) O)]
  exact Matrix.isUnits_det_units M

/-- The `ℚ`-point of `GL₁` with matrix `(2)` has an integral entry but is not an integral point
of `GL_{1,ℤ}`: its inverse `1/2` is not integral. -/
example (two : GL (Fin 1) ℚ) (htwo : (two : Matrix (Fin 1) (Fin 1) ℚ) = !![2]) :
    WithConv.toConv ((GeneralLinear.generalLinearToPoint (R := ℚ) 1 two).ofConv.comp
      (eqToHom (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj ℚ 1)).hom.toAlgHom) ∉
      (SmoothModel.generalLinear ℤ ℚ 1).integralPoints :=
  notMem_integralPoints_generalLinear_one (ϖ := 2) (RingHom.injective_int (algebraMap ℤ ℚ))
    (by decide) two (by rw [htwo, map_ofNat])

end TauCeti.Examples
