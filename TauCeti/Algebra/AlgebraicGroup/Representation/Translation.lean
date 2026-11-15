/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul

/-!
# Right translation of matrix coefficients

For a commutative Hopf algebra `H` over a commutative ring `R`, pullback along right translation by
a rational point `g : WithConv (H →ₐ[R] R)` transforms the matrix coefficient of a vector in a right
`H`-comodule by acting on that vector via `TauCeti.Comodule.basePointsRepresentation`. No
reducedness, finite-type, or field assumptions are needed.

## Main declarations

* `TauCeti.Comodule.rightTranslationAlgHom_matrixCoefficient`: right-translating a matrix
  coefficient as an algebra endomorphism acts on the vector via `basePointsRepresentation`.
* `TauCeti.Comodule.rightTranslationAlgEquiv_matrixCoefficient`: right-translating a matrix
  coefficient as an algebra automorphism acts on the vector via `basePointsRepresentation`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 2.g and 4.b.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 3.1 and 6.7.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

universe u v w

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Right translation as an algebra endomorphism acts on a matrix coefficient through the
base-point representation on the vector. -/
@[simp]
theorem rightTranslationAlgHom_matrixCoefficient (g : WithConv (H →ₐ[R] R))
    (φ : Module.Dual R M) (m : M) :
    HopfAlgebra.rightTranslationAlgHom g (matrixCoefficient (C := H) φ m) =
      matrixCoefficient (C := H) φ (basePointsRepresentation M g m) := by
  rw [HopfAlgebra.rightTranslationAlgHom_apply, comul_matrixCoefficient,
    basePointsRepresentation_apply, endOfPoint_tmul, one_smul]
  induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
  | tmul v a => simp
  | add x y hx hy => simp [hx, hy]

/-- Right translation of a matrix coefficient acts on its vector by the base-point
representation. -/
@[simp]
theorem rightTranslationAlgEquiv_matrixCoefficient (g : WithConv (H →ₐ[R] R))
    (φ : Module.Dual R M) (m : M) :
    HopfAlgebra.rightTranslationAlgEquiv g (matrixCoefficient (C := H) φ m) =
      matrixCoefficient (C := H) φ (basePointsRepresentation M g m) := by
  rw [← AlgEquiv.toAlgHom_apply, HopfAlgebra.rightTranslationAlgEquiv_toAlgHom,
    rightTranslationAlgHom_matrixCoefficient]

end TauCeti.Comodule
