/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.CounitPoints
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic

/-!
# The adjoint action of the special linear group

The tangent Lie algebra of `SLₙ` is the Lie algebra of trace-zero matrices. Its adjoint
action is conjugation by the corresponding determinant-one matrix over every commutative
coefficient algebra, including nonreduced ones. This comparison supports the calculation
of adjoint weights for `SLₙ`.

## Main declarations

* `TauCeti.SpecialLinear.tangentMatrix_adDerivation_coe`: identifies the adjoint action
  on `Lie(SLₙ)` with conjugation by its image in `GLₙ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.d (the adjoint representation), cf. 10.24.
-/

public section

namespace TauCeti.SpecialLinear

open WithConv

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
variable (n : ℕ)

/-- The adjoint action of `SLₙ` on its tangent Lie algebra is conjugation on trace-zero
matrices by the ambient `GLₙ` point. This holds for every commutative coefficient algebra. -/
@[simp]
theorem tangentMatrix_adDerivation_coe
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R]
      Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B))
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    (tangentMatrix n (Derivation.adDerivation B g d) : Matrix (Fin n) (Fin n) B) =
      (counitPointsMulEquiv n g : Matrix (Fin n) (Fin n) B) *
      (tangentMatrix n d : Matrix (Fin n) (Fin n) B) *
      ((counitPointsMulEquiv n g)⁻¹ : Matrix.SpecialLinearGroup (Fin n) B) := by
  rw [tangentMatrix_apply_coe, HopfIdeal.quotientLieHom_adDerivation,
    GeneralLinear.tangentMatrix_adDerivation, ← tangentMatrix_apply_coe n d]
  have hgl := (toGL_counitPointsMulEquiv n g).symm
  simp only [coordinateMap, CommHopfAlgCat.hom_mkQuotient] at hgl
  rw [hgl]
  rw [← map_inv Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

end TauCeti.SpecialLinear
