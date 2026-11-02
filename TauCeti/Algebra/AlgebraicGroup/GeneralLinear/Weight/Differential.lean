/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent

/-!
# Differentials of represented weight-torus cocharacters

Suppose a weight representation factors through a commutative bialgebra `H`. A cocharacter
of its weight torus differentiates to the diagonal matrix of character–cocharacter pairings,
multiplied by its tangent parameter. The formula holds over every coefficient algebra and
requires no smoothness or projectivity assumption.

This gives the matrix calculation for identifying simple-coroot differentials with Cartan
vectors in a group defined by generators inside a general linear group.

The weight cocharacter `t ↦ diag(t ^ w a)` of `GL_N` itself, `weightCocharacter w`, is the
special case read directly off the generic matrix entries: it differentiates to the diagonal
matrix of its weights. For `w = Pi.single i 1` this is the matrix unit `Eᵢᵢ`, which is how a
weight vector of a rational representation is seen to be an eigenvector of `Eᵢᵢ`.

## Main declarations

* `tangentMatrix_derivationComp_cocharacter_of_weightTorus`: the matrix of a represented
  weight-torus cocharacter differential over any coefficient algebra.
* `weightCocharacter_apply_X`: the coordinate morphism of the weight cocharacter
  `t ↦ diag(t ^ w a)` of `GL_N` on the generic matrix entries.
* `tangentMatrix_derivationComp_weightCocharacter`: its differential, the diagonal matrix of the
  weights `w a` times the tangent parameter.
-/

public section

namespace TauCeti.GeneralLinear

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {sigma : Type w} [Finite sigma] {H : Type x} [CommRing H] [Bialgebra R H]
variable {N : ℕ} (q : coordinateHopfAlgebra R N →ₐc[R] H)
  (π : H →ₐc[R] MonoidAlgebra R (Multiplicative (sigma →₀ ℤ)))
  (wt : Fin N → sigma → ℤ) (hπ : π.comp q = weightTorusCoordinateBialgHom (S := R) wt)
  (ψ : Multiplicative (sigma →₀ ℤ) →* Multiplicative ℤ)

/-- **The weight cocharacter on the generic matrix entries**: its coordinate morphism sends the
generic diagonal entry `xₐₐ` to the Laurent monomial `T ^ w a` and every off-diagonal entry to
zero. This is the coordinate form of `t ↦ diag(t ^ w a)`, read off at the universal point. -/
@[simp]
theorem weightCocharacter_apply_X (w : Fin N → ℤ) (a b : Fin N) :
    weightCocharacter (R := R) w
        (coordinateHopfAlgebraAlgEquiv R N (coordinateRingMap R N (MvPolynomial.X (a, b)))) =
      if a = b then LaurentPolynomial.T (w a) else 0 := by
  have h := congrArg (fun p ↦ (pointsMulEquiv N p).val a b)
    (mapDomain_weightCocharacter (R := R) w (WithConv.toConv (AlgHom.id R _)))
  rw [pointsMulEquiv_weightCocharacterPoints] at h
  simp only [BialgHom.mapDomain_apply, AlgHom.id_comp, pointsMulEquiv_apply,
    pointToGeneralLinear_apply, BialgHom.coe_toAlgHom, MultiplicativeGroup.pointsMulEquiv_apply,
    diagGL_apply, weightDiagonalUnits_apply] at h
  rw [h, ← laurentEval_T (R := R), laurentEval_laurentEvalEquiv_symm, AlgHom.id_apply]

/-- **The differential of the weight cocharacter** `t ↦ diag(t ^ w a)` is the diagonal matrix of
its weights, multiplied by the tangent parameter. -/
@[simp]
theorem tangentMatrix_derivationComp_weightCocharacter (w : Fin N → ℤ)
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    tangentMatrix N (derivationComp (B := B) (weightCocharacter (R := R) w) d) =
      Matrix.diagonal fun a ↦ w a • MultiplicativeGroup.tangentLinearEquiv d := by
  ext a b
  rw [tangentMatrix_apply, algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom,
    weightCocharacter_apply_X, Matrix.diagonal_apply]
  split_ifs
  · rw [MultiplicativeGroup.derivation_T_zsmul, map_zsmul,
      MultiplicativeGroup.tangentLinearEquiv_apply]
  · rw [map_zero, map_zero]

include hπ

private theorem cocharacter_comp_apply_X_of_weightTorus (a b : Fin N) :
    π.cocharacter ψ
        (q (coordinateHopfAlgebraAlgEquiv R N
          (coordinateRingMap R N (MvPolynomial.X (a, b))))) =
      if a = b then
        LaurentPolynomial.T
          (ψ (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt a)))).toAdd
      else 0 := by
  rw [← BialgHom.cocharacter_id_comp π ψ, BialgHom.comp_apply,
    ← BialgHom.comp_apply π q, hπ, weightTorusCoordinateBialgHom_X]
  split_ifs <;> simp only [BialgHom.cocharacter_id_single, LaurentPolynomial.T, map_zero]

/-- The differential of a weight-torus cocharacter is diagonal, with entries the integer
character–cocharacter pairings times its tangent parameter. The weight representation may
factor through any commutative bialgebra, and coefficients may lie in any commutative algebra. -/
theorem tangentMatrix_derivationComp_cocharacter_of_weightTorus
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    tangentMatrix N (derivationComp (B := B) q (derivationComp (π.cocharacter ψ) d)) =
      Matrix.diagonal fun a ↦
        (ψ (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt a)))).toAdd •
          MultiplicativeGroup.tangentLinearEquiv d := by
  ext a b
  rw [tangentMatrix_apply, algEquivSelf_derivationComp_apply,
    algEquivSelf_derivationComp_apply]
  simp only [BialgHom.coe_toAlgHom]
  rw [cocharacter_comp_apply_X_of_weightTorus q π wt hπ ψ, Matrix.diagonal_apply]
  split_ifs with hab
  · rw [MultiplicativeGroup.derivation_T_zsmul, map_zsmul,
      MultiplicativeGroup.tangentLinearEquiv_apply]
  · simp only [map_zero]

end

end TauCeti.GeneralLinear
