/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Equivariance

/-!
# The adjoint action of the special linear group

The tangent Lie algebra of `SLₙ` is the Lie algebra of trace-zero matrices. Its adjoint
action is conjugation by the corresponding determinant-one matrix. The proof uses
equivariance of the differential of the closed immersion `SLₙ → GLₙ`, so the formula
holds over every commutative coefficient algebra, including nonreduced ones.

## Main declarations

* `TauCeti.SpecialLinear.tangentMatrix_adDerivation`: identifies the adjoint action
  on `Lie(SLₙ)` with conjugation by its image in `GLₙ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10 and §14.
-/

public section

namespace TauCeti.SpecialLinear

open WithConv

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
variable (n : ℕ)

/-- The adjoint action of `SLₙ` on its tangent Lie algebra is conjugation on trace-zero
matrices by the ambient `GLₙ` point. This holds for every commutative coefficient algebra. -/
@[simp]
theorem tangentMatrix_adDerivation
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R]
      Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B))
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    (tangentMatrix n (Derivation.adDerivation B g d) : Matrix (Fin n) (Fin n) B) =
      (GeneralLinear.counitPointsMulEquiv n
        (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
          (GeneralLinear.coordinateHopfAlgebra R n) B) (coordinateMap R n).hom g) :
        Matrix (Fin n) (Fin n) B) *
      (tangentMatrix n d : Matrix (Fin n) (Fin n) B) *
      ((GeneralLinear.counitPointsMulEquiv n
        (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
          (GeneralLinear.coordinateHopfAlgebra R n) B) (coordinateMap R n).hom g))⁻¹ :
        Matrix.GeneralLinearGroup (Fin n) B) := by
  let φ : GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] coordinateHopfAlgebra R n :=
    (coordinateMap R n).hom
  let g' : WithConv (GeneralLinear.coordinateHopfAlgebra R n →ₐ[R]
      Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B) :=
    AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
      (GeneralLinear.coordinateHopfAlgebra R n) B) φ g
  have hquot (e : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
      HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) e =
        derivationComp φ e := by
    apply Derivation.ext
    intro x
    rw [HopfIdeal.quotientLieHom_apply_apply, derivationComp_apply]
    simp only [Bialgebra.CounitAlgebra.algEquivSelf_apply]
    exact congrArg e (coordinateMap_apply (R := R) (n := n) x).symm
  have hdiff : HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n)
      (Derivation.adDerivation B g d) =
      Derivation.adDerivation B g'
        (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) d) := by
    rw [hquot, hquot]
    exact derivationComp_adDerivation φ g d
  rw [tangentMatrix_apply_coe, hdiff, GeneralLinear.tangentMatrix_adDerivation]
  rw [← tangentMatrix_apply_coe n d]

end TauCeti.SpecialLinear
