/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent

/-!
# The adjoint action of the special linear group

The tangent Lie algebra of `SLₙ` is the Lie algebra of trace-zero matrices. Its adjoint
action is conjugation by the corresponding determinant-one matrix. The proof uses
equivariance of the differential of the closed immersion `SLₙ → GLₙ`, so the formula
holds over every commutative coefficient algebra, including nonreduced ones.

## Main declarations

* `TauCeti.SpecialLinear.counitPointsMulEquiv`: reads counit-valued points as determinant-one
  matrices.
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

/-- The determinant-one matrix of a point of `SLₙ` valued in its counit algebra. -/
noncomputable def counitPointsMulEquiv :
    WithConv (coordinateHopfAlgebra R n →ₐ[R]
        Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃*
      Matrix.SpecialLinearGroup (Fin n) B :=
  (Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R n) B).trans
    (pointsMulEquiv (R := R) (A := B) n)

/-- The image in `GLₙ` of a counit-valued `SLₙ` point is its canonical inclusion. -/
theorem toGL_counitPointsMulEquiv
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R]
      Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    Matrix.SpecialLinearGroup.toGL (counitPointsMulEquiv n g) =
      GeneralLinear.counitPointsMulEquiv n
        (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
          (GeneralLinear.coordinateHopfAlgebra R n) B) (coordinateMap R n).hom g) := by
  rw [counitPointsMulEquiv, MulEquiv.trans_apply]
  rw [GeneralLinear.counitPointsMulEquiv_eq_pointsMulEquiv]
  rw [← pointsMulEquiv_toGL (R := R) (A := B) n]
  rw [CommHopfAlgCat.quotientPointsHom_apply]
  congr 1
  ext x
  simp only [AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    Bialgebra.CounitAlgebra.pointsMulEquiv_apply]
  change _ = Bialgebra.CounitAlgebra.algEquivSelf R
    (GeneralLinear.coordinateHopfAlgebra R n) B
      (AlgHom.mapDomain (coordinateMap R n).hom g x)
  rw [AlgHom.mapDomain_apply_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply]
  rw [CommHopfAlgCat.hom_mkQuotient]
  exact (Bialgebra.CounitAlgebra.algEquivSelf_apply
    (R := R) (A := GeneralLinear.coordinateHopfAlgebra R n) (B := B)
      (g.ofConv ((coordinateMap R n).hom x))).symm

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
  rfl

end TauCeti.SpecialLinear
