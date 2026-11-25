/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange

/-!
# Conjugation on `GLₙ` and base change

For `P ∈ GLₙ(R)`, the coordinate automorphism `TauCeti.GeneralLinear.conjCoordinateIso P` of
`O(GLₙ)` is conjugation by `P`: it sends the generic matrix `X` to `P X P⁻¹`
(`TauCeti.GeneralLinear.genericMatrix_map_conjCoordinateIso_hom`). Since the base-change
isomorphism `K ⊗[R] O(GLₙ, R) ≅ O(GLₙ, K)` sends `1 ⊗ X` to the generic matrix over `K`, it
intertwines the scalar extension of conjugation by `P` with conjugation by the image of `P`
over `K` (`TauCeti.GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp`). This is the
naturality in the base ring of every isomorphism of subgroup schemes of `GLₙ` given by
conjugation by a constant matrix.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- **Conjugation by `P` on the generic matrix.** The coordinate automorphism of conjugation by `P`
sends the generic matrix `X` of `GLₙ` to `P X P⁻¹`. -/
theorem genericMatrix_map_conjCoordinateIso_hom (P : GL (Fin n) R) :
    (genericMatrix R n).map (conjCoordinateIso P).hom.hom =
      (GeneralLinearGroup.map (algebraMap R (coordinateHopfAlgebra R n)) P :
          Matrix (Fin n) (Fin n) (coordinateHopfAlgebra R n)) *
        genericMatrix R n *
        ((GeneralLinearGroup.map (algebraMap R (coordinateHopfAlgebra R n)) P)⁻¹ :
          GL (Fin n) (coordinateHopfAlgebra R n)) := by
  have h := pointsMulEquiv_toConv_comp_conjCoordinateIso P (coordinateHopfAlgebra R n)
    (toConv (AlgHom.id R _))
  have hG : ((pointsMulEquiv n (toConv (AlgHom.id R (coordinateHopfAlgebra R n))) :
      GL (Fin n) (coordinateHopfAlgebra R n)) : Matrix (Fin n) (Fin n) _) = genericMatrix R n := by
    ext i j
    rw [pointsMulEquiv_apply, pointToGeneralLinear_apply, genericMatrix_apply]
    rfl
  calc _ = ((pointsMulEquiv n (toConv ((AlgHom.id R (coordinateHopfAlgebra R n)).comp
          ((conjCoordinateIso P).hom.hom : coordinateHopfAlgebra R n →ₐ[R]
            coordinateHopfAlgebra R n))) : GL (Fin n) (coordinateHopfAlgebra R n)) :
          Matrix (Fin n) (Fin n) _) := by
        ext i j
        rw [pointsMulEquiv_apply, pointToGeneralLinear_apply, Matrix.map_apply,
          genericMatrix_apply]
        rfl
    _ = _ := by
        rw [h, Units.val_mul, Units.val_mul, hG]


/-- **Conjugation commutes with base change.** Along the base-change isomorphism
`K ⊗[R] O(GLₙ, R) ≅ O(GLₙ, K)`, the scalar extension of the coordinate automorphism of conjugation
by `P` is the coordinate automorphism of conjugation by the image of `P` over `K`. -/
theorem baseChangeMap_conjCoordinateIso_hom_comp (K : Type max u v) [CommRing K] [Algebra R K]
    (P : GL (Fin n) R) :
    CommHopfAlgCat.baseChangeMap (K := K) (conjCoordinateIso P).hom ≫
        (coordinateHopfAlgebraBaseChangeIso R K n).hom =
      (coordinateHopfAlgebraBaseChangeIso R K n).hom ≫
        (conjCoordinateIso (GeneralLinearGroup.map (algebraMap R K) P)).hom := by
  let _ : Algebra R (coordinateHopfAlgebra K n) := Algebra.compHom _ (algebraMap R K)
  let _ : IsScalarTower R K (coordinateHopfAlgebra K n) := IsScalarTower.of_algebraMap_eq' rfl
  set ψ : coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra K n :=
    ((coordinateHopfAlgebraBaseChangeIso R K n).hom.hom.toAlgHom.restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  have hG : (genericMatrix R n).map ψ = genericMatrix K n :=
    coordinateHopfAlgebraBaseChangeIso_hom_genericMatrix R K n
  have hP : ∀ Q : GL (Fin n) R,
      ((GeneralLinearGroup.map (algebraMap R (coordinateHopfAlgebra R n)) Q :
        Matrix (Fin n) (Fin n) _)).map ψ =
        (GeneralLinearGroup.map (algebraMap K (coordinateHopfAlgebra K n))
          (GeneralLinearGroup.map (algebraMap R K) Q) : Matrix (Fin n) (Fin n) _) := by
    intro Q
    ext i j
    simp only [Matrix.map_apply, GeneralLinearGroup.map_apply, AlgHom.commutes]
    rfl
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply coordinateHopfAlgebra_baseChange_algHom_ext R K n
  intro i j
  have hL := congrFun (congrFun (genericMatrix_map_conjCoordinateIso_hom P) i) j
  have hR := congrFun (congrFun (genericMatrix_map_conjCoordinateIso_hom
    (GeneralLinearGroup.map (algebraMap R K) P)) i) j
  rw [Matrix.map_apply, genericMatrix_apply] at hL hR
  simp only [CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom]
  rw [CommHopfAlgCat.baseChangeMap_apply_tmul, coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X,
    hR, hL]
  have hψx : ∀ x, (coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x) = ψ x :=
    fun x => rfl
  rw [hψx, ← Matrix.map_apply (f := ψ), Matrix.map_mul, Matrix.map_mul, hG, hP, ← map_inv,
    ← map_inv, hP, map_inv]

end TauCeti.GeneralLinear
