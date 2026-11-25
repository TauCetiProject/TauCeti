/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange

/-!
# Conjugation on `GLₙ` and base change

For `P ∈ GLₙ(R)`, the coordinate automorphism `TauCeti.GeneralLinear.conjCoordinateIso P` of
`O(GLₙ)` is conjugation by `P`: it sends the generic matrix `X` to `P X P⁻¹`
(`TauCeti.GeneralLinear.genericMatrix_map_conjCoordinateIso_hom`). Since the base-change
isomorphism `K ⊗[R] O(GLₙ, R) ≅ O(GLₙ, K)` sends `1 ⊗ X` to the generic matrix over `K`, it
intertwines the scalar extension of conjugation by `P` with conjugation by the image of `P`
over `K` (`TauCeti.GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp`). This is the
`GLₙ`-level ingredient from which the naturality in the base ring of the coordinate isomorphisms
of subgroups of `GLₙ` given by conjugation by a constant matrix follows; naturality of the
corresponding group-scheme isomorphisms is not proved here.
-/

public section

open CategoryTheory Matrix WithConv
open scoped TensorProduct

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
  rw [ofConv_toConv, AlgHom.id_comp] at h
  have hG := map_genericMatrix_eq_coe_pointToGeneralLinear n
    (AlgHom.id R (coordinateHopfAlgebra R n))
  rw [AlgHom.coe_id, Matrix.map_id, ← pointsMulEquiv_apply] at hG
  rw [← BialgHom.coe_toAlgHom, map_genericMatrix_eq_coe_pointToGeneralLinear,
    ← pointsMulEquiv_apply, h, Units.val_mul, Units.val_mul, ← hG]

/-- **Conjugation commutes with base change.** Along the base-change isomorphism
`K ⊗[R] O(GLₙ, R) ≅ O(GLₙ, K)`, the scalar extension of the coordinate automorphism of conjugation
by `P` is the coordinate automorphism of conjugation by the image of `P` over `K`. -/
@[reassoc]
theorem baseChangeMap_conjCoordinateIso_hom_comp (K : Type max u v) [CommRing K] [Algebra R K]
    (P : GL (Fin n) R) :
    CommHopfAlgCat.baseChangeMap (K := K) (conjCoordinateIso P).hom ≫
        (coordinateHopfAlgebraBaseChangeIso R K n).hom =
      (coordinateHopfAlgebraBaseChangeIso R K n).hom ≫
        (conjCoordinateIso (GeneralLinearGroup.map (algebraMap R K) P)).hom := by
  -- The base-change isomorphism restricted to `1 ⊗ O(GLₙ, R)`, as a ring morphism.
  let ψ : coordinateHopfAlgebra R n →+* coordinateHopfAlgebra K n :=
    ((coordinateHopfAlgebraBaseChangeIso R K n).hom.hom :
        K ⊗[R] coordinateHopfAlgebra R n →+* coordinateHopfAlgebra K n).comp
      (Algebra.TensorProduct.includeRight :
        coordinateHopfAlgebra R n →ₐ[R] K ⊗[R] coordinateHopfAlgebra R n).toRingHom
  have hψ (x : coordinateHopfAlgebra R n) :
      (coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x) = ψ x := by
    simp [ψ]
  have hG : (genericMatrix R n).map ψ = genericMatrix K n := by
    ext i j
    rw [Matrix.map_apply, ← hψ, genericMatrix_apply, genericMatrix_apply,
      coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X]
  have hP (Q : GL (Fin n) R) :
      ((GeneralLinearGroup.map (algebraMap R (coordinateHopfAlgebra R n)) Q :
        Matrix (Fin n) (Fin n) _)).map ψ =
        (GeneralLinearGroup.map (algebraMap K (coordinateHopfAlgebra K n))
          (GeneralLinearGroup.map (algebraMap R K) Q) : Matrix (Fin n) (Fin n) _) := by
    ext i j
    rw [Matrix.map_apply, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply,
      GeneralLinearGroup.map_apply, ← hψ, ← Algebra.TensorProduct.algebraMap_apply',
      IsScalarTower.algebraMap_apply R K (K ⊗[R] coordinateHopfAlgebra R n), AlgHomClass.commutes]
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
    hR, hL, hψ, ← Matrix.map_apply (f := ψ), Matrix.map_mul, Matrix.map_mul, hG, hP, ← map_inv,
    ← map_inv, hP, map_inv]

end TauCeti.GeneralLinear
