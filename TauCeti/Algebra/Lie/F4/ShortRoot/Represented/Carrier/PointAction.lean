/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Carrier.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction

/-!
# Point actions of the represented F4 carrier quotient

This file identifies the matrix obtained by evaluating the coordinate morphism of the
represented carrier quotient with the corresponding point action on its scalar extension.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory
open scoped TensorProduct

noncomputable section

local notation "𝔽₂" => ZMod 2

attribute [local instance] f4ShortRootAmbientCotangentComodule

/-- An equality of represented vectors under the ambient carrier action descends to the
modular quotient. Only the inclusion of the represented range is cancelled, not the adjoint
representation itself. -/
theorem f4ShortRootQuotient_endOfPoint_of_represented
    {A : Type*} [CommRing A] [Algebra 𝔽₂ A]
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (x y : A ⊗[𝔽₂] f4ModularChevalleyLieAlgebra)
    (h : Comodule.endOfPoint f4ShortRootCotangentDual g
        (f4ShortRootCarrierCotangentRange.subtype.toLinearMap.baseChange A
          (f4ShortRootCarrierRepresentedMap.baseChange A x)) =
      f4ShortRootCarrierCotangentRange.subtype.toLinearMap.baseChange A
        (f4ShortRootCarrierRepresentedMap.baseChange A y)) :
    Comodule.endOfPoint (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) g
        (f4ShortRootSubspace.mkQ.baseChange A x) =
      f4ShortRootSubspace.mkQ.baseChange A y := by
  let i := f4ShortRootCarrierCotangentRange.subtype
  let π := f4ShortRootCarrierQuotientProjection
  let r := f4ShortRootCarrierRepresentedMap.baseChange A
  have hi : Function.Injective (i.toLinearMap.baseChange A) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      i.toLinearMap (by
        intro v w hvw
        apply Subtype.ext
        simpa only [i, Comodule.Hom.coe_toLinearMap, Subcomodule.subtype_apply] using hvw)
  have hRange : Comodule.endOfPoint f4ShortRootCarrierCotangentRange g (r x) = r y := by
    apply hi
    exact (DFunLike.congr_fun (Comodule.baseChange_comp_endOfPoint i g) (r x)).trans h
  have hq (z : A ⊗[𝔽₂] f4ModularChevalleyLieAlgebra) :
      π.toLinearMap.baseChange A (r z) = f4ShortRootSubspace.mkQ.baseChange A z :=
    DFunLike.congr_fun
      f4ShortRootCarrierQuotientProjection_baseChange_comp_representedMap z
  calc
    _ = Comodule.endOfPoint _ g (π.toLinearMap.baseChange A (r x)) :=
      congrArg (Comodule.endOfPoint _ g) (hq x).symm
    _ = π.toLinearMap.baseChange A
        (Comodule.endOfPoint f4ShortRootCarrierCotangentRange g (r x)) :=
      (DFunLike.congr_fun (Comodule.baseChange_comp_endOfPoint π g) (r x)).symm
    _ = π.toLinearMap.baseChange A (r y) := congrArg _ hRange
    _ = _ := hq y

/-- Matrix coordinates of the scalar-extended represented map are the existing adjoint
matrices. This identifies the two realizations without choosing representatives in the
middle quotient. -/
theorem f4ShortRootCotangentBaseChangeMatrixEquiv_representedMap
    {A : Type} [CommRing A] [Algebra 𝔽₂ A]
    (x : A ⊗[𝔽₂] f4ModularChevalleyLieAlgebra) :
    f4ShortRootCotangentBaseChangeMatrixEquiv
        (f4ShortRootCarrierCotangentRange.subtype.toLinearMap.baseChange A
          (f4ShortRootCarrierRepresentedMap.baseChange A x)) =
      f4ShortRootBaseChangeAdjointMatrixLinearMap
        (TauCeti.cancelBaseChange ℤ 𝔽₂ A f4ChevalleyLieLattice x) := by
  have hmaps :
      f4ShortRootCotangentBaseChangeMatrixEquiv.toLinearMap ∘ₗ
        f4ShortRootCarrierCotangentRange.subtype.toLinearMap.baseChange A ∘ₗ
          f4ShortRootCarrierRepresentedMap.baseChange A =
        f4ShortRootBaseChangeAdjointMatrixLinearMap ∘ₗ
          (TauCeti.cancelBaseChange ℤ 𝔽₂ A
            f4ChevalleyLieLattice).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a X
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      Comodule.Hom.coe_toLinearMap, Subcomodule.subtype_apply,
      LinearEquiv.coe_toLinearMap,
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply,
      GeneralLinear.tangentMatrix_tangentScalarExtensionEquiv_tmul]
    change a • (GeneralLinear.cotangentDualMatrixEquiv
        (f4ShortRootCarrierRepresentedMap X : f4ShortRootCotangentDual)).map _ =
      f4ShortRootBaseChangeAdjointMatrixLinearMap
        (TauCeti.cancelBaseChange ℤ 𝔽₂ A
          f4ChevalleyLieLattice (a ⊗ₜ[𝔽₂] X))
    calc
      _ = a • (GeneralLinear.cotangentDualMatrixEquiv
          (f4ShortRootEndEquivCotangentDual (f4ShortRootAdjoint X))).map
            (algebraMap 𝔽₂ A) :=
        congrArg (fun v : f4ShortRootCotangentDual =>
          a • (GeneralLinear.cotangentDualMatrixEquiv v).map (algebraMap 𝔽₂ A))
          (f4ShortRootCarrierRepresentedMap_apply X)
      _ = a • f4ShortRootAdjointMatrixBaseChange (A := A) X := by
        rw [cotangentDualMatrixEquiv_f4ShortRootEndEquivCotangentDual]
        ext i j
        simp [f4ShortRootAdjointMatrixBaseChange, LinearMap.toMatrix_apply]
      _ = _ := (f4ShortRootBaseChangeAdjointMatrixLinearMap_cancel_tmul a X).symm
  exact DFunLike.congr_fun hmaps x

/-- The carrier cotangent action, in matrix coordinates, is conjugation by its ambient
general-linear point. -/
theorem f4ShortRootCotangentBaseChangeMatrixEquiv_endOfPoint
    {A : Type} [CommRing A] [Algebra 𝔽₂ A]
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (v : A ⊗[𝔽₂] f4ShortRootCotangentDual) :
    let G := GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom))
    f4ShortRootCotangentBaseChangeMatrixEquiv
        (Comodule.endOfPoint f4ShortRootCotangentDual g v) =
      (G : Matrix (Fin 26) (Fin 26) A) * f4ShortRootCotangentBaseChangeMatrixEquiv v *
        ((G⁻¹ : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
  let φ := (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
    (CommHopfAlgCat.commonKernelHopfIdeal F4ShortRoot.PrimeField.generator)).hom
  let g' := WithConv.toConv (g.comp φ.toAlgHom)
  have hcorestrict : Comodule.endOfPoint f4ShortRootCotangentDual g =
      (letI := Derivation.adjointComodule
        (R := 𝔽₂) (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
       Comodule.endOfPoint f4ShortRootCotangentDual g'.ofConv) :=
    Comodule.endOfPoint_corestrict φ g
  rw [hcorestrict]
  have hconj := GeneralLinear.tangentMatrix_adjointComodule_endOfPoint g' v
  simpa only [f4ShortRootCotangentBaseChangeMatrixEquiv_apply] using hconj

private theorem cotangent_endOfPoint_root
    {A : Type} [CommRing A] [Algebra 𝔽₂ A]
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints k A u)
    (v : A ⊗[𝔽₂] f4ShortRootCotangentDual) :
    f4ShortRootCotangentBaseChangeMatrixEquiv
        (Comodule.endOfPoint f4ShortRootCotangentDual g v) =
      (Matrix.lieConj
        ((F4ShortRoot.rootSubgroupPoints k A u : GL (Fin 26) A) :
          Matrix (Fin 26) (Fin 26) A)
        (Units.invertible (F4ShortRoot.rootSubgroupPoints k A u : GL (Fin 26) A)))
        (f4ShortRootCotangentBaseChangeMatrixEquiv v) := by
  have h := f4ShortRootCotangentBaseChangeMatrixEquiv_endOfPoint g v
  dsimp only at h
  rw [hg] at h
  simpa only [Matrix.lieConj_apply, Matrix.GeneralLinearGroup.coe_inv] using h

/-- The action of a carrier root point on the actual quotient comodule is induced by the
integral root exponential. -/
theorem f4ShortRootQuotient_endOfPoint_root
    {A : Type} [CommRing A] [Algebra 𝔽₂ A]
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints k A u)
    (x : A ⊗[𝔽₂] f4ModularChevalleyLieAlgebra) :
    Comodule.endOfPoint (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) g
        (f4ShortRootSubspace.mkQ.baseChange A x) =
      f4ShortRootSubspace.mkQ.baseChange A
        ((TauCeti.cancelBaseChange ℤ 𝔽₂ A f4ChevalleyLieLattice).symm
          (f4RootExponential k (Multiplicative.toAdd u)
            (TauCeti.cancelBaseChange ℤ 𝔽₂ A f4ChevalleyLieLattice x))) := by
  let e := f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
  let c := TauCeti.cancelBaseChange ℤ 𝔽₂ A f4ChevalleyLieLattice
  let C := Matrix.lieConj
    ((F4ShortRoot.rootSubgroupPoints k A u : GL (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A)
    (Units.invertible (F4ShortRoot.rootSubgroupPoints k A u : GL (Fin 26) A))
  let v := f4ShortRootCarrierCotangentRange.subtype.toLinearMap.baseChange A
    (f4ShortRootCarrierRepresentedMap.baseChange A x)
  apply f4ShortRootQuotient_endOfPoint_of_represented
  apply e.injective
  calc
    _ = C (e v) := cotangent_endOfPoint_root g k u hg v
    _ = C (f4ShortRootBaseChangeAdjointMatrixLinearMap (c x)) :=
      congrArg C (f4ShortRootCotangentBaseChangeMatrixEquiv_representedMap x)
    _ = f4ShortRootBaseChangeAdjointMatrixLinearMap
        (f4RootExponential k (Multiplicative.toAdd u) (c x)) :=
      f4ShortRootRoot_lieConj_adjoint k u (c x)
    _ = f4ShortRootBaseChangeAdjointMatrixLinearMap
        (c (c.symm (f4RootExponential k (Multiplicative.toAdd u) (c x)))) :=
      congrArg f4ShortRootBaseChangeAdjointMatrixLinearMap (c.apply_symm_apply _).symm
    _ = _ := (f4ShortRootCotangentBaseChangeMatrixEquiv_representedMap _).symm

/-- Evaluating the represented quotient's coordinate morphism gives the matrix of the induced
point action in the prescribed quotient basis. -/
theorem pointsMulEquiv_comp_f4ShortRootQuotientCoordinateBialgHom
    {A : Type*} [CommRing A] [Algebra 𝔽₂ A]
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A) :
    (GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv
          (g.comp f4ShortRootQuotientCoordinateBialgHom.toAlgHom)) :
      Matrix (Fin 26) (Fin 26) A) =
      LinearMap.toMatrix (f4ShortRootQuotientBasis.baseChange A)
        (f4ShortRootQuotientBasis.baseChange A)
        (Comodule.endOfPoint
          (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) g) := by
  calc
    _ = (Comodule.coefficientMatrix
          (C := f4ShortRootCarrierCoordinateHopfAlgebra)
          f4ShortRootQuotientBasis).map g :=
      AlgHom.pointsMulEquiv_comp_coordinateBialgHom g f4ShortRootQuotientBasis
    _ = _ := (Comodule.toMatrix_endOfPoint f4ShortRootQuotientBasis g).symm

end

end TauCeti.DynkinType
