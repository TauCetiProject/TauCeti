/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Carrier.PointAction
public import TauCeti.LinearAlgebra.Matrix.Diagonal
public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Pinning.Basic
public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Torus

/-!
# Torus pinning of the represented F4 quotient comodule

The weight-torus action on the represented F4 quotient is diagonal in its canonical basis, with
weights given by the special character-lattice map. This torus pinning and the root formulas
characterize the carrier special isogeny on its generators.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory
open scoped TensorProduct

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

/-- Conjugation scales the represented canonical quotient lift by its long-root character,
with character zero on the two Cartan coordinates. -/
theorem f4ShortRootWeightTorusConj_quotientLift (s : Fin 4 → Aˣ) (a : Fin 26) :
    (Matrix.lieConj (f4ShortRootWeightTorusGL s : Matrix (Fin 26) (Fin 26) A)
      (Units.invertible (f4ShortRootWeightTorusGL s)))
        (f4ShortRootAdjointMatrixBaseChange (A := A) (f4ShortRootQuotientLift a)) =
      ((torusCharacter s (f4ShortRootQuotientWeight a) : Aˣ) : A) •
        f4ShortRootAdjointMatrixBaseChange (A := A) (f4ShortRootQuotientLift a) := by
  obtain ⟨i | j, rfl⟩ := f4ShortRootWeightIndexEquiv.symm.surjective a
  · simpa only [Matrix.lieConj_apply, Matrix.GeneralLinearGroup.coe_inv,
      f4ShortRootQuotientLift_eq_basis, f4LongRootBasisCoordinate_symm_inl,
      f4ShortRootQuotientWeight_symm_inl,
      f4ModularRootVector_eq_basis] using
        f4ShortRootWeightTorusGL_conj_root s (f4SpecialIsogenyIndexEquiv i)
  · simpa only [Matrix.lieConj_apply, Matrix.GeneralLinearGroup.coe_inv,
      f4ShortRootQuotientLift_eq_basis, f4LongRootBasisCoordinate_symm_inr,
      f4ShortRootQuotientWeight_symm_inr,
      f4ModularSimpleCoroot_eq_basis,
      torusCharacter_zero, Units.val_one, one_smul] using
        f4ShortRootWeightTorusGL_conj_simpleCoroot s
          (f4LongSimpleIndex j)

private theorem matrixEquiv_representedMap_one_tmul (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootCotangentBaseChangeMatrixEquiv
        (f4ShortRootCarrierCotangentRange.subtype.toLinearMap.baseChange A
          (f4ShortRootCarrierRepresentedMap.baseChange A ((1 : A) ⊗ₜ[𝔽₂] X))) =
      f4ShortRootAdjointMatrixBaseChange (A := A) X := by
  exact (f4ShortRootCotangentBaseChangeMatrixEquiv_representedMap _).trans
    ((f4ShortRootBaseChangeAdjointMatrixLinearMap_cancel_tmul (1 : A) X).trans
      (one_smul A _))

private theorem cotangent_endOfPoint_torus
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom)) = f4ShortRootWeightTorusGL s)
    (v : A ⊗[𝔽₂] f4ShortRootCotangentDual) :
    f4ShortRootCotangentBaseChangeMatrixEquiv
        (Comodule.endOfPoint f4ShortRootCotangentDual g v) =
      (Matrix.lieConj (f4ShortRootWeightTorusGL s : Matrix (Fin 26) (Fin 26) A)
      (Units.invertible (f4ShortRootWeightTorusGL s)))
        (f4ShortRootCotangentBaseChangeMatrixEquiv v) := by
  have h := f4ShortRootCotangentBaseChangeMatrixEquiv_endOfPoint g v
  dsimp only at h
  rw [hg] at h
  simpa only [Matrix.lieConj_apply, Matrix.GeneralLinearGroup.coe_inv] using h

/-- The actual quotient carrier action is diagonal on the prescribed quotient basis, with
weights pulled back along the special torus map. -/
theorem f4ShortRootQuotient_endOfPoint_torus
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom)) = f4ShortRootWeightTorusGL s)
    (a : Fin 26) :
    Comodule.endOfPoint (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) g
        ((f4ShortRootQuotientBasis.baseChange A) a) =
      ((torusCharacter (f4SpecialIsogenyTorusMap s) (f4ShortRootWeight a) : Aˣ) : A) •
        ((f4ShortRootQuotientBasis.baseChange A) a) := by
  let x := (1 : A) ⊗ₜ[𝔽₂] f4ShortRootQuotientLift a
  let c : A := torusCharacter s (f4ShortRootQuotientWeight a)
  let i := f4ShortRootCarrierCotangentRange.subtype.toLinearMap.baseChange A
  let r := f4ShortRootCarrierRepresentedMap.baseChange A
  let e := f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
  let C := Matrix.lieConj (f4ShortRootWeightTorusGL s : Matrix (Fin 26) (Fin 26) A)
    (Units.invertible (f4ShortRootWeightTorusGL s))
  have hmatrix : e (Comodule.endOfPoint f4ShortRootCotangentDual g (i (r x))) =
      e (i (r (c • x))) := by
    calc
      _ = C (e (i (r x))) :=
        cotangent_endOfPoint_torus g s hg _
      _ = C (f4ShortRootAdjointMatrixBaseChange (A := A) (f4ShortRootQuotientLift a)) :=
        congrArg C
          (matrixEquiv_representedMap_one_tmul _)
      _ = c • f4ShortRootAdjointMatrixBaseChange (A := A) (f4ShortRootQuotientLift a) :=
        f4ShortRootWeightTorusConj_quotientLift s a
      _ = c • e (i (r x)) := congrArg (c • ·)
        (matrixEquiv_representedMap_one_tmul _).symm
      _ = _ := ((e.toLinearMap.comp (i.comp r)).map_smul c x).symm
  have h := f4ShortRootQuotient_endOfPoint_of_represented g x (c • x)
    (e.injective hmatrix)
  have hq : f4ShortRootSubspace.mkQ.baseChange A x =
      (f4ShortRootQuotientBasis.baseChange A) a := by
    simp only [x, LinearMap.baseChange_tmul, f4ShortRootSubspace_mkQ_quotientLift,
      Module.Basis.baseChange_apply]
  have hq' := (f4ShortRootSubspace.mkQ.baseChange A).map_smul c x
  exact (congrArg (Comodule.endOfPoint _ g) hq.symm).trans
    (h.trans (hq'.trans ((congrArg (c • ·) hq).trans
      (congrArg (fun t : A => t • ((f4ShortRootQuotientBasis.baseChange A) a))
        (coe_torusCharacter_f4ShortRootQuotientWeight s a)))))

/-- Evaluating the quotient coordinate map at a weight-torus point applies the special torus
map to that point. -/
theorem pointsMulEquiv_f4ShortRootQuotientCoordinateBialgHom_torus
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom)) = f4ShortRootWeightTorusGL s) :
    GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp f4ShortRootQuotientCoordinateBialgHom.toAlgHom)) =
      f4ShortRootWeightTorusGL (f4SpecialIsogenyTorusMap s) := by
  apply Units.ext
  calc
    _ = LinearMap.toMatrix (f4ShortRootQuotientBasis.baseChange A)
        (f4ShortRootQuotientBasis.baseChange A) (Comodule.endOfPoint _ g) :=
      pointsMulEquiv_comp_f4ShortRootQuotientCoordinateBialgHom g
    _ = Matrix.diagonal (fun a =>
        ((torusCharacter (f4SpecialIsogenyTorusMap s) (f4ShortRootWeight a) : Aˣ) : A)) :=
      (f4ShortRootQuotientBasis.baseChange A).toMatrix_eq_diagonal_of_basis _ _
        (f4ShortRootQuotient_endOfPoint_torus g s hg)
    _ = _ := (TauCeti.diagGL_coe _).symm

end

end TauCeti.DynkinType
