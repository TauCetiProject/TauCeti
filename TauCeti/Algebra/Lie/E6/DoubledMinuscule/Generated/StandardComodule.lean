/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.Basic
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.CompletelyReducible

/-!
# The standard representation of the generated doubled E₆ subgroup

The subgroup of `GL₅₄` generated over a commutative ring by the numbered doubled minuscule
root subgroups and weight torus has a faithful standard comodule. Over every field it is
completely reducible: its distinct torus characters extract coordinate lines, root matrices
connect each of the two minuscule blocks, and its matrix coefficients preserve those blocks.

This concerns the subgroup generated over the coefficient ring, not the specialization of the
integral toral closure. No equality between these subgroup schemes or identification with the
pinned simply connected group scheme of type `E₆` is asserted.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 26.

The quotient-comodule and generator-lift construction follows
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.StandardComodule` and
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.StandardComodule`.
The weight-graph argument is shared with
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.CompletelyReducible`.
-/

public section

open CategoryTheory WithConv
open TauCeti.UniversalEnvelopingAlgebra
open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

universe u v

variable (R : Type u) [CommRing R]

/-- The weight torus factored through the subgroup generated over the coefficient ring. -/
noncomputable def generatedWeightTorusCoordinateMap :
    generatedCoordinateHopfAlgebra R ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 6))).obj :=
  generatedCoordinateLift R (.inr ())

/-- The generated subgroup's weight torus recovers the ambient doubled minuscule weight torus. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap :
    generatedCoordinateMap R ≫ generatedWeightTorusCoordinateMap R =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ R matrixWeight := by
  rw [generatedWeightTorusCoordinateMap, generatedCoordinateMap_comp_generatedCoordinateLift,
    generatorCoordinateMap_inr]

/-- A point induced by a generated root-subgroup lift maps to the numbered doubled minuscule
root matrix with the same parameter, over every value algebra. -/
-- Rewrite the dependent generator codomain before `mapDomain_apply` unfolds it.
@[simp↓]
theorem pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    (i : Fin 6 ⊕ Fin 6) (B : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) B) :
    GeneralLinear.pointToGeneralLinear 54
        (AlgHom.mapDomain (generatedCoordinateMap R).hom
          (no_index (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl i)).hom.toAlgHom)))) =
      (rootSubgroupPoints i B (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 54) B) := by
  let f := kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight R i
  have hcomp : generatedCoordinateMap R ≫ generatedCoordinateLift R (.inl i) =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R 54)
        (kostantToralBaseChangePresentationIdeal
          (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
          (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
          rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator
          matrixBasis matrixWeight R) ≫ f := by
    rw [generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inl]
    exact (mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
      _ _ _ _ _ _ _ _ _ i).symm
  have hpoint : AlgHom.mapDomain (generatedCoordinateMap R).hom
      (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl i)).hom.toAlgHom)) =
      CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R 54) _ B
        (toConv (q.ofConv.comp f.hom.toAlgHom)) := by
    apply WithConv.ext
    ext x
    exact congrArg (fun g ↦ q.ofConv (g.hom x)) hcomp
  have h := pointsMulEquiv_kostantRootSubgroupToralBaseChangeCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis
    matrixWeight R definingIdeal_def i B q
  -- The point functor's component uses the indexed presentation of the same points.
  erw [CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  rw [hpoint, ← GeneralLinear.pointsMulEquiv_apply, coe_rootSubgroupPoints]
  exact h

/-- The standard right comodule of the generated doubled minuscule subgroup on `R⁵⁴`. -/
@[instance_reducible]
noncomputable def generatedStandardComodule :
    Comodule R (generatedCoordinateHopfAlgebra R) (Fin 54 → R) :=
  GeneralLinear.corestrictStandardComodule R 54 (generatedCoordinateMap R).hom

attribute [local instance] GeneralLinear.standardComodule generatedStandardComodule

/-- The generated subgroup's standard comodule is faithful over every commutative ring. -/
theorem isFaithful_generatedStandardComodule :
    Comodule.IsFaithful (k := R) (H := generatedCoordinateHopfAlgebra R) (V := Fin 54 → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R 54 (generatedCoordinateMap R).hom
    (generatedCoordinateMap_surjective R)

/-- Subcomodules of the generated subgroup's standard comodule are stable under the numbered
positive and negative doubled minuscule root matrices, with any parameter. -/
theorem generatedRootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (generatedCoordinateHopfAlgebra R) (Fin 54 → R))
    (i : Fin 6 ⊕ Fin 6) (t : Multiplicative R) {w : Fin 54 → R} (hw : w ∈ N) :
    ((rootSubgroupPoints i R t : Matrix.GeneralLinearGroup (Fin 54) R) :
      Matrix (Fin 54) (Fin 54) R) *ᵥ w ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R 54
    (generatedCoordinateMap R).hom N
    (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl i)).hom.toAlgHom)) hw
  rw [pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints R i
    (CommAlgCat.of R R) q, MulEquiv.apply_symm_apply] at h
  exact h

/-- Restriction to the generated weight torus is the direct sum of the fifty-four character
lines of the doubled minuscule representation. -/
theorem generatedTorusCorestrict_eq_ofWeights :
    Comodule.Corestrict (generatedWeightTorusCoordinateMap R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 54)) minusculeCharacter := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (generatedCoordinateMap R).hom (generatedWeightTorusCoordinateMap R).hom matrixWeight
  rw [← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- The generated subgroup's standard matrix coefficients do not mix the two minuscule blocks.
-/
theorem generatedCoefficientMatrix_eq_zero_of_summand_ne (a b : Fin 54)
    (hab : matrixSummand a ≠ matrixSummand b) :
    Comodule.coefficientMatrix (C := generatedCoordinateHopfAlgebra R)
      (Pi.basisFun R (Fin 54)) a b = 0 := by
  rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
    GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
    GeneralLinear.genericMatrix_apply]
  apply RingHom.mem_ker.mp
  rw [generatedCoordinateMap_ker]
  apply baseChangeDefiningIdeal_le_generatedDefiningIdeal R
  have h := RingHom.mem_ker.mpr (coordinateMap_X_eq_zero R hab)
  rw [coordinateMap_ker] at h
  exact h

/-- The generated subgroup's faithful doubled minuscule comodule is completely reducible over
every field, including characteristics two and three. -/
theorem isCompletelyReducible_generatedStandardComodule (k : Type u) [Field k] :
    let _ := generatedStandardComodule k
    Comodule.IsCompletelyReducible k (generatedCoordinateHopfAlgebra k) (Fin 54 → k) :=
  isCompletelyReducible_of_minusculeWeights_of_rootSubgroupPoints k
    (generatedWeightTorusCoordinateMap k).hom.toCoalgHom
    (generatedTorusCorestrict_eq_ofWeights k)
    (fun N i _ hw ↦ generatedRootSubgroupPoints_mulVec_mem k N i (Multiplicative.ofAdd 1) hw)
    (generatedCoefficientMatrix_eq_zero_of_summand_ne k)

end TauCeti.E6DoubledMinuscule
