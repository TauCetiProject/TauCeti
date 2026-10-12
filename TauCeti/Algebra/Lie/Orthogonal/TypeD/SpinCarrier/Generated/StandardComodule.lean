/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.CompletelyReducible

/-!
# The full spin representation of the generated type-D subgroup

The subgroup of `GL_(2^n)` generated over a commutative ring by the numbered type-D root
subgroups and weight torus has a faithful standard comodule. Over every field it is completely
reducible: distinct torus characters extract coordinate lines, and the root matrices connect
all lines of each half-spin parity. Its matrix coefficients do not mix the two parities.

This concerns the subgroup generated over the coefficient ring, not the specialization of the
integral toral closure. No identification between those subgroup schemes is asserted.

## Main results

* `TauCeti.TypeDSpinCarrier.isFaithful_generatedStandardComodule`: faithfulness over every ring.
* `TauCeti.TypeDSpinCarrier.isCompletelyReducible_generatedStandardComodule`: complete
  reducibility over every field, including characteristic two.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The quotient-comodule and generator-lift construction follows
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.StandardComodule`. The weight-graph argument is
shared with `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.CompletelyReducible`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.TypeDSpinCarrier

universe u v

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

/-- The weight torus factored through the subgroup generated over the coefficient ring. -/
noncomputable def generatedWeightTorusCoordinateMap :
    generatedCoordinateHopfAlgebra n hn R ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin n))).obj :=
  generatedCoordinateLift n hn R (.inr ())

/-- The generated subgroup's weight torus recovers the ambient spin weight torus. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap :
    generatedCoordinateMap n hn R ≫ generatedWeightTorusCoordinateMap n hn R =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ R (basisWeight n) := by
  rw [generatedWeightTorusCoordinateMap, generatedCoordinateMap_comp_generatedCoordinateLift,
    generatorCoordinateMap_inr]

/-- A point induced by a generated root-subgroup lift maps to the numbered spin root matrix
with the same parameter. -/
@[simp↓]
theorem pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    (i : Fin n ⊕ Fin n) (B : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) B) :
    GeneralLinear.pointToGeneralLinear (dimension n)
        (AlgHom.mapDomain (generatedCoordinateMap n hn R).hom
          (no_index (toConv (q.ofConv.comp
            (generatedCoordinateLift n hn R (.inl i)).hom.toAlgHom)))) =
      (rootSubgroupPoints n hn i B (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) B) := by
  have hcomp : generatedCoordinateMap n hn R ≫ generatedCoordinateLift n hn R (.inl i) =
      coordinateMap n hn R ≫ rootSubgroupToBaseChangeCoordinateMap n hn R i := by
    rw [generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inl]
    exact (coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap n hn R i).symm
  have hpoint : AlgHom.mapDomain (generatedCoordinateMap n hn R).hom
      (toConv (q.ofConv.comp (generatedCoordinateLift n hn R (.inl i)).hom.toAlgHom)) =
      AlgHom.mapDomain (coordinateMap n hn R).hom
        (toConv (q.ofConv.comp (rootSubgroupToBaseChangeCoordinateMap n hn R i).hom.toAlgHom)) := by
    apply WithConv.ext
    ext x
    exact congrArg (fun f ↦ q.ofConv (f.hom x)) hcomp
  rw [hpoint]
  have h := congrArg (fun g : points n hn B ↦
    (g : Matrix.GeneralLinearGroup (Fin (dimension n)) B))
    (baseChangePointsMulEquiv_mapPointsFunctor_rootSubgroupToBaseChangeCoordinateMap
      n hn R B i q)
  have hcoe := coe_baseChangePointsMulEquiv_apply n hn R B
    ((CommHopfAlgCat.mapPointsFunctor
      (rootSubgroupToBaseChangeCoordinateMap n hn R i)).app B q)
  rw [hcoe] at h
  -- The functor component uses an indexed presentation of the same algebra-valued points.
  erw [← mapPointsFunctor_coordinateMap_app, GeneralLinear.pointsMulEquiv_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  exact h

/-- The standard right comodule of the generated full-weight type-D spin subgroup. -/
@[instance_reducible]
noncomputable def generatedStandardComodule :
    Comodule R (generatedCoordinateHopfAlgebra n hn R) (Fin (dimension n) → R) :=
  GeneralLinear.corestrictStandardComodule R (dimension n) (generatedCoordinateMap n hn R).hom

attribute [local instance] GeneralLinear.standardComodule generatedStandardComodule

/-- The standard comodule of the generated spin subgroup is faithful over every commutative
ring. -/
theorem isFaithful_generatedStandardComodule :
    Comodule.IsFaithful (k := R) (H := generatedCoordinateHopfAlgebra n hn R)
      (V := Fin (dimension n) → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R (dimension n)
    (generatedCoordinateMap n hn R).hom (generatedCoordinateMap_surjective n hn R)

/-- Subcomodules of the generated subgroup's standard comodule are stable under the numbered
positive and negative spin root matrices. -/
theorem generatedRootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (generatedCoordinateHopfAlgebra n hn R) (Fin (dimension n) → R))
    (i : Fin n ⊕ Fin n) (t : Multiplicative R) {w : Fin (dimension n) → R} (hw : w ∈ N) :
    ((rootSubgroupPoints n hn i R t : Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ w ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R (dimension n)
    (generatedCoordinateMap n hn R).hom N
    (toConv (q.ofConv.comp (generatedCoordinateLift n hn R (.inl i)).hom.toAlgHom)) hw
  rw [pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    n hn R i (CommAlgCat.of R R) q, MulEquiv.apply_symm_apply] at h
  exact h

/-- Restriction to the generated weight torus is the direct sum of the distinct spin character
lines. -/
theorem generatedTorusCorestrict_eq_ofWeights :
    Comodule.Corestrict (generatedWeightTorusCoordinateMap n hn R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin (dimension n))) (basisCharacter n) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (generatedCoordinateMap n hn R).hom (generatedWeightTorusCoordinateMap n hn R).hom
    (basisWeight n)
  rw [← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- The standard matrix coefficients of the generated subgroup do not mix half-spin parity.
-/
theorem generatedCoefficientMatrix_eq_zero_of_parity_ne (a b : Fin (dimension n))
    (hab : basisParity n a ≠ basisParity n b) :
    Comodule.coefficientMatrix (C := generatedCoordinateHopfAlgebra n hn R)
      (Pi.basisFun R (Fin (dimension n))) a b = 0 := by
  rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
    GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
    GeneralLinear.genericMatrix_apply]
  apply RingHom.mem_ker.mp
  rw [generatedCoordinateMap_ker]
  apply baseChangeDefiningIdeal_le_generatedDefiningIdeal n hn R
  have h := RingHom.mem_ker.mpr (coordinateMap_X_eq_zero n hn R hab)
  rw [coordinateMap_ker] at h
  exact h

/-- The faithful full spin comodule of the generated subgroup is completely reducible over every
field, including characteristic two. -/
theorem isCompletelyReducible_generatedStandardComodule (k : Type u) [Field k] :
    let _ := generatedStandardComodule n hn k
    Comodule.IsCompletelyReducible k (generatedCoordinateHopfAlgebra n hn k)
      (Fin (dimension n) → k) :=
  isCompletelyReducible_of_spinWeights_of_rootSubgroupPoints n hn k
    (generatedWeightTorusCoordinateMap n hn k).hom.toCoalgHom
    (generatedTorusCorestrict_eq_ofWeights n hn k)
    (fun N i _ hw ↦ generatedRootSubgroupPoints_mulVec_mem n hn k N i
      (Multiplicative.ofAdd 1) hw)
    (generatedCoefficientMatrix_eq_zero_of_parity_ne n hn k)

end TauCeti.TypeDSpinCarrier
