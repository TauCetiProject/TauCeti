/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Connected
public import TauCeti.Algebra.Lie.D4.Tripled.StandardComodule
import TauCeti.Algebra.Lie.D4.Tripled.Levi

/-!
# The tripled representation of the generated type-D₄ subgroup

The subgroup of `GL₂₄` generated over a commutative ring by the eight numbered root subgroups
and weight torus has a faithful standard comodule. Over every field it is completely reducible:
the twenty-four distinct torus characters extract coordinate lines, and the numbered root
matrices connect all lines in each of the three eight-dimensional summands. Matrix coefficients
do not mix summands, so the missing summands provide an invariant complement.

This concerns the subgroup generated over the coefficient ring, not the specialization of the
integral toral closure. No identification between those subgroup schemes or with a pinned
simply connected group is asserted.

## Main results

* `TauCeti.D4Tripled.isFaithful_generatedStandardComodule`: faithfulness over every ring.
* `TauCeti.D4Tripled.isCompletelyReducible_generatedStandardComodule`: complete reducibility
  over every field, including characteristic two.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.

The quotient-comodule and generator-lift construction follows
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.StandardComodule`. The weight-graph
argument is shared with `TauCeti.Algebra.Lie.D4.Tripled.StandardComodule`.
-/

public section

open CategoryTheory WithConv
open TauCeti.DynkinType
open scoped Matrix

namespace TauCeti.D4Tripled

universe u v

variable (R : Type u) [CommRing R]

/-- The weight torus factored through the subgroup generated over the coefficient ring. -/
noncomputable def generatedWeightTorusCoordinateMap :
    generatedCoordinateHopfAlgebra R ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 4))).obj :=
  generatedCoordinateLift R (.inr ())

/-- The generated subgroup's weight torus recovers the ambient tripled weight torus. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap :
    generatedCoordinateMap R ≫ generatedWeightTorusCoordinateMap R =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ R d4TripledWeight := by
  rw [generatedWeightTorusCoordinateMap, generatedCoordinateMap_comp_generatedCoordinateLift,
    generatorCoordinateMap_inr]

/-- A point induced by a generated root-subgroup lift maps to the numbered tripled root matrix
with the same parameter. -/
@[simp↓]
theorem pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    (i : Fin 4 ⊕ Fin 4) (B : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) B) :
    GeneralLinear.pointToGeneralLinear 24
        (AlgHom.mapDomain (generatedCoordinateMap R).hom
          (no_index (toConv (q.ofConv.comp
            (generatedCoordinateLift R (.inl i)).hom.toAlgHom)))) =
      (rootSubgroupPoints i B (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 24) B) := by
  have hcomp : generatedCoordinateMap R ≫ generatedCoordinateLift R (.inl i) =
      coordinateMap R ≫ rootSubgroupToBaseChangeCoordinateMap R i := by
    rw [generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inl]
    exact (coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap R i).symm
  have hpoint : AlgHom.mapDomain (generatedCoordinateMap R).hom
      (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl i)).hom.toAlgHom)) =
      AlgHom.mapDomain (coordinateMap R).hom
        (toConv (q.ofConv.comp (rootSubgroupToBaseChangeCoordinateMap R i).hom.toAlgHom)) := by
    apply WithConv.ext
    ext x
    exact congrArg (fun f ↦ q.ofConv (f.hom x)) hcomp
  rw [hpoint]
  have h := congrArg (fun g : points B ↦
    (g : Matrix.GeneralLinearGroup (Fin 24) B))
    (baseChangePointsMulEquiv_mapPointsFunctor_rootSubgroupToBaseChangeCoordinateMap R B i q)
  have hcoe := coe_baseChangePointsMulEquiv_apply R B
    ((CommHopfAlgCat.mapPointsFunctor (rootSubgroupToBaseChangeCoordinateMap R i)).app B q)
  rw [hcoe] at h
  -- The functor component uses an indexed presentation of the same algebra-valued points.
  erw [← mapPointsFunctor_coordinateMap_app, GeneralLinear.pointsMulEquiv_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  exact h

/-- The standard right comodule of the generated tripled type-D₄ subgroup. -/
@[instance_reducible]
noncomputable def generatedStandardComodule :
    Comodule R (generatedCoordinateHopfAlgebra R) (Fin 24 → R) :=
  GeneralLinear.corestrictStandardComodule R 24 (generatedCoordinateMap R).hom

attribute [local instance] GeneralLinear.standardComodule generatedStandardComodule

/-- The standard comodule of the generated tripled subgroup is faithful over every ring. -/
theorem isFaithful_generatedStandardComodule :
    Comodule.IsFaithful (k := R) (H := generatedCoordinateHopfAlgebra R) (V := Fin 24 → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R 24
    (generatedCoordinateMap R).hom (generatedCoordinateMap_surjective R)

/-- Subcomodules of the generated subgroup's standard comodule are stable under the numbered
positive and negative tripled root matrices. -/
theorem generatedRootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (generatedCoordinateHopfAlgebra R) (Fin 24 → R))
    (i : Fin 4 ⊕ Fin 4) (t : Multiplicative R) {w : Fin 24 → R} (hw : w ∈ N) :
    ((rootSubgroupPoints i R t : Matrix.GeneralLinearGroup (Fin 24) R) :
      Matrix (Fin 24) (Fin 24) R) *ᵥ w ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R 24
    (generatedCoordinateMap R).hom N
    (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl i)).hom.toAlgHom)) hw
  rw [pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    R i (CommAlgCat.of R R) q, MulEquiv.apply_symm_apply] at h
  exact h

/-- Restriction to the generated weight torus is the direct sum of the distinct tripled
character lines. -/
theorem generatedTorusCorestrict_eq_ofWeights :
    Comodule.Corestrict (generatedWeightTorusCoordinateMap R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 24)) tripledCharacter := by
  have hchar : (fun a ↦ SplitTorus.weightCharacter (d4TripledWeight a)) = tripledCharacter := by
    funext a
    apply Multiplicative.toAdd.injective
    ext j
    simp [tripledCharacter]
  rw [← hchar]
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (generatedCoordinateMap R).hom (generatedWeightTorusCoordinateMap R).hom d4TripledWeight
  rw [← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- The standard matrix coefficients of the generated subgroup do not mix its three summands. -/
theorem generatedCoefficientMatrix_eq_zero_of_summand_ne (a b : Fin 24)
    (hab : d4TripledSummand a ≠ d4TripledSummand b) :
    Comodule.coefficientMatrix (C := generatedCoordinateHopfAlgebra R)
      (Pi.basisFun R (Fin 24)) a b = 0 := by
  rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
    GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
    GeneralLinear.genericMatrix_apply]
  apply RingHom.mem_ker.mp
  rw [generatedCoordinateMap_ker]
  apply baseChangeDefiningIdeal_le_generatedDefiningIdeal R
  have h := RingHom.mem_ker.mpr (coordinateMap_X_eq_zero R hab)
  rw [coordinateMap_ker] at h
  exact h

/-- The faithful tripled comodule of the generated subgroup is completely reducible over every
field, including characteristic two. -/
theorem isCompletelyReducible_generatedStandardComodule (k : Type u) [Field k] :
    let _ := generatedStandardComodule k
    Comodule.IsCompletelyReducible k (generatedCoordinateHopfAlgebra k) (Fin 24 → k) :=
  isCompletelyReducible_of_tripledWeights_of_rootSubgroupPoints k
    (generatedWeightTorusCoordinateMap k).hom.toCoalgHom
    (generatedTorusCorestrict_eq_ofWeights k)
    (fun N i _ hw ↦ generatedRootSubgroupPoints_mulVec_mem k N i (Multiplicative.ofAdd 1) hw)
    (generatedCoefficientMatrix_eq_zero_of_summand_ne k)

end TauCeti.D4Tripled
