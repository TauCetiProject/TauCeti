/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Basic
public import TauCeti.Algebra.Lie.E7.Minuscule.StandardComodule

/-!
# The standard comodule of the generated type-E₇ minuscule subgroup

The subgroup of `GL₅₆` generated directly over a commutative ring by the fourteen numbered
minuscule root subgroups and the weight torus has a faithful standard comodule. Over any field
this comodule is simple: the torus separates the 56 weight lines, and the root matrices connect
them along the minuscule weight graph.

This subgroup is not identified here with the specialization of the integral minuscule carrier.
The two comodules share their weight decomposition and root matrices, so the simplicity criterion
`TauCeti.E7Minuscule.isSimpleOrder_of_minusculeWeights_of_rootSubgroupPoints` applies to both
without repeating the weight-graph argument.

## Main declarations

* `TauCeti.E7Minuscule.generatedWeightTorusCoordinateMap`: the weight torus factored through the
  generated subgroup.
* `TauCeti.E7Minuscule.generatedStandardComodule`: the standard comodule on `R⁵⁶`.
* `TauCeti.E7Minuscule.isFaithful_generatedStandardComodule`: faithfulness over every
  commutative ring.
* `TauCeti.E7Minuscule.generatedRootSubgroupPoints_mulVec_mem`: subcomodules are stable under
  the numbered root-subgroup matrices.
* `TauCeti.E7Minuscule.generatedTorusCorestrict_eq_ofWeights`: the weight decomposition under
  the weight torus.
* `TauCeti.E7Minuscule.instIsSimpleOrderGeneratedSubcomodule`: simplicity over every field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The construction is adapted from the generated type-`E₆` minuscule subgroup in
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.StandardComodule`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.E7Minuscule

universe u v

variable (R : Type u) [CommRing R]

/-- The weight torus factored through the subgroup generated over `R`. -/
noncomputable def generatedWeightTorusCoordinateMap :
    generatedCoordinateHopfAlgebra R ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 7))).obj :=
  generatedCoordinateLift R (.inr ())

/-- The generated subgroup's weight torus recovers the ambient minuscule weight torus. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap :
    generatedCoordinateMap R ≫ generatedWeightTorusCoordinateMap R =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ R DynkinType.e7MinusculeWeight := by
  rw [generatedWeightTorusCoordinateMap, generatedCoordinateMap_comp_generatedCoordinateLift,
    generatorCoordinateMap_inr]

/-- A point induced by a generated root-subgroup lift maps to the numbered minuscule root matrix
with the same parameter, over every value algebra. -/
-- Avoid indexing the lift's dependent codomain; rewrite before `mapDomain_apply` unfolds.
@[simp↓]
theorem pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    (i : Fin 7 ⊕ Fin 7) (B : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) B) :
    GeneralLinear.pointToGeneralLinear 56
        (AlgHom.mapDomain (generatedCoordinateMap R).hom
          (no_index (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl i)).hom.toAlgHom)))) =
      (rootSubgroupPoints i B (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 56) B) := by
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
  rw [hpoint,
    pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints]

/-- The standard right comodule of the generated type-`E₇` minuscule subgroup on `R⁵⁶`. -/
@[instance_reducible]
noncomputable def generatedStandardComodule :
    Comodule R (generatedCoordinateHopfAlgebra R) (Fin 56 → R) :=
  GeneralLinear.corestrictStandardComodule R 56 (generatedCoordinateMap R).hom

attribute [local instance] generatedStandardComodule

/-- **The standard comodule of the generated type-`E₇` minuscule subgroup is faithful over every
commutative ring.** -/
theorem isFaithful_generatedStandardComodule :
    Comodule.IsFaithful (k := R) (H := generatedCoordinateHopfAlgebra R) (V := Fin 56 → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R 56 (generatedCoordinateMap R).hom
    (generatedCoordinateMap_surjective R)

/-- A subcomodule of the generated subgroup's standard comodule is stable under each numbered
positive and negative root-subgroup matrix, with any parameter. -/
theorem generatedRootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (generatedCoordinateHopfAlgebra R) (Fin 56 → R))
    (i : Fin 7 ⊕ Fin 7) (t : Multiplicative R) {w : Fin 56 → R} (hw : w ∈ N) :
    ((rootSubgroupPoints i R t : Matrix.GeneralLinearGroup (Fin 56) R) :
      Matrix (Fin 56) (Fin 56) R) *ᵥ w ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R 56
    (generatedCoordinateMap R).hom N
    (toConv (q.ofConv.comp (generatedCoordinateLift R (.inl i)).hom.toAlgHom)) hw
  rw [pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints R i
    (CommAlgCat.of R R) q, MulEquiv.apply_symm_apply] at h
  exact h

/-- **Restricting the generated subgroup's standard comodule to the weight torus gives the direct
sum of the 56 minuscule weight lines.** -/
theorem generatedTorusCorestrict_eq_ofWeights :
    Comodule.Corestrict (generatedWeightTorusCoordinateMap R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 56)) minusculeCharacter := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (generatedCoordinateMap R).hom (generatedWeightTorusCoordinateMap R).hom
    DynkinType.e7MinusculeWeight
  rw [← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- **The standard comodule of the generated type-`E₇` minuscule subgroup is simple over every
field**, including characteristics two and three. -/
instance instIsSimpleOrderGeneratedSubcomodule (k : Type u) [Field k] :
    let _ := generatedStandardComodule k
    IsSimpleOrder (Subcomodule k (generatedCoordinateHopfAlgebra k) (Fin 56 → k)) :=
  isSimpleOrder_of_minusculeWeights_of_rootSubgroupPoints k
    (generatedWeightTorusCoordinateMap k).hom.toCoalgHom
    (generatedTorusCorestrict_eq_ofWeights k)
    (fun N i _ hw ↦ generatedRootSubgroupPoints_mulVec_mem k N i (Multiplicative.ofAdd 1) hw)

end TauCeti.E7Minuscule
