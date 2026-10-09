/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.StandardComodule

/-!
# The standard comodule of the generated type-Bₙ₊₁ spin subgroup

The subgroup of `GL_(2^(n+1))` generated directly over a commutative ring by the numbered
type-`Bₙ₊₁` spin root subgroups and weight torus has a faithful standard comodule, its spin
representation. Over any field this comodule is simple: the weight torus separates the `2^(n+1)`
distinct spin weight lines, and the simple-root matrices connect them along the single Weyl orbit
of spin weights.

This subgroup is not identified with the specialization of the integral spin carrier, which
contains it. The two comodules share their weight decomposition and root matrices, so the
simplicity criterion `TauCeti.TypeBSpinCarrier.isSimpleOrder_of_spinWeights_of_rootSubgroupPoints`
applies to both without repeating the weight-orbit argument.

## Main declarations

* `TauCeti.TypeBSpinCarrier.generatedWeightTorusCoordinateMap`: the weight torus factored through
  the generated subgroup.
* `TauCeti.TypeBSpinCarrier.generatedStandardComodule`: the standard comodule of the generated
  subgroup on `R^(2^(n+1))`.

## Main results

* `TauCeti.TypeBSpinCarrier.isFaithful_generatedStandardComodule`: the standard comodule is
  faithful over every commutative ring.
* `TauCeti.TypeBSpinCarrier.generatedRootSubgroupPoints_mulVec_mem`: its subcomodules are stable
  under every numbered simple-root matrix.
* `TauCeti.TypeBSpinCarrier.generatedTorusCorestrict_eq_ofWeights`: restricted to the weight
  torus, it is the direct sum of the spin weight lines.
* `TauCeti.TypeBSpinCarrier.instIsSimpleOrderGeneratedSubcomodule`: it is simple over every field.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The construction follows the generated type-`E₆` minuscule subgroup in
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.StandardComodule`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.TypeBSpinCarrier

universe u v

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The weight torus factored through the subgroup generated over `R`. -/
noncomputable def generatedWeightTorusCoordinateMap :
    generatedCoordinateHopfAlgebra n R ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin (n + 1)))).obj :=
  generatedCoordinateLift n R (.inr ())

/-- The generated subgroup's weight torus recovers the ambient spin weight torus. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap :
    generatedCoordinateMap n R ≫ generatedWeightTorusCoordinateMap n R =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ R (basisWeight n) := by
  rw [generatedWeightTorusCoordinateMap, generatedCoordinateMap_comp_generatedCoordinateLift,
    generatorCoordinateMap_inr]

/-- A point induced by a generated root-subgroup lift maps to the numbered spin root matrix with
the same parameter, over every value algebra. -/
theorem pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints
    (j : Fin (n + 1) ⊕ Fin (n + 1)) {B : Type v} [CommRing B] [Algebra R B]
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
      (CommAlgCat.of R B)) :
    GeneralLinear.pointToGeneralLinear (dimension n)
        (AlgHom.mapDomain (generatedCoordinateMap n R).hom
          (toConv (q.ofConv.comp (generatedCoordinateLift n R (.inl j)).hom.toAlgHom))) =
      (rootSubgroupPoints n j B (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) B) := by
  -- Both generator families are the same transported root-subgroup map out of `O(GL)`.
  have hcomp : generatedCoordinateMap n R ≫ generatedCoordinateLift n R (.inl j) =
      coordinateMap n R ≫ rootSubgroupToBaseChangeCoordinateMap n R j := by
    rw [generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inl]
    exact (coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap n R j).symm
  have hpoint : AlgHom.mapDomain (generatedCoordinateMap n R).hom
      (toConv (q.ofConv.comp (generatedCoordinateLift n R (.inl j)).hom.toAlgHom)) =
      AlgHom.mapDomain (coordinateMap n R).hom
        (toConv (q.ofConv.comp (rootSubgroupToBaseChangeCoordinateMap n R j).hom.toAlgHom)) := by
    apply WithConv.ext
    ext x
    exact congrArg (fun f ↦ q.ofConv (f.hom x)) hcomp
  have hcarrier := mapPointsFunctor_coordinateMap_app n R
    ((CommHopfAlgCat.mapPointsFunctor (rootSubgroupToBaseChangeCoordinateMap n R j)).app _ q)
  have hmatrix := coe_baseChangePointsMulEquiv_apply n R (CommAlgCat.of R B)
    ((CommHopfAlgCat.mapPointsFunctor (rootSubgroupToBaseChangeCoordinateMap n R j)).app _ q)
  rw [baseChangePointsMulEquiv_mapPointsFunctor_rootSubgroupToBaseChangeCoordinateMap,
    ← hcarrier, CommHopfAlgCat.mapPointsFunctor_app_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply] at hmatrix
  rw [hpoint, hmatrix, GeneralLinear.pointsMulEquiv_apply, AlgHom.mapDomain_apply]

/-- The standard right comodule of the generated type-`Bₙ₊₁` spin subgroup on `R^(2^(n+1))`. -/
@[instance_reducible]
noncomputable def generatedStandardComodule :
    Comodule R (generatedCoordinateHopfAlgebra n R) (Fin (dimension n) → R) :=
  GeneralLinear.corestrictStandardComodule R (dimension n) (generatedCoordinateMap n R).hom

attribute [local instance] generatedStandardComodule

/-- The standard comodule of the generated type-`Bₙ₊₁` spin subgroup is faithful over every
commutative ring. -/
theorem isFaithful_generatedStandardComodule :
    Comodule.IsFaithful (k := R) (H := generatedCoordinateHopfAlgebra n R)
      (V := Fin (dimension n) → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R (dimension n)
    (generatedCoordinateMap n R).hom (generatedCoordinateMap_surjective n R)

/-- A subcomodule of the generated subgroup's standard comodule is stable under each numbered
positive and negative simple-root matrix, with any parameter. -/
theorem generatedRootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (generatedCoordinateHopfAlgebra n R) (Fin (dimension n) → R))
    (j : Fin (n + 1) ⊕ Fin (n + 1)) (t : Multiplicative R) {w : Fin (dimension n) → R}
    (hw : w ∈ N) :
    ((rootSubgroupPoints n j R t : Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ w ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R (dimension n)
    (generatedCoordinateMap n R).hom N
    (toConv (q.ofConv.comp (generatedCoordinateLift n R (.inl j)).hom.toAlgHom)) hw
  rw [pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints n R j q,
    MulEquiv.apply_symm_apply] at h
  exact h

/-- Restriction of the generated subgroup's standard comodule to the weight torus is the direct
sum of the distinct spin weight lines. -/
theorem generatedTorusCorestrict_eq_ofWeights :
    Comodule.Corestrict (generatedWeightTorusCoordinateMap n R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin (dimension n))) (basisCharacter n) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (generatedCoordinateMap n R).hom (generatedWeightTorusCoordinateMap n R).hom (basisWeight n)
  rw [← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- The standard comodule of the generated type-`Bₙ₊₁` spin subgroup is simple over every field,
including characteristic two. -/
instance instIsSimpleOrderGeneratedSubcomodule (k : Type u) [Field k] :
    let _ := generatedStandardComodule n k
    IsSimpleOrder (Subcomodule k (generatedCoordinateHopfAlgebra n k) (Fin (dimension n) → k)) :=
  isSimpleOrder_of_spinWeights_of_rootSubgroupPoints n k
    (generatedWeightTorusCoordinateMap n k).hom.toCoalgHom
    (generatedTorusCorestrict_eq_ofWeights n k)
    fun N j _ hw ↦ generatedRootSubgroupPoints_mulVec_mem n k N j (Multiplicative.ofAdd 1) hw

end TauCeti.TypeBSpinCarrier
