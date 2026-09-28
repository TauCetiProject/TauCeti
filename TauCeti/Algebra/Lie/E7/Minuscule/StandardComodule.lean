/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Lie.E7.Minuscule.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.Lie.E7.Minuscule.PointsFunctor

/-!
# The standard representation of the type-E7 minuscule carrier

The full-weight type-`E₇` minuscule carrier is a closed subgroup of `GL₅₆`.  After base
change to a commutative ring `R`, its standard representation is therefore the corestriction of
the standard `O(GL₅₆)`-comodule along the quotient coordinate morphism.

This file proves that the resulting representation is faithful over every commutative ring and
simple over every field.  For simplicity, restriction to the rank-seven weight torus separates a
nonzero invariant vector into its one-dimensional weight components.  The positive and negative
simple-root elements then move a coordinate vector across the connected minuscule weight graph.

## Main declarations

* `TauCeti.E7Minuscule.standardComodule`: its standard comodule on `R⁵⁶`.
* `TauCeti.E7Minuscule.isFaithful_standardComodule`: faithfulness of the standard comodule.
* `TauCeti.E7Minuscule.specializedPointsMulEquiv`: specialized coordinate-algebra points are
  identified with concrete carrier points.
* `TauCeti.E7Minuscule.points_mulVec_mem`: invariant submodules are stable under concrete carrier
  points.
* `TauCeti.E7Minuscule.instIsSimpleOrderSubcomodule`: simplicity over a field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.

The corestriction and point-action interface follows
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule` and is adapted from
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule`; the specialized point
identification uses `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.BaseChange`.
-/

public section

open CategoryTheory Module WithConv
open scoped Matrix TensorProduct

namespace TauCeti.E7Minuscule

universe u

variable (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized type-`E₇` minuscule carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R) (Fin 56 → R) :=
  let _ := GeneralLinear.standardComodule R 56
  Comodule.Corestrict (coordinateMap R).hom.toCoalgHom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard carrier coaction is the standard general-linear coaction followed by the
quotient coordinate morphism. -/
@[simp]
theorem standardComodule_coact :
    let _ := GeneralLinear.standardComodule R 56
    Comodule.corestrictCoact
        (R := R) (C := GeneralLinear.coordinateHopfAlgebra R 56)
        (D := coordinateHopfAlgebra R) (M := Fin 56 → R)
        (coordinateMap R).hom.toCoalgHom =
      TensorProduct.map LinearMap.id
          (coordinateMap R).hom.toCoalgHom.toLinearMap ∘ₗ
        GeneralLinear.standardCoact R 56 := by
  apply LinearMap.ext
  intro v
  rw [Comodule.corestrictCoact_apply, LinearMap.comp_apply,
    GeneralLinear.standardComodule_coact]

/-- **The standard comodule of the specialized type-`E₇` minuscule carrier is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R) (V := Fin 56 → R) := by
  exact Comodule.isFaithful_corestrict_of_surjective (coordinateMap R).hom
    (coordinateMap_surjective R)
    (GeneralLinear.isFaithful_standardComodule R 56)

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under scalar extension, a carrier-valued point acts on the standard comodule by the matrix
obtained from its ambient `GL₅₆` point. -/
theorem piScalarRight_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin 56)).toLinearMap.comp
        (Comodule.endOfPoint (Fin 56 → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin
          (GeneralLinear.pointToGeneralLinear 56
            (CommHopfAlgCat.quotientPointsHom
              (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
              (CommAlgCat.of R A) g)) :
          (Fin 56 → A) →ₗ[A] Fin 56 → A).comp
        (TensorProduct.piScalarRight R A A (Fin 56)).toLinearMap := by
  rw [Comodule.endOfPoint_corestrict]
  have hpoint :
      g.ofConv.comp ((coordinateMap R).hom :
        GeneralLinear.coordinateHopfAlgebra R 56 →ₐ[R] coordinateHopfAlgebra R) =
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R A) g).ofConv := by
    exact congrArg WithConv.ofConv (mapPointsFunctor_coordinateMap_app R g)
  rw [hpoint]
  exact GeneralLinear.piScalarRight_comp_endOfPoint R 56 _

end PointAction

/-- **A subcomodule of the standard carrier comodule is stable under every carrier-valued
point.** -/
theorem mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 56 → R))
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] R)) {w : Fin 56 → R} (hw : w ∈ N) :
    (GeneralLinear.pointToGeneralLinear 56
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R R) g) : Matrix (Fin 56) (Fin 56) R) *ᵥ w ∈ N := by
  have h := Comodule.basePointsRepresentation_mem N g hw
  rw [Comodule.basePointsRepresentation_corestrict (coordinateMap R).hom g,
    GeneralLinear.basePointsRepresentation_eq_mulVec] at h
  have hpoint :
      AlgHom.mapDomain (coordinateMap R).hom g =
        CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R R) g := by
    exact mapPointsFunctor_coordinateMap_app R g
  rw [hpoint] at h
  exact h

/-- Base-valued points of the specialized coordinate algebra, identified with points of the
integral minuscule carrier after base change. -/
noncomputable def specializedPointsMulEquiv :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) (CommAlgCat.of R R) ≃*
      points R :=
  (CommHopfAlgCat.baseChangeIsoPointsMulEquiv (baseChangeCoordinateIso R)
      (CommAlgCat.of R R)).trans
    (pointsPresentation
      (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ R) (CommAlgCat.of R R))).mulEquiv

/-- Under the specialized point equivalence, the quotient point is represented by the carrier
point's ambient general-linear matrix. -/
theorem quotientPointsHom_specializedPointsMulEquiv_symm (g : points R) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
        (CommAlgCat.of R R) ((specializedPointsMulEquiv R).symm g) =
      (GeneralLinear.pointsMulEquiv (R := R) 56).symm
        (g : Matrix.GeneralLinearGroup (Fin 56) R) := by
  have h :
      ((specializedPointsMulEquiv R)
          ((specializedPointsMulEquiv R).symm g) : Matrix.GeneralLinearGroup (Fin 56) R) =
        GeneralLinear.pointsMulEquiv 56
          (CommHopfAlgCat.quotientPointsHom
            (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
            (CommAlgCat.of R R) ((specializedPointsMulEquiv R).symm g)) := by
    rw [specializedPointsMulEquiv, MulEquiv.trans_apply,
    GeneralLinear.IntegralPointsPresentation.coe_mulEquiv_apply]
    exact GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
      56 definingIdeal (baseChangeDefiningIdeal R) (baseChangeCoordinateIso R)
      (mkQuotient_comp_baseChangeCoordinateIso_hom R) (CommAlgCat.of R R) _
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

/-- A subcomodule of the standard carrier comodule is stable under every concrete carrier
point. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 56 → R))
    (g : points R) {w : Fin 56 → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) *ᵥ w ∈ N := by
  have h := mulVec_mem R N ((specializedPointsMulEquiv R).symm g) hw
  rw [quotientPointsHom_specializedPointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

/-! ## Simplicity over a field -/

section Simple

variable (k : Type u) [Field k]

private theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k))
    (i : Fin 7 ⊕ Fin 7) {w : Fin 56 → k} (hw : w ∈ N) :
    ((rootSubgroupPoints i k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 56) k) : Matrix (Fin 56) (Fin 56) k) *ᵥ w ∈ N := by
  exact points_mulVec_mem k N (rootSubgroupPoints i k (Multiplicative.ofAdd 1)) hw

/-- The character of the weight torus corresponding to a minuscule-basis index. -/
private noncomputable abbrev minusculeCharacter (a : Fin 56) :
    Multiplicative (Fin 7 →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (DynkinType.e7MinusculeWeight a))

private theorem torusCorestrict_eq_ofWeights :
    let _ := standardComodule k
    Comodule.Corestrict (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun k (Fin 56)) minusculeCharacter := by
  let _ := GeneralLinear.standardComodule k 56
  let _ := standardComodule k
  apply Comodule.ext
  rw [Comodule.corestrict_coact,
    ← Comodule.corestrictCoact_comp (coordinateMap k).hom.toCoalgHom
      (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom]
  have hcomp :
      _root_.CoalgHom.comp ((weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom)
          ((coordinateMap k).hom.toCoalgHom) =
        (GeneralLinear.weightTorusCoordinateBialgHom (S := k)
          DynkinType.e7MinusculeWeight).toCoalgHom := by
    have hb :
        (weightTorusToBaseChangeCoordinateMap k).hom.comp (coordinateMap k).hom =
          GeneralLinear.weightTorusCoordinateBialgHom (S := k)
            DynkinType.e7MinusculeWeight := by
      rw [← _root_.CommHopfAlgCat.hom_comp,
        coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
        GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    apply DFunLike.ext _ _
    intro x
    exact DFunLike.congr_fun hb x
  rw [hcomp]
  simpa only [Comodule.corestrict_coact] using
    congrArg (fun c : Comodule k _ (Fin 56 → k) ↦ c.coact)
      (GeneralLinear.corestrict_standardComodule_weightTorusCoordinateBialgHom_eq_ofWeights
        DynkinType.e7MinusculeWeight)

private theorem minusculeCharacter_injective : Function.Injective minusculeCharacter := by
  intro a b h
  apply DynkinType.e7MinusculeWeight_injective
  apply Finsupp.equivFunOnFinite.symm.injective
  exact Multiplicative.ofAdd.injective h

private theorem positiveRoot_mulVec_single_sub (i : Fin 7) (a : Fin 56)
    (ha : DynkinType.e7MinusculeWeight a i = -1) :
    (((rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 56) k) : Matrix (Fin 56) (Fin 56) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      Pi.single (DynkinType.e7MinusculeReflection i a) 1 := by
  rw [coe_rootSubgroupPoints_inl, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  simp only [toAdd_ofAdd, one_smul]
  have hmatrix : raisingMatrix i = weightTable.raisingMatrix i := by
    ext b c
    simp
  rw [hmatrix]
  rw [Matrix.mulVec_single_one, weightTable.raisingMatrix_map_col]
  simp only [weightTable_weight, weightTable_reflection, ha, ite_true, add_sub_cancel_left]

private theorem negativeRoot_mulVec_single_sub (i : Fin 7) (a : Fin 56)
    (ha : DynkinType.e7MinusculeWeight a i = 1) :
    (((rootSubgroupPoints (.inr i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 56) k) : Matrix (Fin 56) (Fin 56) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      Pi.single (DynkinType.e7MinusculeReflection i a) 1 := by
  rw [coe_rootSubgroupPoints_inr, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  simp only [toAdd_ofAdd, one_smul]
  have hmatrix : loweringMatrix i = weightTable.loweringMatrix i := by
    ext b c
    simp
  rw [hmatrix]
  rw [Matrix.mulVec_single_one, weightTable.loweringMatrix_map_col]
  simp only [weightTable_weight, weightTable_reflection, ha, ite_true, add_sub_cancel_left]

/-- Invariance under the two simple-root points makes membership of coordinate basis vectors
stable under every simple reflection. -/
private theorem single_reflection_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k))
    (a : Fin 56) (i : Fin 7) (ha : Pi.single a 1 ∈ N) :
    Pi.single (DynkinType.e7MinusculeReflection i a) 1 ∈ N := by
  rcases DynkinType.e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with
    hneg | hzero | hpos
  · have hact := rootSubgroupPoints_mulVec_mem k N (.inl i) ha
    have hsub := N.toSubmodule.sub_mem hact ha
    rwa [positiveRoot_mulVec_single_sub k i a hneg] at hsub
  · rw [(DynkinType.e7MinusculeReflection_eq_self_iff i a).2 hzero]
    exact ha
  · have hact := rootSubgroupPoints_mulVec_mem k N (.inr i) ha
    have hsub := N.toSubmodule.sub_mem hact ha
    rwa [negativeRoot_mulVec_single_sub k i a hpos] at hsub

/-- **The standard comodule of the specialized type-`E₇` minuscule carrier is simple over
every field.** -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k)) := by
  exact Subcomodule.isSimpleOrder_of_corestrict_eq_ofWeights
    (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom minusculeCharacter
    minusculeCharacter_injective (torusCorestrict_eq_ofWeights k)
    (fun i a ↦ DynkinType.e7MinusculeReflection i a)
    (fun i ↦ DynkinType.e7MinusculeReflection_apply_apply i)
    (fun N a i ↦ single_reflection_mem k N a i) 0
    DynkinType.exists_e7MinusculeReflections_eq

end Simple

end TauCeti.E7Minuscule
