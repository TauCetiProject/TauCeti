/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Levi
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# The standard representation of the type-D spin carrier and its half-spin summands

The full-weight type-`Dₙ` spin carrier is a closed subgroup of `GL_(2^n)`. After base change to a
commutative ring `R`, its standard representation is therefore the corestriction of the standard
general-linear comodule along the quotient coordinate morphism; it is the spin representation
`S = S⁺ ⊕ S⁻` of the carrier, on the coordinates indexed by sign sets.

This file proves that this representation is faithful over every commutative ring, and that its
two half-spin summands are subcomodules over every commutative ring: the coordinates whose sign
sets have even cardinality span `S⁺`, those of odd cardinality span `S⁻`, and the two are
complementary. The input is that the carrier preserves the half-spin decomposition
scheme-theoretically, `TauCeti.TypeDSpinCarrier.coordinateMap_X_eq_zero`.

## Main declarations

* `TauCeti.TypeDSpinCarrier.standardComodule`: the standard comodule on `R^(2^n)`.
* `TauCeti.TypeDSpinCarrier.isFaithful_standardComodule`: faithfulness of the standard comodule.
* `TauCeti.TypeDSpinCarrier.coefficientMatrix_basisFun`: its matrix coefficients.
* `TauCeti.TypeDSpinCarrier.points_mulVec_mem`: stability of subcomodules under carrier points.
* `TauCeti.TypeDSpinCarrier.torusCorestrict_eq_ofWeights`: restriction to the distinct spin
  weight lines of the weight torus.
* `TauCeti.TypeDSpinCarrier.halfSpinSubcomodule`: the half-spin summand of a given parity, as a
  subcomodule.
* `TauCeti.TypeDSpinCarrier.mem_halfSpinSubcomodule`: its vectors are those supported on sign
  sets of that parity.
* `TauCeti.TypeDSpinCarrier.isCompl_halfSpinSubcomodule_toSubmodule`: the two half-spin
  summands are complementary.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, §20.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The corestriction and faithfulness arguments follow the type-`B` spin carrier in
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.StandardComodule`, and the summand subcomodules
follow those of the tripled type-`D₄` carrier in
`TauCeti.Algebra.Lie.D4.Tripled.StandardComodule`.
-/

public section

open CategoryTheory
open scoped Matrix

namespace TauCeti.TypeDSpinCarrier

universe u

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized type-`Dₙ` spin carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R) :=
  GeneralLinear.corestrictStandardComodule R (dimension n) (coordinateMap n hn R).hom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- **The standard comodule of the specialized type-`Dₙ` spin carrier is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra n hn R)
      (V := Fin (dimension n) → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R (dimension n)
    (coordinateMap n hn R).hom (coordinateMap_surjective n hn R)

/-- The standard coefficient matrix is the image of the ambient matrix coordinates in the
carrier coordinate algebra. -/
theorem coefficientMatrix_basisFun (a b : Fin (dimension n)) :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra n hn R)
        (Pi.basisFun R (Fin (dimension n))) a b =
      (coordinateMap n hn R).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (dimension n)
        (GeneralLinear.coordinateRingMap R (dimension n) (MvPolynomial.X (a, b)))) := by
  rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
    GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
    GeneralLinear.genericMatrix_apply]

/-- A subcomodule of the standard spin representation is stable under every concrete carrier
point, over any commutative ring. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R))
    (g : points n hn R) {w : Fin (dimension n) → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ w ∈ N := by
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R (dimension n)
    (coordinateMap n hn R).hom N ((baseChangePointsMulEquiv n hn R (CommAlgCat.of R R)).symm g) hw
  have hpoint : AlgHom.mapDomain (coordinateMap n hn R).hom
      ((baseChangePointsMulEquiv n hn R (CommAlgCat.of R R)).symm g) = _ :=
    mapPointsFunctor_coordinateMap_app n hn R _
  rw [hpoint, quotientPointsHom_baseChangePointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

/-! ## The weight torus -/

/-- The character of the spin weight torus attached to a coordinate basis vector. -/
noncomputable abbrev basisCharacter (a : Fin (dimension n)) :
    Multiplicative (Fin n →₀ ℤ) :=
  SplitTorus.weightCharacter (basisWeight n a)

/-- Distinct spin-basis indices define distinct characters, including between the two
half-spin summands. -/
theorem basisCharacter_injective : Function.Injective (basisCharacter n) := by
  intro a b h
  have hw : basisWeight n a = basisWeight n b := by
    funext i
    simpa only [basisCharacter, SplitTorus.toAdd_weightCharacter] using
      congrArg (fun χ : Multiplicative (Fin n →₀ ℤ) ↦ Multiplicative.toAdd χ i) h
  exact (Fintype.equivFin (Finset (Fin n))).symm.injective
    (DynkinType.typeDSpinWeight_injective hw)

/-- Restriction of the standard spin comodule to the weight torus is the direct sum of the
spin character lines. This equality holds over every commutative ring. -/
theorem torusCorestrict_eq_ofWeights :
    let _ := standardComodule n hn R
    Comodule.Corestrict (weightTorusToBaseChangeCoordinateMap n hn R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin (dimension n))) (basisCharacter n) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (coordinateMap n hn R).hom (weightTorusToBaseChangeCoordinateMap n hn R).hom
    (basisWeight n)
  rw [← _root_.CommHopfAlgCat.hom_comp,
    coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-! ## The half-spin subcomodules -/

/-- **The half-spin summand of parity `j` is a subcomodule of the standard carrier comodule**, over
every commutative ring. It is spanned by the coordinate vectors whose sign sets have cardinality
of parity `j`: `S⁺` for `j = 0` and `S⁻` for `j = 1`. -/
noncomputable def halfSpinSubcomodule (j : ZMod 2) :
    Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R) :=
  (Pi.basisFun R (Fin (dimension n))).coordinateSpanSubcomodule
    {a | ((signSet n a).card : ZMod 2) = j} <|
    ((Pi.basisFun R (Fin (dimension n))).coordinateSpanIsStable_iff
      (C := coordinateHopfAlgebra n hn R) _).2 <| by
    intro a ha b hb
    rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
      GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
      GeneralLinear.genericMatrix_apply]
    exact coordinateMap_X_eq_zero n hn R fun h ↦
      ha (((basisParity_eq_basisParity_iff n).1 h).trans hb)

/-- A half-spin subcomodule is the span of the coordinate vectors of its parity. -/
@[simp]
theorem halfSpinSubcomodule_toSubmodule (j : ZMod 2) :
    (halfSpinSubcomodule n hn R j).toSubmodule =
      Submodule.span R ((Pi.basisFun R (Fin (dimension n))) ''
        {a | ((signSet n a).card : ZMod 2) = j}) :=
  Module.Basis.coordinateSpanSubcomodule_toSubmodule _ _ _

/-- Membership in a half-spin subcomodule means vanishing at every sign set of the other
parity. -/
@[simp]
theorem mem_halfSpinSubcomodule (j : ZMod 2) (v : Fin (dimension n) → R) :
    v ∈ halfSpinSubcomodule n hn R j ↔ ∀ a, ((signSet n a).card : ZMod 2) ≠ j → v a = 0 := by
  classical
  rw [← Subcomodule.mem_toSubmodule, halfSpinSubcomodule_toSubmodule,
    (Pi.basisFun R (Fin (dimension n))).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr,
    Set.mem_ofPred_eq]
  exact forall_congr' fun a ↦ not_imp_comm

/-- **The two half-spin subcomodules are complementary**: the standard carrier comodule is the
direct sum `S⁺ ⊕ S⁻` of its even and odd half-spin summands. -/
theorem isCompl_halfSpinSubcomodule_toSubmodule :
    IsCompl (halfSpinSubcomodule n hn R 0).toSubmodule
      (halfSpinSubcomodule n hn R 1).toSubmodule := by
  have hodd : {a : Fin (dimension n) | ((signSet n a).card : ZMod 2) = 1} =
      {a | ((signSet n a).card : ZMod 2) = 0}ᶜ := by
    ext a
    simpa only [Set.mem_ofPred_eq, Set.mem_compl_iff] using
      (by decide : ∀ c : ZMod 2, c = 1 ↔ ¬c = 0) _
  rw [halfSpinSubcomodule_toSubmodule, halfSpinSubcomodule_toSubmodule, hodd]
  exact (Pi.basisFun R (Fin (dimension n))).linearIndependent.isCompl_span_image
    (Pi.basisFun R (Fin (dimension n))).span_eq isCompl_compl

end TauCeti.TypeDSpinCarrier
