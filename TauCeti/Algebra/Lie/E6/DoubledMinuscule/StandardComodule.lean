/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Levi
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor

/-!
# The two minuscule subcomodules of the doubled E₆ carrier

The standard representation of the doubled minuscule carrier is the corestriction of the
standard `O(GL₅₄)`-comodule along its quotient coordinate morphism. It is faithful over every
commutative ring. Its two coordinate blocks `V(ϖ₁)` and `V(ϖ₆)` are complementary subcomodules:
the carrier preserves them scheme-theoretically, so this decomposition persists after arbitrary
base change.

The parameter `dual = false` selects the first block, and `dual = true` the contragredient block.
Membership means vanishing outside the selected block. Restriction to the weight torus
identifies the fifty-four weight lines, and subcomodules are stable under concrete carrier points.
These two constituents provide the block decomposition used to prove complete reducibility
over fields in `TauCeti.Algebra.Lie.E6.DoubledMinuscule.CompletelyReducible`.

The carrier has not been identified with the pinned simply connected group scheme of type `E₆`.
Transfer of these representations to that pinned group requires such an identification.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.1–2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* The corestriction interface follows `TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule`;
  the presented point identification follows the same module;
  the coordinate subcomodules follow `TauCeti.Algebra.Lie.D4.Tripled.StandardComodule`.
-/

public section

open CategoryTheory Module WithConv
open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

universe u

variable (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized doubled type-`E₆` minuscule carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R) (Fin 54 → R) :=
  GeneralLinear.corestrictStandardComodule R 54 (coordinateMap R).hom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard representation of the doubled minuscule carrier is faithful over every
commutative ring. -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R) (V := Fin 54 → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R 54
    (coordinateMap R).hom (coordinateMap_surjective R)

/-- The coefficient matrix of the standard comodule consists of the ambient matrix coordinates
mapped to the carrier's coordinate algebra. This explicit rewrite also applies when the comodule
instance's body is hidden by the module boundary. -/
theorem coefficientMatrix_basisFun (a b : Fin 54) :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra R) (Pi.basisFun R (Fin 54)) a b =
      (coordinateMap R).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv R 54
        (GeneralLinear.coordinateRingMap R 54 (MvPolynomial.X (a, b)))) := by
  rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
    GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
    GeneralLinear.genericMatrix_apply]

/-- The minuscule (`dual = false`) or contragredient minuscule (`dual = true`) block as a
subcomodule of the standard carrier comodule. -/
noncomputable def summandSubcomodule (dual : Bool) :
    Subcomodule R (coordinateHopfAlgebra R) (Fin 54 → R) :=
  (Pi.basisFun R (Fin 54)).coordinateSpanSubcomodule
    {a | matrixSummand a = if dual then 1 else 0} <|
    ((Pi.basisFun R (Fin 54)).coordinateSpanIsStable_iff
      (C := coordinateHopfAlgebra R) _).2 <| by
    intro a ha b hb
    have hab : matrixSummand a ≠ matrixSummand b := fun h ↦ ha (h.trans hb)
    rw [coefficientMatrix_basisFun]
    exact coordinateMap_X_eq_zero R hab

/-- Each summand subcomodule is the span of the corresponding coordinate basis vectors. -/
@[simp]
theorem summandSubcomodule_toSubmodule (dual : Bool) :
    (summandSubcomodule R dual).toSubmodule =
      Submodule.span R ((Pi.basisFun R (Fin 54)) ''
        {a | matrixSummand a = if dual then 1 else 0}) :=
  Module.Basis.coordinateSpanSubcomodule_toSubmodule _ _ _

/-- Membership in a minuscule summand means vanishing outside its coordinate block. -/
@[simp]
theorem mem_summandSubcomodule (dual : Bool) (v : Fin 54 → R) :
    v ∈ summandSubcomodule R dual ↔
      ∀ a, matrixSummand a ≠ (if dual then 1 else 0) → v a = 0 := by
  classical
  rw [← Subcomodule.mem_toSubmodule, summandSubcomodule_toSubmodule,
    (Pi.basisFun R (Fin 54)).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr,
    Set.mem_ofPred_eq]
  exact forall_congr' fun a ↦ not_imp_comm

/-- The two minuscule summands are complementary over every commutative ring. -/
theorem isCompl_summandSubcomodule :
    IsCompl (summandSubcomodule R false).toSubmodule
      (summandSubcomodule R true).toSubmodule := by
  classical
  have hset : {a : Fin 54 | matrixSummand a = 1} = {a | matrixSummand a = 0}ᶜ := by
    ext a
    obtain ⟨b, rfl⟩ := matrixIndexEquiv.surjective a
    cases b <;> simp
  rw [summandSubcomodule_toSubmodule, summandSubcomodule_toSubmodule]
  simp only [Bool.false_eq_true, ↓reduceIte, hset]
  exact (Pi.basisFun R (Fin 54)).linearIndependent.isCompl_span_image
    (Pi.basisFun R (Fin 54)).span_eq isCompl_compl

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
@[simp]
theorem quotientPointsHom_specializedPointsMulEquiv_symm (g : points R) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R 54) (baseChangeDefiningIdeal R)
        (CommAlgCat.of R R) ((specializedPointsMulEquiv R).symm g) =
      (GeneralLinear.pointsMulEquiv (R := R) 54).symm
        (g : Matrix.GeneralLinearGroup (Fin 54) R) := by
  have h :
      ((specializedPointsMulEquiv R)
          ((specializedPointsMulEquiv R).symm g) : Matrix.GeneralLinearGroup (Fin 54) R) =
        GeneralLinear.pointsMulEquiv 54
          (CommHopfAlgCat.quotientPointsHom
            (GeneralLinear.coordinateHopfAlgebra R 54) (baseChangeDefiningIdeal R)
            (CommAlgCat.of R R) ((specializedPointsMulEquiv R).symm g)) := by
    rw [specializedPointsMulEquiv, MulEquiv.trans_apply,
      GeneralLinear.IntegralPointsPresentation.coe_mulEquiv_apply]
    exact GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
      54 definingIdeal (baseChangeDefiningIdeal R) (baseChangeCoordinateIso R)
      (mkQuotient_comp_baseChangeCoordinateIso_hom R) (CommAlgCat.of R R) _
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

/-- A subcomodule of the standard carrier comodule is stable under every concrete carrier
point. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 54 → R))
    (g : points R) {w : Fin 54 → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin 54) R) : Matrix (Fin 54) (Fin 54) R) *ᵥ w ∈ N := by
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R 54
    (coordinateMap R).hom N ((specializedPointsMulEquiv R).symm g) hw
  have hpoint : AlgHom.mapDomain (coordinateMap R).hom
      ((specializedPointsMulEquiv R).symm g) = _ :=
    mapPointsFunctor_coordinateMap_app R _
  rw [hpoint] at h
  rw [quotientPointsHom_specializedPointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

/-- The weight-torus character of a doubled minuscule coordinate. -/
noncomputable abbrev minusculeCharacter (a : Fin 54) : Multiplicative (Fin 6 →₀ ℤ) :=
  SplitTorus.weightCharacter (matrixWeight a)

/-- Restriction of the standard comodule to the weight torus gives its fifty-four weight lines,
over every commutative ring. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict (weightTorusToBaseChangeCoordinateMap R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin 54)) minusculeCharacter := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (coordinateMap R).hom (weightTorusToBaseChangeCoordinateMap R).hom matrixWeight
  rw [← _root_.CommHopfAlgCat.hom_comp,
    coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

end TauCeti.E6DoubledMinuscule
