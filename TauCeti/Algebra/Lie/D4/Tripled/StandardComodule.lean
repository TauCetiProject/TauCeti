/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Lie.D4.Tripled.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# The standard representation of the tripled type-D4 carrier

The tripled type-`D₄` carrier is a closed subgroup of `GL₂₄`, constructed from the direct sum
of the vector and two half-spin eight-dimensional representations. After base change to a
commutative ring `R`, its standard representation is the corestriction of the standard
`O(GL₂₄)`-comodule along the quotient coordinate morphism.

This file proves that the resulting representation is faithful over every commutative ring. It
also identifies the action of an algebra-valued point with multiplication by its ambient
`24 × 24` matrix and deduces that subcomodules are stable under the concrete carrier points.
No irreducibility assertion is made: the tripled representation is designed to have three
eight-dimensional constituents.

## Main declarations

* `TauCeti.D4Tripled.standardComodule`: the standard comodule on `R²⁴`.
* `TauCeti.D4Tripled.isFaithful_standardComodule`: faithfulness of the standard comodule.
* `TauCeti.D4Tripled.piScalarRight_comp_endOfPoint`: algebra-valued points act through their
  ambient matrices.
* `TauCeti.D4Tripled.points_mulVec_mem`: invariant submodules are stable under concrete carrier
  points.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.

The corestriction and point-action interface follows
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule`; the organization is adapted from
`TauCeti.Algebra.Lie.E7.Minuscule.StandardComodule`.
-/

public section

open CategoryTheory Module WithConv
open scoped Matrix TensorProduct

namespace TauCeti.D4Tripled

universe u

variable (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized tripled type-`D₄` carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R) (Fin 24 → R) :=
  let _ := GeneralLinear.standardComodule R 24
  Comodule.Corestrict (coordinateMap R).hom.toCoalgHom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- **The standard comodule of the specialized tripled type-`D₄` carrier is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R) (V := Fin 24 → R) := by
  exact Comodule.isFaithful_corestrict_of_surjective (coordinateMap R).hom
    (coordinateMap_surjective R)
    (GeneralLinear.isFaithful_standardComodule R 24)

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under scalar extension, a carrier-valued point acts on the standard comodule by the matrix
obtained from its ambient `GL₂₄` point. -/
theorem piScalarRight_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin 24)).toLinearMap.comp
        (Comodule.endOfPoint (Fin 24 → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin
          (GeneralLinear.pointToGeneralLinear 24
            (CommHopfAlgCat.quotientPointsHom
              (GeneralLinear.coordinateHopfAlgebra R 24) (baseChangeDefiningIdeal R)
              (CommAlgCat.of R A) g)) :
          (Fin 24 → A) →ₗ[A] Fin 24 → A).comp
        (TensorProduct.piScalarRight R A A (Fin 24)).toLinearMap := by
  rw [Comodule.endOfPoint_corestrict]
  have hpoint :
      g.ofConv.comp ((coordinateMap R).hom :
        GeneralLinear.coordinateHopfAlgebra R 24 →ₐ[R] coordinateHopfAlgebra R) =
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 24) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R A) g).ofConv := by
    exact congrArg WithConv.ofConv (mapPointsFunctor_coordinateMap_app R g)
  rw [hpoint]
  exact GeneralLinear.piScalarRight_comp_endOfPoint R 24 _

end PointAction

/-- A subcomodule of the standard carrier comodule is stable under every coordinate-algebra
point over the base ring. -/
theorem mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 24 → R))
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] R)) {w : Fin 24 → R} (hw : w ∈ N) :
    (GeneralLinear.pointToGeneralLinear 24
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 24) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R R) g) : Matrix (Fin 24) (Fin 24) R) *ᵥ w ∈ N := by
  have h := Comodule.basePointsRepresentation_mem N g hw
  rw [Comodule.basePointsRepresentation_corestrict (coordinateMap R).hom g,
    GeneralLinear.basePointsRepresentation_eq_mulVec] at h
  have hpoint :
      AlgHom.mapDomain (coordinateMap R).hom g =
        CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 24) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R R) g := by
    exact mapPointsFunctor_coordinateMap_app R g
  rw [hpoint] at h
  exact h

/-- A subcomodule of the standard carrier comodule is stable under every concrete tripled
type-`D₄` carrier point. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 24 → R))
    (g : points R) {w : Fin 24 → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin 24) R) : Matrix (Fin 24) (Fin 24) R) *ᵥ w ∈ N := by
  have h := mulVec_mem R N
    ((baseChangePointsMulEquiv R (CommAlgCat.of R R)).symm g) hw
  rw [quotientPointsHom_baseChangePointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

end TauCeti.D4Tripled
