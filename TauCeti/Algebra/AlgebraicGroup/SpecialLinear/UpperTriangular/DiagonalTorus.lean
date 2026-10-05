/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Over
import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion

/-!
# The diagonal torus in the special-linear Borel

The standard rank-`r` diagonal torus of `SL_{r+1}` factors through the upper-triangular
subgroup scheme over every commutative ring. The factored coordinate morphism is surjective,
so the resulting morphism `T → B` is a closed immersion. Its composite with `B → SL_{r+1}`
recovers the standard torus, and its algebra-valued points are the same diagonal matrices
in fundamental-weight coordinates.

This gives the represented containment of the chosen torus in the chosen Borel used in a
standard type-A pinning. The existing Hopf-ideal containment
`SpecialLinear.UpperTriangular.definingHopfIdeal_le_splitMaximalTorus_definingIdeal`
supplies the factorization, including over nonreduced base rings.

The construction uses `CommHopfAlgCat.liftQuotient` and
`SpecialLinear.diagonalTorusCoordinateMap`. Its general-linear analogue is
`GeneralLinear.UpperTriangular.diagonalTorusCoordinateMap`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1 (pinnings).
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.SpecialLinear.UpperTriangular

universe u v

variable (r : ℕ) (R : Type u) [CommRing R]

/-- Restriction from the special-linear upper-triangular coordinate algebra to its standard
diagonal torus, in fundamental-weight coordinates. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R (r + 1) ⟶
      (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R (r + 1))
    (SpecialLinear.diagonalTorusCoordinateMap r R)
    (by
      intro x hx
      apply RingHom.mem_ker.mpr
      have hle := definingHopfIdeal_le_splitMaximalTorus_definingIdeal R r
      rw [SpecialLinear.splitMaximalTorus_definingIdeal] at hle
      exact (SpecialLinear.mem_diagonalTorusDefiningIdeal r R x).mp (hle hx))

/-- The factored coordinate map recovers restriction from `SL_{r+1}` to its diagonal torus. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_diagonalTorusCoordinateMap :
    coordinateMap R (r + 1) ≫ diagonalTorusCoordinateMap r R =
      SpecialLinear.diagonalTorusCoordinateMap r R :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The torus-coordinate restriction from the Borel is surjective over every base ring. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap r R).hom :=
  CommHopfAlgCat.liftQuotient_surjective_of_surjective _ _ _
    (SpecialLinear.diagonalTorusCoordinateMap_surjective r R)

/-- Under the upper-triangular point equivalence, the factored torus map gives the same
special-linear diagonal matrix as the ambient torus map. -/
@[simp]
theorem pointsMulEquiv_diagonalTorusCoordinateMap {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv
      (MonoidAlgebra R (SplitTorus.characterGroup (ULift.{u} (Fin r))) →ₐ[R] A)) :
    (pointsMulEquiv R (r + 1) (A := A)
        (toConv (f.ofConv.comp (diagonalTorusCoordinateMap r R).hom)) :
        Matrix.SpecialLinearGroup (Fin (r + 1)) A) =
      SpecialLinear.pointsMulEquiv (R := R) (A := A) (r + 1)
        (SpecialLinear.diagonalTorusPoints r R A f) := by
  have hquot := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal R (r + 1)) (diagonalTorusCoordinateMap r R)
    (SpecialLinear.diagonalTorusCoordinateMap r R)
    (coordinateMap_comp_diagonalTorusCoordinateMap r R) (CommAlgCat.of R A) f
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply (diagonalTorusCoordinateMap r R)
    (CommAlgCat.of R A) f] at hquot
  rw [← pointsMulEquiv_coe, ← hquot, SpecialLinear.diagonalTorusPoints_apply]

/-- The standard diagonal torus as a morphism into the represented special-linear
upper-triangular subgroup. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin r)) ⟶
      CommHopfAlgCat.quotientSpec (SpecialLinear.coordinateHopfAlgebra R (r + 1))
        (definingHopfIdeal R (r + 1)) :=
  eqToHom (DiagonalizableGroup.groupScheme_def R
    (SplitTorus.characterGroup (ULift.{u} (Fin r)))) ≫
      (hopfSpec (CommRingCat.of R)).map (diagonalTorusCoordinateMap r R).op

/-- Inclusion of the factored torus into `SL_{r+1}` recovers the spectrum of the standard
diagonal-torus coordinate morphism. -/
@[reassoc (attr := simp)]
theorem diagonalTorus_comp_quotientSpecι :
    diagonalTorus r R ≫
        CommHopfAlgCat.quotientSpecι (SpecialLinear.coordinateHopfAlgebra R (r + 1))
          (definingHopfIdeal R (r + 1)) =
      eqToHom (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))) ≫
          (hopfSpec (CommRingCat.of R)).map (SpecialLinear.diagonalTorusCoordinateMap r R).op := by
  have hcomp := CommHopfAlgCat.hopfSpec_map_comp_quotientSpecι
    (definingHopfIdeal R (r + 1)) (diagonalTorusCoordinateMap r R)
  rw [coordinateMap_comp_diagonalTorusCoordinateMap] at hcomp
  simpa only [diagonalTorus, Category.assoc] using congrArg
    (fun g ↦ eqToHom (DiagonalizableGroup.groupScheme_def R
      (SplitTorus.characterGroup (ULift.{u} (Fin r)))) ≫ g) hcomp

/-- The standard torus is a closed subgroup scheme of the special-linear Borel. -/
instance isClosedImmersion_diagonalTorus :
    IsClosedImmersion (diagonalTorus r R).hom.hom.left := by
  rw [diagonalTorus]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (DiagonalizableGroup.groupScheme_def R
      (SplitTorus.characterGroup (ULift.{u} (Fin r)))) _).mpr
    (diagonalTorusCoordinateMap_surjective r R)

end TauCeti.SpecialLinear.UpperTriangular
