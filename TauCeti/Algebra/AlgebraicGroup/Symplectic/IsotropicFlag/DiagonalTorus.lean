/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.ClosedImmersion

/-!
# The diagonal torus in the symplectic isotropic flag subgroup

The standard diagonal torus of `Sp₂ₘ` factors through the standard complete isotropic
flag subgroup over every commutative ring. The factored coordinate restriction is
surjective, so the torus inclusion is a closed immersion. Its composite with the flag
subgroup inclusion recovers the ambient symplectic torus, and its algebra-valued points
are the same diagonal symplectic matrices.

The factorization follows
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.DiagonalTorus`, using
`CommHopfAlgCat.liftQuotient` and `Symplectic.diagonalTorusCoordinateMap`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6 (symplectic groups and isotropic flags).
* B. Conrad, *Reductive Group Schemes* (2014), §5.1 (pinnings).
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.Symplectic.IsotropicFlag

open GLSymplecticFin.IsotropicFlag

universe u w

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The diagonal symplectic torus lies in the standard isotropic flag subgroup.
The order of defining ideals reverses the inclusion of closed subgroups. -/
theorem definingHopfIdeal_le_diagonalTorusDefiningIdeal :
    definingHopfIdeal R m ≤ Symplectic.diagonalTorusDefiningIdeal R m := by
  rw [← HopfIdeal.toIdeal_le_toIdeal, definingHopfIdeal_toIdeal, Ideal.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, j, hij, rfl⟩ :=
    (GeneralLinear.mem_weightParabolicRelationSet_iff R (weights m) x).mp hx
  rw [weights_lt_weights_iff] at hij
  rw [SetLike.mem_coe, HopfIdeal.mem_toIdeal, Symplectic.mem_diagonalTorusDefiningIdeal]
  exact Symplectic.coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _
    (fun h ↦ hij.ne (congrArg (flagOrder m) h).symm)

/-- Restriction from the isotropic flag subgroup to its diagonal symplectic torus. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R m ⟶
      (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin m)))).obj :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R m)
    (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m)) (by
      intro x hx
      apply RingHom.mem_ker.mpr
      exact (Symplectic.mem_diagonalTorusDefiningIdeal R m x).mp
        (definingHopfIdeal_le_diagonalTorusDefiningIdeal R m hx))

/-- The factored torus restriction recovers the original restriction from the symplectic group. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_diagonalTorusCoordinateMap :
    coordinateMap R m ≫ diagonalTorusCoordinateMap R m =
      Symplectic.diagonalTorusCoordinateMap (R := R) (m := m) :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The torus restriction from the isotropic flag subgroup is surjective. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap R m).hom :=
  CommHopfAlgCat.liftQuotient_surjective_of_surjective _ _ _
    Symplectic.diagonalTorusCoordinateMap_surjective

/-- The standard diagonal torus as a morphism into the isotropic flag subgroup scheme. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin m)) ⟶ groupScheme R m :=
  eqToHom (DiagonalizableGroup.groupScheme_def R
    (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫
      (hopfSpec (CommRingCat.of R)).map (diagonalTorusCoordinateMap R m).op

/-- Inclusion of the factored diagonal torus recovers the ambient symplectic diagonal torus. -/
@[reassoc (attr := simp)]
theorem diagonalTorus_comp_inclusion :
    diagonalTorus R m ≫ inclusion R m = Symplectic.diagonalTorus (R := R) (m := m) := by
  have hcomp := CommHopfAlgCat.hopfSpec_map_comp_quotientSpecι
    (definingHopfIdeal R m) (diagonalTorusCoordinateMap R m)
  rw [coordinateMap_comp_diagonalTorusCoordinateMap] at hcomp
  simpa only [diagonalTorus, inclusion, Symplectic.diagonalTorus_def,
    eqToHom_refl, Category.comp_id, Category.assoc] using congrArg
    (fun g ↦ eqToHom (DiagonalizableGroup.groupScheme_def R
      (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫ g) hcomp

/-- The standard diagonal torus is a closed subgroup scheme of the isotropic flag subgroup. -/
instance isClosedImmersion_diagonalTorus :
    IsClosedImmersion (diagonalTorus R m).hom.hom.left := by
  rw [diagonalTorus]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (DiagonalizableGroup.groupScheme_def R
      (SplitTorus.characterGroup (ULift.{u} (Fin m)))) _).mpr
    (diagonalTorusCoordinateMap_surjective R m)

/-- The factored torus map gives the same symplectic diagonal matrix as the ambient torus map. -/
@[simp]
theorem pointsMulEquiv_diagonalTorusCoordinateMap {A : Type w} [CommRing A] [Algebra R A]
    (f : WithConv
      (MonoidAlgebra R (SplitTorus.characterGroup (ULift.{u} (Fin m))) →ₐ[R] A)) :
    (pointsMulEquiv R m (A := A)
        (toConv (f.ofConv.comp (diagonalTorusCoordinateMap R m).hom)) : GLSymplecticFin m A) =
      Symplectic.pointsMulEquiv R m (A := A) (Symplectic.diagonalTorusPoints f) := by
  have hquot := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal R m) (diagonalTorusCoordinateMap R m)
    (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m))
    (coordinateMap_comp_diagonalTorusCoordinateMap R m) (CommAlgCat.of R A) f
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply (diagonalTorusCoordinateMap R m)
    (CommAlgCat.of R A) f] at hquot
  rw [← pointsMulEquiv_coe, ← hquot, Symplectic.mapPointsFunctor_diagonalTorusCoordinateMap_app]

end TauCeti.Symplectic.IsotropicFlag
