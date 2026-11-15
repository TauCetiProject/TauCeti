/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.DiagonalTorus

/-!
# A chosen split maximal torus of the symplectic group over a ring

The paired diagonal torus is a chosen split maximal torus of `Sp₂ₘ` over every commutative
ring. The parametrization uses the coordinate characters `eᵢ`, so the resulting datum has
rank `m`. Maximality is checked on each geometric fiber using the fieldwise diagonal-torus
theorem and the base-change comparison of its defining ideal.

The choice commutes with arbitrary base change and lies in the standard complete isotropic
flag subgroup. These are the torus data used to construct the standard symplectic pinning.
The construction follows the special-linear torus assembly in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Over` and reuses
`Symplectic.isMaximalTorus_diagonalTorusDefiningIdeal`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.2.1 and Example 3.2.3.
* J. S. Milne, *Algebraic Groups* (2017), §24.6.
-/

public section

open CategoryTheory

namespace TauCeti.Symplectic

universe u

variable (R : Type u) [CommRing R]

/-- The paired diagonal torus as a chosen rank-`m` split maximal torus of `Sp₂ₘ` over a
commutative base ring. -/
noncomputable def splitMaximalTorus (m : ℕ) :
    SplitMaximalTorus R (coordinateHopfAlgebra R m) m where
  coordinateMap := diagonalTorusCoordinateMap
  surjective := diagonalTorusCoordinateMap_surjective
  maximal := by
    intro k _ _ _
    have hker : HopfIdeal.kerOfSurjective
        (diagonalTorusCoordinateMap (R := R) (m := m)).hom
        diagonalTorusCoordinateMap_surjective = diagonalTorusDefiningIdeal R m := by
      ext x
      rw [HopfIdeal.mem_kerOfSurjective, mem_diagonalTorusDefiningIdeal]
    rw [hker]
    let e : FiniteTypeCommHopfAlgCat.of k
        (CommHopfAlgCat.baseChange (K := k) (coordinateHopfAlgebra R m)) ≅
        FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k m) :=
      ObjectProperty.isoMk _ (coordinateHopfAlgebraBaseChangeIso R k m)
    have hmax := (isMaximalTorus_diagonalTorusDefiningIdeal k m).comapOfIso e
    rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal R m k] at hmax
    simp only [e, ObjectProperty.isoMk_hom, FiniteTypeCommHopfAlgCat.toBialgHom,
      ObjectProperty.homMk_hom] at hmax
    rw [HopfIdeal.comapOfSurjective_map_of_bijective _ _
      (ConcreteCategory.bijective_of_isIso
        (coordinateHopfAlgebraBaseChangeIso R k m).hom)] at hmax
    exact hmax

/-- The chosen torus uses restriction to the standard paired diagonal coordinates. -/
@[simp]
theorem splitMaximalTorus_coordinateMap (m : ℕ) :
    (splitMaximalTorus R m).coordinateMap = diagonalTorusCoordinateMap := (rfl)

/-- The chosen torus is cut out by the diagonal-torus defining ideal. -/
@[simp]
theorem splitMaximalTorus_definingIdeal (m : ℕ) :
    (splitMaximalTorus R m).definingIdeal = diagonalTorusDefiningIdeal R m := by
  ext x
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap,
    mem_diagonalTorusDefiningIdeal]

/-- Base-changing the chosen symplectic torus and transporting it to the symplectic group
constructed over the new base recovers its chosen torus, including the parametrization. -/
theorem splitMaximalTorus_baseChange_comapOfIso (S : Type u) [CommRing S] [Algebra R S]
    (m : ℕ) :
    ((splitMaximalTorus R m).baseChange S).comapOfIso
        (coordinateHopfAlgebraBaseChangeIso R S m).symm = splitMaximalTorus S m := by
  ext1
  rw [SplitMaximalTorus.comapOfIso_coordinateMap, SplitMaximalTorus.baseChange_coordinateMap,
    splitMaximalTorus_coordinateMap, splitMaximalTorus_coordinateMap, Iso.symm_hom]
  exact diagonalTorusCoordinateMap_baseChange R S

/-- The chosen split maximal torus lies in the standard complete isotropic flag subgroup.
The order of defining Hopf ideals reverses inclusion of closed subgroups. -/
theorem IsotropicFlag.definingHopfIdeal_le_splitMaximalTorus_definingIdeal (m : ℕ) :
    IsotropicFlag.definingHopfIdeal R m ≤ (splitMaximalTorus R m).definingIdeal := by
  rw [splitMaximalTorus_definingIdeal]
  exact IsotropicFlag.definingHopfIdeal_le_diagonalTorusDefiningIdeal R m

end TauCeti.Symplectic
