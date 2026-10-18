/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.DiagonalTorus

/-!
# The standard torus and Borel of the general linear group over a ring

The diagonal matrices give a chosen split maximal torus of `GLₙ` over every commutative
ring. It has rank `n`, is maximal on every geometric fiber, and lies in the
upper-triangular Borel subgroup over the base. Both subgroups commute with arbitrary
base change. These are the torus and Borel data used to pin the general linear group;
no choice of simple-root vectors is included here.

The construction uses the surjective diagonal coordinate map, the field-valued maximality
in `GeneralLinear.DiagonalTorus.Maximal`, and the Borel recognition in
`GeneralLinear.UpperTriangular.Borel`. Its organization follows the special-linear
construction in `SpecialLinear.Reductive.Over`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definitions 3.2.1 and 5.2.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable (R : Type u) [CommRing R]

/-- The diagonal torus is a chosen rank-`n` split maximal torus of `GLₙ` over any
commutative ring, maximal on every geometric fiber. -/
noncomputable def splitMaximalTorus (n : ℕ) :
    SplitMaximalTorus R (coordinateHopfAlgebra R n) n where
  coordinateMap := diagonalTorusCoordinateMap (R := R) (N := n)
  surjective := diagonalTorusCoordinateMap_surjective R n
  maximal := by
    intro k _ _ _
    let e : FiniteTypeCommHopfAlgCat.of k
        (CommHopfAlgCat.baseChange (K := k) (coordinateHopfAlgebra R n)) ≅
        FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n) :=
      ObjectProperty.isoMk _ (coordinateHopfAlgebraBaseChangeIso R k n)
    have hmax := (isMaximalTorus_diagonalTorusDefiningIdeal k n).comapOfIso e
    rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal R n k] at hmax
    simp only [e, ObjectProperty.isoMk_hom, FiniteTypeCommHopfAlgCat.toBialgHom,
      ObjectProperty.homMk_hom] at hmax
    rw [HopfIdeal.comapOfSurjective_map_of_bijective _ _
      (ConcreteCategory.bijective_of_isIso (coordinateHopfAlgebraBaseChangeIso R k n).hom)]
      at hmax
    rwa [diagonalTorusDefiningIdeal_eq_ker] at hmax

/-- Restriction to the chosen torus is the standard diagonal coordinate morphism. -/
@[simp]
theorem splitMaximalTorus_coordinateMap (n : ℕ) :
    (splitMaximalTorus R n).coordinateMap = diagonalTorusCoordinateMap (R := R) (N := n) :=
  (rfl)

/-- The chosen torus is cut out by the diagonal-torus defining ideal. -/
@[simp]
theorem splitMaximalTorus_definingIdeal (n : ℕ) :
    (splitMaximalTorus R n).definingIdeal = diagonalTorusDefiningIdeal R n := by
  ext x
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap,
    mem_diagonalTorusDefiningIdeal]

/-- Base change of the chosen diagonal torus, transported through the general-linear
coordinate isomorphism, is the chosen diagonal torus over the new base. -/
theorem splitMaximalTorus_baseChange_comapOfIso (S : Type u) [CommRing S] [Algebra R S]
    (n : ℕ) :
    ((splitMaximalTorus R n).baseChange S).comapOfIso
        (coordinateHopfAlgebraBaseChangeIso R S n).symm = splitMaximalTorus S n := by
  ext1
  rw [SplitMaximalTorus.comapOfIso_coordinateMap, SplitMaximalTorus.baseChange_coordinateMap,
    splitMaximalTorus_coordinateMap, splitMaximalTorus_coordinateMap, Iso.symm_hom]
  exact diagonalTorusCoordinateMap_baseChange R S

/-- The upper-triangular Borel contains the chosen split maximal torus over the base.
Inclusion of closed subgroups reverses the order on their defining Hopf ideals. -/
theorem UpperTriangular.definingHopfIdeal_le_splitMaximalTorus_definingIdeal (n : ℕ) :
    UpperTriangular.definingHopfIdeal R n ≤ (splitMaximalTorus R n).definingIdeal := by
  intro x hx
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap]
  exact CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp
    (by simpa only [UpperTriangular.coordinateMap_def] using
      UpperTriangular.coordinateMap_comp_diagonalTorusCoordinateMap R n) hx

end TauCeti.GeneralLinear
