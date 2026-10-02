/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Maximal
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth

/-!
# The special linear group over a ring and its split maximal torus

`SL_n` is a reductive affine group scheme over every commutative ring. The determinant-one
diagonal matrices give a chosen split maximal torus of `SL_{r+1}` of rank `r`, in the
fundamental-weight coordinates of type `A_r`.

The integral smoothness theorem and the base-change comparison with the field-valued
special-linear coordinate algebra supply reductivity over the base. The existing
diagonal-torus coordinate morphism, its surjectivity, and its maximality over fields supply
the torus data. In particular these give an integral example over `ℤ` together with all its
geometric fibers.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definitions 3.1.1 and 3.2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 21.
-/

public section

open CategoryTheory

namespace TauCeti.SpecialLinear

universe u

variable (R : Type u) [CommRing R]

/-- The special linear group is reductive over every commutative base ring. -/
theorem reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra (n : ℕ) :
    reductiveCommHopfAlgPropertyOver R (finiteTypeCoordinateHopfAlgebra R n) := by
  rw [reductiveCommHopfAlgPropertyOver_iff]
  refine ⟨?_, ?_⟩
  · exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra R n)
  · intro k _ _ _
    exact (reductiveCommHopfAlgProperty k).prop_of_iso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso R k n).symm
      (reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n)

/-- The determinant-one diagonal torus, parametrized in fundamental-weight coordinates,
is a chosen split maximal torus of `SL_{r+1}` over every commutative base ring. -/
noncomputable def splitMaximalTorus (r : ℕ) :
    SplitMaximalTorus R (coordinateHopfAlgebra R (r + 1)) r where
  coordinateMap := diagonalTorusCoordinateMap r R
  surjective := diagonalTorusCoordinateMap_surjective r R
  maximal := by
    intro k _ _ _
    rw [← diagonalTorusDefiningIdeal_eq_ker]
    let e : FiniteTypeCommHopfAlgCat.of k
        (CommHopfAlgCat.baseChange (K := k) (coordinateHopfAlgebra R (r + 1))) ≅
        FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k (r + 1)) :=
      ObjectProperty.isoMk _ (coordinateHopfAlgebraBaseChangeIso R k (r + 1))
    have hmax := (isMaximalTorus_diagonalTorusDefiningIdeal r k).comapOfIso e
    rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal r R k] at hmax
    simp only [e, ObjectProperty.isoMk_hom, FiniteTypeCommHopfAlgCat.toBialgHom,
      ObjectProperty.homMk_hom] at hmax
    rw [HopfIdeal.comapOfSurjective_map_of_bijective _ _
      (ConcreteCategory.bijective_of_isIso
        (coordinateHopfAlgebraBaseChangeIso R k (r + 1)).hom)] at hmax
    exact hmax

/-- The chosen split maximal torus has the standard diagonal-torus coordinate morphism. -/
@[simp]
theorem splitMaximalTorus_coordinateMap (r : ℕ) :
    (splitMaximalTorus R r).coordinateMap = diagonalTorusCoordinateMap r R :=
  (rfl)

/-- The chosen split maximal torus has the standard diagonal-torus defining ideal. -/
@[simp]
theorem splitMaximalTorus_definingIdeal (r : ℕ) :
    (splitMaximalTorus R r).definingIdeal = diagonalTorusDefiningIdeal r R := by
  ext x
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap,
    mem_diagonalTorusDefiningIdeal]

end TauCeti.SpecialLinear
