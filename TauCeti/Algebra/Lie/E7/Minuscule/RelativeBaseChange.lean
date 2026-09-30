/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.BaseChange

/-!
# Relative base change of the type-E7 minuscule carrier

The full-weight type-`E₇` minuscule carrier over a commutative ring is obtained by base change
from its integral coordinate Hopf algebra. Consequently, for a scalar tower `ℤ → R → S`,
extending the carrier from `R` to `S` agrees with constructing the carrier directly over `S`.

This comparison is the relative form of the existing integral base-change presentation. It is
the isomorphism used when geometric properties of a carrier over a field are checked after
extension to an algebraic closure.

## Main declarations

* `TauCeti.E7Minuscule.coordinateHopfAlgebraBaseChangeIso`: scalar extension of the
  coordinate Hopf algebra from `R` to `S` is the coordinate Hopf algebra over `S`.
* `TauCeti.E7Minuscule.finiteTypeCoordinateHopfAlgebraBaseChangeIso`: the same comparison
  in the category of finite-type commutative Hopf algebras.

## Implementation notes

`CommHopfAlgCat.baseChangeTowerIso` requires the intermediate ring to live in the universe of
the Hopf algebra being extended. The integral carrier lives in `Type`, while `R : Type u` is
arbitrary, so the comparison applies the underlying bialgebra tower equivalence
`TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv` directly.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule

universe u v

attribute [local instance high] Algebra.toModule

variable (R : Type u) (S : Type max u v) [CommRing R] [CommRing S]
variable [Algebra R S]

/-- Scalar extension of the full-weight type-`E₇` minuscule carrier from `R` to `S` agrees
with the carrier obtained directly by base change from its integral model to `S`. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := S) (coordinateHopfAlgebra R) ≅
      coordinateHopfAlgebra S :=
  (CommHopfAlgCat.baseChangeFunctor (K := S)).mapIso (baseChangeCoordinateIso R) ≪≫
    eqToIso (CommHopfAlgCat.baseChangeFunctor_obj (K := S)
      (CommHopfAlgCat.baseChange (K := R)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 56)
          definingIdeal))) ≪≫
    _root_.CommHopfAlgCat.isoMk
      (TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv ℤ R
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal)
        S) ≪≫
    (baseChangeCoordinateIso S).symm

/-- On a pure tensor represented through the integral presentation over `R`, scalar extension
absorbs the intermediate coefficient into the scalar over `S`. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeIso_hom_tmul (s : S) (r : R)
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal) :
    (coordinateHopfAlgebraBaseChangeIso R S).hom.hom
        (s ⊗ₜ[R] (baseChangeCoordinateIso R).inv.hom (r ⊗ₜ[ℤ] x)) =
      (baseChangeCoordinateIso S).inv.hom ((r • s) ⊗ₜ[ℤ] x) := by
  simp [coordinateHopfAlgebraBaseChangeIso]

/-- The inverse scalar-extension comparison inserts the unit of the intermediate ring in the
integral presentation. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeIso_inv_tmul (s : S)
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal) :
    (coordinateHopfAlgebraBaseChangeIso R S).inv.hom
        ((baseChangeCoordinateIso S).inv.hom (s ⊗ₜ[ℤ] x)) =
      s ⊗ₜ[R] (baseChangeCoordinateIso R).inv.hom (1 ⊗ₜ[ℤ] x) := by
  simp [coordinateHopfAlgebraBaseChangeIso]

/-- The finite-type coordinate Hopf algebra of the full-weight type-`E₇` minuscule carrier
commutes with scalar extension. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := S) (finiteTypeCoordinateHopfAlgebra R) ≅
      finiteTypeCoordinateHopfAlgebra S :=
  FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso
    (finiteTypeCoordinateHopfAlgebra_obj R)
    (finiteTypeCoordinateHopfAlgebra_obj S)
    (coordinateHopfAlgebraBaseChangeIso R S)

/-- The underlying commutative-Hopf-algebra morphism of the finite-type scalar-extension
comparison is the coordinate-Hopf-algebra comparison, with the object equalities made explicit.
-/
@[simp]
theorem finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom :
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso R S).hom.hom =
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := S))
          (finiteTypeCoordinateHopfAlgebra_obj R)) ≪≫
        coordinateHopfAlgebraBaseChangeIso R S ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj S).symm).hom := by
  exact FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso_hom
    (finiteTypeCoordinateHopfAlgebra_obj R)
    (finiteTypeCoordinateHopfAlgebra_obj S)
    (coordinateHopfAlgebraBaseChangeIso R S)

end TauCeti.E7Minuscule
