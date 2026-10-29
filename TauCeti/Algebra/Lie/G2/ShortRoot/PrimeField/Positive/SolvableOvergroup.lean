/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.StandardComodule
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin

/-!
# Solvable overgroups of the positive short-root G₂ subgroup

Over an algebraically closed field of characteristic three, a reduced connected solvable
closed subgroup of `GL₇` containing the positive short-root G₂ subgroup is upper triangular
in the ordered weight basis. Lie--Kolchin supplies an invariant full flag of the overgroup;
restriction to the positive subgroup identifies it with the standard flag, since that
subgroup has exactly one invariant full flag. The containment is scheme-theoretic, expressed
by vanishing of the lower matrix coordinates, and holds on points over nonreduced algebras.

This reduces maximality of the positive subgroup inside the short-root carrier to identifying
that subgroup with the carrier's upper-triangular intersection. That identification and Borel
maximality are not asserted here.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§17 and 21.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.30 and §17.a.

The flag argument uses `Positive.flag_eq_of_coefficientMatrix_isUpperTriangular`;
the generic-coordinate argument follows
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel`.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField.Positive

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra (ZMod 3) k] [IsAlgClosed k]

/-- A reduced connected solvable representation in `GL₇` whose restriction is the positive
short-root representation is upper triangular in the ordered weight basis. -/
theorem isUpperTriangular_genericMatrix_of_geometricallySolvable
    {Q : CommHopfAlgCat.{u} k} [Algebra.FiniteType k Q] [IsReduced Q]
    (hconn : geometricallyConnectedCommHopfAlgProperty k Q)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k Q)
    (π : GeneralLinear.coordinateHopfAlgebra k 7 ⟶ Q)
    (f : Q ⟶ CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra)
    (hf : π ≫ f = standardCoordinateMap k) :
    ((GeneralLinear.genericMatrix k 7).map π.hom).IsUpperTriangular := by
  let _ := GeneralLinear.corestrictStandardComodule k 7 π.hom
  obtain ⟨m, b, hb, -⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (k := k) (H := Q) (M := Fin 7 → k) hconn hsolv
  have hm : m = 7 := by simpa using (Module.finrank_eq_card_basis b).symm
  subst m
  have hcore : Comodule.Corestrict f.hom.toCoalgHom = standardComodule k := by
    rw [standardComodule_def]
    let _ := GeneralLinear.standardComodule k 7
    apply Comodule.ext
    rw [Comodule.corestrict_coact]
    -- `corestrict_coact` exposes the outer `Corestrict f`, but the right-hand coaction
    -- remains behind `GeneralLinear.corestrictStandardComodule`. Unfold that wrapper
    -- via definitional equality to expose `corestrictCoact`; the left-hand source instance
    -- similarly uses `corestrictStandardComodule` for π, giving the iterated corestriction.
    change Comodule.corestrictCoact (M := Fin 7 → k) f.hom.toCoalgHom =
      Comodule.corestrictCoact (M := Fin 7 → k) (standardCoordinateMap k).hom.toCoalgHom
    rw [← Comodule.corestrictCoact_comp]
    exact congrArg (Comodule.corestrictCoact (M := Fin 7 → k))
      (congrArg (fun g => g.hom.toCoalgHom) hf)
  have hbpos :
      (let _ := standardComodule k
       Comodule.coefficientMatrix
         (C := CommHopfAlgCat.baseChange (K := k) coordinateHopfAlgebra) b).IsUpperTriangular := by
    rw [← hcore, Comodule.coefficientMatrix_corestrict]
    exact hb.map f.hom.toCoalgHom
  have hflag := flag_eq_of_coefficientMatrix_isUpperTriangular k b hbpos
  have hstandard :
      (Comodule.coefficientMatrix (C := Q) (Pi.basisFun k (Fin 7))).IsUpperTriangular := by
    rw [Comodule.coefficientMatrix_isUpperTriangular_iff]
    intro r
    exact ⟨Comodule.flagSubcomodule b hb r,
      (Comodule.flagSubcomodule_toSubmodule b hb r).trans (hflag r)⟩
  let _ := GeneralLinear.standardComodule k 7
  rwa [Comodule.coefficientMatrix_corestrict, GeneralLinear.coefficientMatrix_basisFun] at hstandard

/-- Every reduced connected solvable closed subgroup of `GL₇` containing the scalar-extended
positive short-root subgroup is contained in the upper-triangular subgroup. The containment
hypothesis says that its defining ideal vanishes under restriction to the positive subgroup. -/
theorem upperTriangular_le_of_geometricallySolvable
    (J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k 7))
    [IsReduced (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 7) J)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 7) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k 7) J))
    (hJ : J.toIdeal ≤ RingHom.ker (standardCoordinateMap k).hom) :
    GeneralLinear.UpperTriangular.definingHopfIdeal k 7 ≤ J := by
  let π := CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra k 7) J
  let f := CommHopfAlgCat.liftQuotient J (standardCoordinateMap k) hJ
  have htri := isUpperTriangular_genericMatrix_of_geometricallySolvable k hconn hsolv π f
    (CommHopfAlgCat.mkQuotient_comp_liftQuotient J (standardCoordinateMap k) hJ)
  have hker := GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    k 7 π.hom.toAlgHom (by
      rwa [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear])
  rw [CommHopfAlgCat.mkQuotient_ker] at hker
  exact HopfIdeal.toIdeal_le_toIdeal.mp hker

end

end TauCeti.G2ShortRoot.PrimeField.Positive
