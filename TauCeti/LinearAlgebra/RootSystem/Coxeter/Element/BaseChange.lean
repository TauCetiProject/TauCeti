/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Rational
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy

/-!
# Rational base-change transport for Coxeter words

For a finite crystallographic root system `P` over a characteristic-zero domain `R` with base `b`,
and any characteristic-zero `ℚ`-algebra domain `S`, the base-changed rational model
`rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap` has the same Cartan matrix
as `b` up to `b.supportEquivRootPairingBaseChangeRationalModel S`.

This file transports word orders and characteristic polynomials of Weyl-group words in simple
reflections from `(P, b)` to that base-changed rational model over `S`, using `ActsBy` and
`Matrix.prod_map_reflMatrix_submatrix`.

## Main results

* `RootPairing.Base.orderOf_wordProd_rootPairingBaseChange_rationalModel`: rational base change
  to `S` preserves the order of any word in the simple reflections.
* `RootPairing.Base.charpoly_weylGroupRootRep_wordProd_rootPairingBaseChange_rationalModel`: the
  characteristic polynomial of a simple-reflection word on the weight space of the base-changed
  rational model over `S` is the rational reflection-matrix characteristic polynomial mapped into
  `S`.
-/

public section

open Matrix Polynomial TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsRootSystem]

/-- Rational base change to a characteristic-zero `ℚ`-algebra domain `S` preserves the order of
any word in the simple reflections. -/
theorem orderOf_wordProd_rootPairingBaseChange_rationalModel [IsDomain R] (b : P.Base)
    (S : Type*) [CommRing S] [IsDomain S] [CharZero S] [Algebra ℚ S] (l : List b.support) :
    orderOf (wordProd P b l) =
      orderOf (wordProd (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap)
        (rootPairingBaseChangeBase S b.rationalModel
          b.rationalModel_toLinearMap b.rationalModelBase)
        (l.map (b.supportEquivRootPairingBaseChangeRationalModel S).symm)) := by
  classical
  let bS := rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let e := b.supportEquivRootPairingBaseChangeRationalModel S
  have hC : bS.cartanMatrix = b.cartanMatrix.submatrix e e := by
    ext i j
    exact b.cartanMatrix_rootPairingBaseChangeRationalModel S i j
  rw [(b.actsBy_wordProd l).orderOf_eq, (bS.actsBy_wordProd _).orderOf_eq, hC,
    Matrix.prod_map_reflMatrix_submatrix b.cartanMatrix e l]
  exact (orderOf_injective
    (Matrix.reindexAlgEquiv ℤ ℤ e.symm).toRingEquiv.toMulEquiv.toMonoidHom
    (Matrix.reindexAlgEquiv ℤ ℤ e.symm).injective _).symm

/-- Over any characteristic-zero `ℚ`-algebra domain `S`, the characteristic polynomial of a
simple-reflection word on the weight space of the base-changed rational model equals the rational
reflection-matrix characteristic polynomial with coefficients mapped into `S`. -/
theorem charpoly_weylGroupRootRep_wordProd_rootPairingBaseChange_rationalModel [DecidableEq ι]
    (b : P.Base) (S : Type*) [CommRing S] [IsDomain S] [CharZero S] [Algebra ℚ S]
    (l : List b.support) :
    (((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly).map
        (algebraMap ℚ S) =
      ((rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap).weylGroupRootRep
        (wordProd (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap)
          (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
            b.rationalModelBase)
          (l.map (b.supportEquivRootPairingBaseChangeRationalModel S).symm))).charpoly := by
  classical
  let bS := rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let e := b.supportEquivRootPairingBaseChangeRationalModel S
  have hC : bS.cartanMatrix = b.cartanMatrix.submatrix e e := by
    ext i j
    exact b.cartanMatrix_rootPairingBaseChangeRationalModel S i j
  rw [← bS.charpoly_weylGroupRootRep_wordProd_eq_map_rat (l.map e.symm)]
  congr 1
  have hcast :
      (Matrix.reindexAlgEquiv ℤ ℤ e.symm
          (l.map (reflMatrix b.cartanMatrix)).prod).map (Int.castRingHom ℚ) =
        Matrix.reindexAlgEquiv ℚ ℚ e.symm
          ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)) := by
    ext i j; simp
  rw [hC, Matrix.prod_map_reflMatrix_submatrix b.cartanMatrix e l, hcast]
  exact (Matrix.charpoly_reindex e.symm _).symm

end RootPairing.Base
