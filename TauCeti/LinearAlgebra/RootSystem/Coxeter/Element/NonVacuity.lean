/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Eigen
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Basic

/-!
# The Coxeter-element theorems on TauCeti's pinned root data

Non-vacuity checks: the hypotheses of `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_E8` and its
siblings are met by TauCeti's pinned simply connected root data, for all five types. The pinned `E₆`
and `E₇` data are not root systems (their roots do not span the character lattice); the order
statements still apply because faithfulness of the Weyl group on the roots needs no spanning
hypothesis (`TauCeti.Coxeter.eq_one_of_forall_smul_root_eq`).
-/

@[expose] public section

open Polynomial RootPairing TauCeti DynkinType

namespace TauCeti.Coxeter

theorem orderOf_wordProd_e8SimplyConnectedRootDatum {l : List e8SimplyConnectedBase.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd e8SimplyConnectedRootDatum e8SimplyConnectedBase l) = 30 :=
  orderOf_wordProd_of_hasCartanType_E8 hasCartanType_e8SimplyConnectedRootDatum hnd hall

theorem orderOf_wordProd_f4SimplyConnectedRootDatum {l : List f4SimplyConnectedBase.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd f4SimplyConnectedRootDatum f4SimplyConnectedBase l) = 12 :=
  orderOf_wordProd_of_hasCartanType_F4 hasCartanType_f4SimplyConnectedRootDatum hnd hall

theorem orderOf_wordProd_g2SimplyConnectedRootDatum {l : List g2SimplyConnectedBase.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd g2SimplyConnectedRootDatum g2SimplyConnectedBase l) = 6 :=
  orderOf_wordProd_of_hasCartanType_G2 hasCartanType_g2SimplyConnectedRootDatum hnd hall

theorem orderOf_wordProd_e6SimplyConnectedRootDatum {l : List e6SimplyConnectedBase.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd e6SimplyConnectedRootDatum e6SimplyConnectedBase l) = 12 :=
  orderOf_wordProd_of_hasCartanType_E6 hasCartanType_e6SimplyConnectedRootDatum hnd hall

theorem orderOf_wordProd_e7SimplyConnectedRootDatum {l : List e7SimplyConnectedBase.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd e7SimplyConnectedRootDatum e7SimplyConnectedBase l) = 18 :=
  orderOf_wordProd_of_hasCartanType_E7 hasCartanType_e7SimplyConnectedRootDatum hnd hall

theorem charpoly_e6SimplyConnectedRootDatum {l : List e6SimplyConnectedBase.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix e6SimplyConnectedBase.support e6SimplyConnectedBase.support ℤ}
    (hW : ActsBy e6SimplyConnectedBase (wordProd e6SimplyConnectedRootDatum e6SimplyConnectedBase l)
      W) :
    W.charpoly = cyclotomic 12 ℤ * cyclotomic 3 ℤ :=
  charpoly_of_actsBy_of_hasCartanType_E6 hasCartanType_e6SimplyConnectedRootDatum hnd hall hW

theorem charpoly_e7SimplyConnectedRootDatum {l : List e7SimplyConnectedBase.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix e7SimplyConnectedBase.support e7SimplyConnectedBase.support ℤ}
    (hW : ActsBy e7SimplyConnectedBase (wordProd e7SimplyConnectedRootDatum e7SimplyConnectedBase l)
      W) :
    W.charpoly = cyclotomic 18 ℤ * cyclotomic 2 ℤ :=
  charpoly_of_actsBy_of_hasCartanType_E7 hasCartanType_e7SimplyConnectedRootDatum hnd hall hW

end TauCeti.Coxeter

end
