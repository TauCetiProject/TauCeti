/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
public import TauCeti.LinearAlgebra.RootSystem.RootCount

/-!
# Root counts and Coxeter element orders

Combines `TauCeti.LinearAlgebra.RootSystem.RootCount` (`|Φ| = r * h`) with
`TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType` (`orderOf c = h`) to relate root counts and
positive-root counts to the order of any Coxeter element `wordProd P b l`:
`|Φ| = r * orderOf c`, `orderOf c = |Φ| / r`, and `2 * |Φ⁺| = r * orderOf c`.

## Main results

* `TauCeti.Coxeter.natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType`,
  `orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType`, and
  `two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd_of_hasCartanType`.
* `TauCeti.Coxeter.natCard_eq_card_support_mul_orderOf_wordProd`,
  `orderOf_wordProd_eq_natCard_div_card_support`,
  `two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd`, and
  `two_mul_card_posRootsFinset_eq_card_support_mul_orderOf_wordProd`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2, and Ch. VI, §1.11.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§ 3.16--3.18.
-/

public section

open RootPairing

namespace TauCeti.Coxeter

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]

/-- **For any base `b` of valid Cartan type `t` and any Coxeter element `c`, `|Φ| = r * orderOf c`**
(no spanning assumption on the roots needed). -/
theorem natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType {b : P.Base}
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  rw [orderOf_wordProd_of_hasCartanType ht h hnd hall]
  exact h.natCard_eq_card_support_mul_coxeterNumber ht

/-- **For any base `b` of valid Cartan type `t` and any Coxeter element `c`,
`orderOf c = |Φ| / r`.** -/
theorem orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType {b : P.Base}
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = Nat.card ι / b.support.card := by
  rw [orderOf_wordProd_of_hasCartanType ht h hnd hall]
  exact h.coxeterNumber_eq_natCard_div_card_support ht

/-- Twice the number of positive roots of a base `b` of valid Cartan type `t` is
`b.support.card * orderOf (wordProd P b l)`. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd_of_hasCartanType {b : P.Base}
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  (two_mul_ncard_posRoots P b).trans
    (natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType ht h hnd hall)

end HasCartanType

section Irreducible

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **`|Φ| = r * h`**: in any finite irreducible reduced crystallographic root system, the number of
roots equals the rank `b.support.card` times the order of any Coxeter element. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) :=
  natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **`h = |Φ| / r`**: in any finite irreducible reduced crystallographic root system, every Coxeter
element has order equal to the number of roots divided by the rank. -/
theorem orderOf_wordProd_eq_natCard_div_card_support {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = Nat.card ι / b.support.card :=
  orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **`2 |Φ⁺| = r * h`**: twice the number of positive roots equals the rank times the order of any
Coxeter element. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd {b : P.Base}
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd_of_hasCartanType
    (valid_classifiedDynkinType b) (hasCartanType_classifiedDynkinType b) hnd hall

/-- Finset version of
`TauCeti.Coxeter.two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd`. -/
theorem two_mul_card_posRootsFinset_eq_card_support_mul_orderOf_wordProd {b : P.Base}
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRootsFinset P b).card = b.support.card * orderOf (wordProd P b l) := by
  rw [card_posRootsFinset,
    two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd hnd hall]

end Irreducible

end TauCeti.Coxeter

end
