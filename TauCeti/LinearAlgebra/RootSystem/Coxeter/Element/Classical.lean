/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every

/-!
# Every Coxeter element of types `B`, `C` and `D` has order the Coxeter number

A *Coxeter element* of a base is a product of all the simple reflections, each once, in any order.
The Dynkin diagrams of types `Bₙ`, `Cₙ` and `Dₙ` are trees whose numbering order is
one-degenerate (`TauCeti.Coxeter.isOneDegenerateOrder_B` and its siblings), so the order and the
characteristic polynomial of a Coxeter element do not depend on the ordering, and they are those
of the Coxeter element of the standard Cartan matrix computed in
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical`:

| type | `h` | characteristic polynomial on the simple roots |
|---|---|---|
| `Bₙ`, `Cₙ` (`n ≥ 1`) | `2n` | `X ^ n + 1` |
| `Dₙ` (`n ≥ 4`) | `2n - 2` | `(X ^ (n - 1) + 1) (X + 1)` |

The statements are phrased with `TauCeti.HasCartanType`, so they apply to any base that the
classification has matched to a type. As for the exceptional types, the characteristic polynomial
describes the action on the span of the roots.

## Main results

* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_B` (and `C`, `D`): **every** Coxeter element
  of a base of type `Bₙ` or `Cₙ` has order `2n`, and of type `Dₙ` order `2n - 2`.
* `TauCeti.Coxeter.charpoly_of_hasCartanType_B_of_actsBy` (and `C`, `D`): the matrix of every such
  Coxeter element on the simple roots has the characteristic polynomial in the table.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates II--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.18.
-/

public section

open Matrix Polynomial RootPairing TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]

namespace TauCeti.Coxeter

variable {b : P.Base} {l : List b.support} {n : ℕ}

/-- **Every Coxeter element of a base of type `Bₙ` has order `2n`.** -/
theorem orderOf_wordProd_of_hasCartanType_B [Finite ι] (h : HasCartanType P b (.B n))
    (hn : 0 < n) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_B hn)

/-- **Every Coxeter element of a base of type `Cₙ` has order `2n`.** -/
theorem orderOf_wordProd_of_hasCartanType_C [Finite ι] (h : HasCartanType P b (.C n))
    (hn : 0 < n) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_C hn)

/-- **Every Coxeter element of a base of type `Dₙ` has order `2n - 2`.** -/
theorem orderOf_wordProd_of_hasCartanType_D [Finite ι] (h : HasCartanType P b (.D n))
    (hn : 4 ≤ n) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 2 * (n - 1) :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_D hn)

/-- **Every Coxeter element of a base of type `Bₙ`** has characteristic polynomial `X ^ n + 1` on
the simple roots. -/
theorem charpoly_of_hasCartanType_B_of_actsBy [DecidableEq ι] (h : HasCartanType P b (.B n))
    (hn : 0 < n) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) : W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxeterElement_B hn)

/-- **Every Coxeter element of a base of type `Cₙ`** has characteristic polynomial `X ^ n + 1` on
the simple roots. -/
theorem charpoly_of_hasCartanType_C_of_actsBy [DecidableEq ι] (h : HasCartanType P b (.C n))
    (hn : 0 < n) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) : W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxeterElement_C hn)

/-- **Every Coxeter element of a base of type `Dₙ`** has characteristic polynomial
`(X ^ (n - 1) + 1) (X + 1)` on the simple roots. -/
theorem charpoly_of_hasCartanType_D_of_actsBy [DecidableEq ι] (h : HasCartanType P b (.D n))
    (hn : 4 ≤ n) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) : W.charpoly = (X ^ (n - 1) + 1) * (X + 1) :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxeterElement_D hn)

end TauCeti.Coxeter

end
