/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.Charpoly
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every

/-!
# Every Coxeter element of a classical type

A *Coxeter element* is a product of all the simple reflections, each once, in any order. For the
classical types the order `0, 1, …, n - 1` of the simple roots is a one-degenerate order of the
Dynkin diagram (`TauCeti.Coxeter.isOneDegenerateOrder_A` and its `B`, `C`, `D` analogues), so by
`TauCeti.Coxeter.orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType` and
`TauCeti.Coxeter.charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy` every Coxeter element
has the order and the characteristic polynomial of `Matrix.coxeterElement` of the standard Cartan
matrix:

| type | `h` | characteristic polynomial |
|---|---|---|
| `Aₙ` | `n + 1` | `1 + X + ⋯ + Xⁿ` |
| `Bₙ`, `Cₙ` | `2n` | `Xⁿ + 1` |
| `Dₙ` | `2n - 2` | `(X^{n-1} + 1)(X + 1)` |

## Main results

* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_A` (and `B`, `C`, `D`): **every** Coxeter
  element of a base of type `Aₙ` has order `n + 1` (and `2n`, `2n`, `2n - 2`).
* `TauCeti.Coxeter.charpoly_of_hasCartanType_A_of_actsBy` (and `B`, `C`, `D`): the matrix of every
  such Coxeter element on the simple roots has the characteristic polynomial in the table.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Ch. VI, Planches I–IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix RootPairing TauCeti

namespace TauCeti.Coxeter

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]
  {b : P.Base} {l : List b.support}

/-- **Every Coxeter element of a base of type `Aₙ` has order `n + 1`.** -/
theorem orderOf_wordProd_of_hasCartanType_A [Finite ι] {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = n + 1 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .A n)
    (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_A hn)

/-- **Every Coxeter element of a base of type `Bₙ` has order `2n`.** -/
theorem orderOf_wordProd_of_hasCartanType_B [Finite ι] {m : ℕ} (h : HasCartanType P b (.B (m + 1)))
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 2 * (m + 1) :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .B (m + 1))
    (DynkinType.cartanMatrix_B _) (isOneDegenerateOrder_B _) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_B m)

/-- **Every Coxeter element of a base of type `Cₙ` has order `2n`.** -/
theorem orderOf_wordProd_of_hasCartanType_C [Finite ι] {m : ℕ} (h : HasCartanType P b (.C (m + 1)))
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 2 * (m + 1) :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .C (m + 1))
    (DynkinType.cartanMatrix_C _) (isOneDegenerateOrder_C _) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_C m)

/-- **Every Coxeter element of a base of type `Dₙ` has order `2n - 2`** (`n = m + 3`). -/
theorem orderOf_wordProd_of_hasCartanType_D [Finite ι] {m : ℕ} (h : HasCartanType P b (.D (m + 3)))
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 2 * (m + 2) :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .D (m + 3))
    (DynkinType.cartanMatrix_D _) (isOneDegenerateOrder_D m) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_D m)

/-- **Every Coxeter element of a base of type `Aₙ`** (`n = m + 1`) has characteristic polynomial
`1 + X + ⋯ + Xⁿ` on the simple roots. -/
theorem charpoly_of_hasCartanType_A_of_actsBy [DecidableEq ι] {m : ℕ}
    (h : HasCartanType P b (.A (m + 1))) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = ∑ i ∈ Finset.range (m + 2), Polynomial.X ^ i :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .A (m + 1))
    (DynkinType.cartanMatrix_A _) (isOneDegenerateOrder_A _) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxeterElement_A m)

/-- **Every Coxeter element of a base of type `Bₙ`** (`n = m + 1`) has characteristic polynomial
`Xⁿ + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_B_of_actsBy [DecidableEq ι] {m : ℕ}
    (h : HasCartanType P b (.B (m + 1))) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.X ^ (m + 1) + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .B (m + 1))
    (DynkinType.cartanMatrix_B _) (isOneDegenerateOrder_B _) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxeterElement_B m)

/-- **Every Coxeter element of a base of type `Cₙ`** (`n = m + 1`) has characteristic polynomial
`Xⁿ + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_C_of_actsBy [DecidableEq ι] {m : ℕ}
    (h : HasCartanType P b (.C (m + 1))) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.X ^ (m + 1) + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .C (m + 1))
    (DynkinType.cartanMatrix_C _) (isOneDegenerateOrder_C _) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxeterElement_C m)

/-- **Every Coxeter element of a base of type `Dₙ`** (`n = m + 3`) has characteristic polynomial
`(X^{n-1} + 1)(X + 1)` on the simple roots. -/
theorem charpoly_of_hasCartanType_D_of_actsBy [DecidableEq ι] {m : ℕ}
    (h : HasCartanType P b (.D (m + 3))) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = (Polynomial.X ^ (m + 2) + 1) * (Polynomial.X + 1) :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .D (m + 3))
    (DynkinType.cartanMatrix_D _) (isOneDegenerateOrder_D m) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxeterElement_D m)

end TauCeti.Coxeter

end
