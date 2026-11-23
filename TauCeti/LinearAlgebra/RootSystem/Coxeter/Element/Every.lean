/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclotomic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Charpoly
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Number
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Exceptional

/-!
# Every Coxeter element of a Dynkin type has order the Coxeter number

A *Coxeter element* is a product of all the simple reflections, each once, in any order. The Dynkin
diagrams of all classical and exceptional types are trees, so their vertices admit a one-degenerate
order, and `List.eq_of_isOneDegenerateOrder` shows that the order and the characteristic polynomial
of the product do not depend on the ordering:

| type | rank bound | `h` | characteristic polynomial |
|---|---|---|---|
| `Aₙ` | all `n` | `n + 1` | `∑_{k=0}^n X^k` |
| `Bₙ` | `1 ≤ n` | `2 n` | `X^n + 1` |
| `Cₙ` | `1 ≤ n` | `2 n` | `X^n + 1` |
| `Dₙ` | `2 ≤ n` | `2 (n - 1)` | `(X^{n-1} + 1)(X + 1)` |
| `E₆` | — | 12 | `Φ₁₂ Φ₃` |
| `E₇` | — | 18 | `Φ₁₈ Φ₂` |
| `E₈` | — | 30 | `Φ₃₀` |
| `F₄` | — | 12 | `Φ₁₂` |
| `G₂` | — | 6 | `Φ₆` |

The statements are phrased with `TauCeti.HasCartanType`, so they apply to any base that the
classification has matched to a type. TauCeti's `G₂` Cartan matrix is the transpose of Mathlib's
`CartanMatrix.G₂`.

## Main results

* `TauCeti.Coxeter.orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType` and
  `TauCeti.Coxeter.charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy`: for a base of
  Cartan type `t` with a one-degenerate order, every Coxeter element has the order and the
  characteristic polynomial of the Coxeter element of the standard Cartan matrix of `t`.
* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_A` (and `B`, `C`, `D`, `E6`, `E7`, `E8`, `F4`,
  `G2`): every Coxeter element of a base of that type has order `h`.
* `TauCeti.Coxeter.charpoly_of_hasCartanType_A_of_actsBy` (and `B`, `C`, `D`, `E6`, `E7`, `E8`,
  `F4`, `G2`), and `TauCeti.Coxeter.charpoly_of_hasCartanType_of_actsBy`: the matrix of every such
  Coxeter element on the simple roots has the characteristic polynomial of `coxeterElement
  t.cartanMatrix`.
* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType`,
  `orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType`, `two_le_orderOf_wordProd`, and
  `orderOf_wordProd_eq_orderOf_wordProd`: every Coxeter element of a finite irreducible reduced
  crystallographic root system has order `t.coxeterNumber` (at least `2`), independent of base and
  ordering.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix RootPairing TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]

namespace RootPairing.Base

omit [IsDomain R] [CharZero R] in
/-- A one-degenerate order of a standard Cartan matrix transports to a base of that type: any
Coxeter element and the one in the numbering order are orderings of a common one-degenerate
order. -/
private theorem exists_isOneDegenerateOrder_of_cartanMatrix_eq {n : ℕ} (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (e : b.support ≃ Fin n) (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) (S₀ : List (Fin n))
    (hel₀ : List.IsOneDegenerateOrder (fun i j : Fin n => A i j ≠ 0) S₀)
    (hperm₀ : S₀.Perm (List.finRange n))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    ∃ S : List b.support, S.Nodup ∧
      List.IsOneDegenerateOrder (fun x y => b.cartanMatrix x y ≠ 0) S ∧ l.Perm S ∧
      ((List.finRange n).map e.symm).Perm S := by
  have hfun : (fun x y => A (e x) (e y) ≠ 0) = fun x y => b.cartanMatrix x y ≠ 0 := by
    funext x y; rw [hA]
  have hS : ((List.finRange n).map e.symm).Perm (S₀.map e.symm) := (hperm₀.map e.symm).symm
  have hndτ : ((List.finRange n).map e.symm).Nodup :=
    (List.nodup_finRange n).map e.symm.injective
  have hlτ : l.Perm ((List.finRange n).map e.symm) :=
    (List.perm_ext_iff_of_nodup hnd hndτ).2 fun i =>
      iff_of_true (hall i) (List.mem_map.2 ⟨e i, List.mem_finRange _, e.symm_apply_apply i⟩)
  exact ⟨_, hS.nodup_iff.1 hndτ, hfun ▸ hel₀.map_equiv e, hlτ.trans hS, hS⟩

end RootPairing.Base

namespace TauCeti.Coxeter

/-! ### The one-degenerate orders of the exceptional diagrams list every vertex -/

/-- The one-degenerate order of `E₈` lists every vertex once. -/
private theorem perm_finRange_E8 :
    ([0, 2, 3, 1, 4, 5, 6, 7] : List (Fin 8)).Perm (List.finRange 8) := by
  decide

/-- The one-degenerate order of `E₇` lists every vertex once. -/
private theorem perm_finRange_E7 :
    ([0, 2, 3, 1, 4, 5, 6] : List (Fin 7)).Perm (List.finRange 7) := by
  decide

/-- The one-degenerate order of `E₆` lists every vertex once. -/
private theorem perm_finRange_E6 :
    ([0, 2, 3, 1, 4, 5] : List (Fin 6)).Perm (List.finRange 6) := by
  decide

/-- The one-degenerate order of `F₄` lists every vertex once. -/
private theorem perm_finRange_F4 :
    ([0, 1, 2, 3] : List (Fin 4)).Perm (List.finRange 4) := by
  decide

/-- The one-degenerate order of `G₂` lists every vertex once. -/
private theorem perm_finRange_G2 :
    ([0, 1] : List (Fin 2)).Perm (List.finRange 2) := by
  decide

/-! ### Independence of the ordering -/

/-- The characteristic polynomial of any Coxeter element of a base of Cartan type `t`, with standard
Cartan matrix `A`, is that of `coxeterElement A` when the diagram of `t` has a one-degenerate
order. -/
theorem charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy [DecidableEq ι] {t : DynkinType}
    {A : Matrix (Fin t.rank) (Fin t.rank) ℤ} (ht : t.cartanMatrix = A) {S₀ : List (Fin t.rank)}
    (hel₀ : List.IsOneDegenerateOrder (fun i j => A i j ≠ 0) S₀)
    (hperm₀ : S₀.Perm (List.finRange t.rank)) {b : P.Base} (h : HasCartanType P b t)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) : W.charpoly = (coxeterElement A).charpoly := by
  subst ht
  obtain ⟨e, hA⟩ := (hasCartanType_iff b t).1 h
  obtain ⟨S, hndS, hel, hlS, hτS⟩ :=
    Base.exists_isOneDegenerateOrder_of_cartanMatrix_eq b _ e hA S₀ hel₀ hperm₀ hnd hall
  rw [hW.unique (b.actsBy_wordProd l),
    b.charpoly_prod_reflMatrix_eq_of_isOneDegenerateOrder hndS hel hlS hτS,
    b.prod_reflMatrix_eq _ e hA,
    coe_reindexAlgEquiv, charpoly_reindex]

/-- Any Coxeter element of a base of Cartan type `t`, with standard Cartan matrix `A`, has the
order of `coxeterElement A` when the diagram of `t` has a one-degenerate order. -/
theorem orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType [Finite ι] {t : DynkinType}
    {A : Matrix (Fin t.rank) (Fin t.rank) ℤ} (ht : t.cartanMatrix = A) {S₀ : List (Fin t.rank)}
    (hel₀ : List.IsOneDegenerateOrder (fun i j => A i j ≠ 0) S₀)
    (hperm₀ : S₀.Perm (List.finRange t.rank)) {b : P.Base} (h : HasCartanType P b t)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = orderOf (coxeterElement A) := by
  subst ht
  obtain ⟨e, hA⟩ := (hasCartanType_iff b t).1 h
  obtain ⟨S, hndS, hel, hlS, hτS⟩ :=
    Base.exists_isOneDegenerateOrder_of_cartanMatrix_eq b _ e hA S₀ hel₀ hperm₀ hnd hall
  rw [b.orderOf_wordProd_eq_of_isOneDegenerateOrder hndS hel hlS hτS,
    b.orderOf_wordProd_of_cartanMatrix_eq _ e hA]

/-! ### The exceptional types -/

variable {b : P.Base} {l : List b.support}

/-- **Every Coxeter element of a base of type `E₆` has order 12.** -/
theorem orderOf_wordProd_of_hasCartanType_E6 [Finite ι] (h : HasCartanType P b .E6) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 12 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .E6)
    DynkinType.cartanMatrix_E6 isOneDegenerateOrder_E6 perm_finRange_E6 h hnd
    hall).trans orderOf_coxE6

/-- **Every Coxeter element of a base of type `E₇` has order 18.** -/
theorem orderOf_wordProd_of_hasCartanType_E7 [Finite ι] (h : HasCartanType P b .E7) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 18 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .E7)
    DynkinType.cartanMatrix_E7 isOneDegenerateOrder_E7 perm_finRange_E7 h hnd
    hall).trans orderOf_coxE7

/-- **Every Coxeter element of a base of type `E₈` has order 30.** -/
theorem orderOf_wordProd_of_hasCartanType_E8 [Finite ι] (h : HasCartanType P b .E8) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 30 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .E8)
    DynkinType.cartanMatrix_E8 isOneDegenerateOrder_E8 perm_finRange_E8 h hnd
    hall).trans orderOf_coxE8

/-- **Every Coxeter element of a base of type `F₄` has order 12.** -/
theorem orderOf_wordProd_of_hasCartanType_F4 [Finite ι] (h : HasCartanType P b .F4) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 12 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .F4)
    DynkinType.cartanMatrix_F4 isOneDegenerateOrder_F4 perm_finRange_F4 h hnd
    hall).trans orderOf_coxF4

/-- **Every Coxeter element of a base of type `G₂` has order 6.** -/
theorem orderOf_wordProd_of_hasCartanType_G2 [Finite ι] (h : HasCartanType P b .G2) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 6 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .G2)
    DynkinType.cartanMatrix_G2 isOneDegenerateOrder_G2 perm_finRange_G2 h hnd
    hall).trans orderOf_coxG2

/-- **Every Coxeter element of a base of type `E₆`** has characteristic polynomial `Φ₁₂ Φ₃` on the
simple roots. -/
theorem charpoly_of_hasCartanType_E6_of_actsBy [DecidableEq ι] (h : HasCartanType P b .E6)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 12 ℤ * Polynomial.cyclotomic 3 ℤ :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .E6)
    DynkinType.cartanMatrix_E6 isOneDegenerateOrder_E6 perm_finRange_E6 h hnd
    hall hW).trans charpoly_coxE6

/-- **Every Coxeter element of a base of type `E₇`** has characteristic polynomial `Φ₁₈ Φ₂` on the
simple roots. -/
theorem charpoly_of_hasCartanType_E7_of_actsBy [DecidableEq ι] (h : HasCartanType P b .E7)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 18 ℤ * Polynomial.cyclotomic 2 ℤ :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .E7)
    DynkinType.cartanMatrix_E7 isOneDegenerateOrder_E7 perm_finRange_E7 h hnd
    hall hW).trans charpoly_coxE7

/-- **Every Coxeter element of a base of type `E₈`** has characteristic polynomial `Φ₃₀` on the
simple roots. -/
theorem charpoly_of_hasCartanType_E8_of_actsBy [DecidableEq ι] (h : HasCartanType P b .E8)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 30 ℤ :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .E8)
    DynkinType.cartanMatrix_E8 isOneDegenerateOrder_E8 perm_finRange_E8 h hnd
    hall hW).trans charpoly_coxE8

/-- **Every Coxeter element of a base of type `F₄`** has characteristic polynomial `Φ₁₂` on the
simple roots. -/
theorem charpoly_of_hasCartanType_F4_of_actsBy [DecidableEq ι] (h : HasCartanType P b .F4)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 12 ℤ :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .F4)
    DynkinType.cartanMatrix_F4 isOneDegenerateOrder_F4 perm_finRange_F4 h hnd
    hall hW).trans charpoly_coxF4

/-- **Every Coxeter element of a base of type `G₂`** has characteristic polynomial `Φ₆` on the
simple roots. -/
theorem charpoly_of_hasCartanType_G2_of_actsBy [DecidableEq ι] (h : HasCartanType P b .G2)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 6 ℤ :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .G2)
    DynkinType.cartanMatrix_G2 isOneDegenerateOrder_G2 perm_finRange_G2 h hnd
    hall hW).trans charpoly_coxG2

/-! ### The classical types -/

/-- **Every Coxeter element of a base of type `Aₙ` has order `n + 1`.** -/
theorem orderOf_wordProd_of_hasCartanType_A [Finite ι] {n : ℕ} (h : HasCartanType P b (.A n))
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = n + 1 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .A n)
    (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_A n)

/-- **Every Coxeter element of a base of type `Bₙ` (`1 ≤ n`) has order `2 n`.** -/
theorem orderOf_wordProd_of_hasCartanType_B [Finite ι] {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_B hn)

/-- **Every Coxeter element of a base of type `Cₙ` (`1 ≤ n`) has order `2 n`.** -/
theorem orderOf_wordProd_of_hasCartanType_C [Finite ι] {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_C hn)

/-- **Every Coxeter element of a base of type `Dₙ` (`2 ≤ n`) has order `2 (n - 1)`.** -/
theorem orderOf_wordProd_of_hasCartanType_D [Finite ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * (n - 1) :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd
    hall).trans (orderOf_coxeterElement_D hn)

/-- **Every Coxeter element of a base of type `Aₙ`** has characteristic polynomial
`∑_{k=0}^n X^k` on the simple roots. -/
theorem charpoly_of_hasCartanType_A_of_actsBy [DecidableEq ι] {n : ℕ}
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = ∑ k ∈ Finset.range (n + 1), Polynomial.X ^ k :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .A n)
    (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd
    hall hW).trans (charpoly_coxeterElement_A n)

/-- **Every Coxeter element of a base of type `Bₙ` (`1 ≤ n`)** has characteristic polynomial
`X^n + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_B_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd
    hall hW).trans (charpoly_coxeterElement_B hn)

/-- **Every Coxeter element of a base of type `Cₙ` (`1 ≤ n`)** has characteristic polynomial
`X^n + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_C_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd
    hall hW).trans (charpoly_coxeterElement_C hn)

/-- **Every Coxeter element of a base of type `Dₙ` (`2 ≤ n`)** has characteristic polynomial
`(X^{n-1} + 1)(X + 1)` on the simple roots. -/
theorem charpoly_of_hasCartanType_D_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = (Polynomial.X ^ (n - 1) + 1) * (Polynomial.X + 1) :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd
    hall hW).trans (charpoly_coxeterElement_D hn)

/-! ### Uniform characteristic polynomial and order across all Dynkin types -/

/-- **Every Coxeter element of a base of Cartan type `t`** has the same characteristic polynomial
on the simple roots as `Matrix.coxeterElement t.cartanMatrix`. -/
theorem charpoly_of_hasCartanType_of_actsBy [DecidableEq ι] {t : DynkinType}
    (h : HasCartanType P b t) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = (coxeterElement t.cartanMatrix).charpoly := by
  cases t with
  | A n =>
    rw [DynkinType.cartanMatrix_A]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .A n)
      (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd hall hW
  | B n =>
    rw [DynkinType.cartanMatrix_B]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .B n)
      (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd hall hW
  | C n =>
    rw [DynkinType.cartanMatrix_C]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .C n)
      (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd hall hW
  | D n =>
    rw [DynkinType.cartanMatrix_D]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .D n)
      (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd hall hW
  | E6 =>
    rw [DynkinType.cartanMatrix_E6]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .E6)
      DynkinType.cartanMatrix_E6 isOneDegenerateOrder_E6 perm_finRange_E6 h hnd hall hW
  | E7 =>
    rw [DynkinType.cartanMatrix_E7]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .E7)
      DynkinType.cartanMatrix_E7 isOneDegenerateOrder_E7 perm_finRange_E7 h hnd hall hW
  | E8 =>
    rw [DynkinType.cartanMatrix_E8]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .E8)
      DynkinType.cartanMatrix_E8 isOneDegenerateOrder_E8 perm_finRange_E8 h hnd hall hW
  | F4 =>
    rw [DynkinType.cartanMatrix_F4]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .F4)
      DynkinType.cartanMatrix_F4 isOneDegenerateOrder_F4 perm_finRange_F4 h hnd hall hW
  | G2 =>
    rw [DynkinType.cartanMatrix_G2]
    exact charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .G2)
      DynkinType.cartanMatrix_G2 isOneDegenerateOrder_G2 perm_finRange_G2 h hnd hall hW

/-- **Every Coxeter element of a base of valid Cartan type `t` has order `t.coxeterNumber`.** -/
theorem orderOf_wordProd_of_hasCartanType [Finite ι] {t : DynkinType} (ht : t.Valid)
    (h : HasCartanType P b t) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = t.coxeterNumber := by
  cases t with
  | A n => rw [DynkinType.coxeterNumber_A]; exact orderOf_wordProd_of_hasCartanType_A h hnd hall
  | B n =>
    rw [DynkinType.coxeterNumber_B]
    exact orderOf_wordProd_of_hasCartanType_B (by have := DynkinType.valid_B.mp ht; omega)
      h hnd hall
  | C n =>
    rw [DynkinType.coxeterNumber_C]
    exact orderOf_wordProd_of_hasCartanType_C (by have := DynkinType.valid_C.mp ht; omega)
      h hnd hall
  | D n =>
    rw [DynkinType.coxeterNumber_D]
    exact orderOf_wordProd_of_hasCartanType_D (by have := DynkinType.valid_D.mp ht; omega)
      h hnd hall
  | E6 => rw [DynkinType.coxeterNumber_E6]; exact orderOf_wordProd_of_hasCartanType_E6 h hnd hall
  | E7 => rw [DynkinType.coxeterNumber_E7]; exact orderOf_wordProd_of_hasCartanType_E7 h hnd hall
  | E8 => rw [DynkinType.coxeterNumber_E8]; exact orderOf_wordProd_of_hasCartanType_E8 h hnd hall
  | F4 => rw [DynkinType.coxeterNumber_F4]; exact orderOf_wordProd_of_hasCartanType_F4 h hnd hall
  | G2 => rw [DynkinType.coxeterNumber_G2]; exact orderOf_wordProd_of_hasCartanType_G2 h hnd hall

section Irreducible

variable [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsIrreducible]

/-- **Every Coxeter element of a base `b` of a finite irreducible reduced crystallographic root
system has order `(classifiedDynkinType b).coxeterNumber`.** -/
theorem orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = (classifiedDynkinType b).coxeterNumber :=
  orderOf_wordProd_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **Every Coxeter element of a finite irreducible reduced crystallographic root system has order
at least `2`.** -/
theorem two_le_orderOf_wordProd (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 ≤ orderOf (wordProd P b l) := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall]
  exact (classifiedDynkinType b).two_le_coxeterNumber (valid_classifiedDynkinType b)

/-- **Any two Coxeter elements of a finite irreducible reduced crystallographic root system, across
any two bases and any two orderings of their simple reflections, have the same order.** -/
theorem orderOf_wordProd_eq_orderOf_wordProd {b' : P.Base} {l' : List b'.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) (hnd' : l'.Nodup) (hall' : ∀ i, i ∈ l') :
    orderOf (wordProd P b l) = orderOf (wordProd P b' l') := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall,
    orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd' hall',
    b.classifiedDynkinType_eq_classifiedDynkinType b']

end Irreducible

end TauCeti.Coxeter

end
