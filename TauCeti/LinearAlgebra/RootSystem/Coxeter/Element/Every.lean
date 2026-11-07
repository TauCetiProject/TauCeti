/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclotomic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Reorder
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Exceptional

/-!
# Every Coxeter element of an exceptional type has order the Coxeter number

A *Coxeter element* is a product of all the simple reflections, each once, in any order. The Dynkin
diagrams `E₆`, `E₇`, `E₈`, `F₄`, `G₂` are trees, so their vertices admit an elimination order
(checked by `decide`), and `List.eq_of_isElimOrder` shows that the order and the characteristic
polynomial of the product do not depend on the ordering:

| type | `h` | characteristic polynomial |
|---|---|---|
| `E₆` | 12 | `Φ₁₂ Φ₃` |
| `E₇` | 18 | `Φ₁₈ Φ₂` |
| `E₈` | 30 | `Φ₃₀` |
| `F₄` | 12 | `Φ₁₂` |
| `G₂` | 6 | `Φ₆` |

The statements are phrased with `TauCeti.HasCartanType`, so they apply to any base that the
classification has matched to a type. TauCeti's `G₂` Cartan matrix is the transpose of Mathlib's
`CartanMatrix.G₂`.

## Main results

* `RootPairing.Base.charpoly_prod_reflMatrix_eq_of_isElimOrder`: for a base whose Dynkin diagram has
  an elimination order, the matrices of all Coxeter elements on the simple roots have the same
  characteristic polynomial.
* `TauCeti.Coxeter.orderOf_wordProd_of_isElimOrder_of_hasCartanType` and
  `TauCeti.Coxeter.charpoly_of_isElimOrder_of_hasCartanType_of_actsBy`: for a base of Cartan type
  `t` with an elimination order, every Coxeter element has the order and the characteristic
  polynomial of the Coxeter element of the standard Cartan matrix of `t`.
* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_E8` (and `E7`, `E6`, `F4`, `G2`): **every**
  Coxeter element of a base of type `E₈` has order 30 (and 18, 12, 12, 6).
* `TauCeti.Coxeter.charpoly_of_hasCartanType_E8_of_actsBy` (and `E7`, `E6`, `F4`, `G2`): the matrix
  of every such Coxeter element on the simple roots has the characteristic polynomial in the table.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix RootPairing TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]

namespace RootPairing.Base

omit [IsDomain R] [CharZero R] in
/-- An elimination order of a standard Cartan matrix transports to a base of that type: any Coxeter
element and the one in the numbering order are orderings of a common elimination order. -/
private theorem exists_isElimOrder_of_cartanMatrix_eq {n : ℕ} (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (e : b.support ≃ Fin n) (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) (S₀ : List (Fin n))
    (hel₀ : List.IsElimOrder (fun i j : Fin n => A i j ≠ 0) S₀) (hperm₀ : S₀.Perm (List.finRange n))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    ∃ S : List b.support, S.Nodup ∧ List.IsElimOrder (fun x y => b.cartanMatrix x y ≠ 0) S ∧
      l.Perm S ∧ ((List.finRange n).map e.symm).Perm S := by
  have hfun : (fun x y => A (e x) (e y) ≠ 0) = fun x y => b.cartanMatrix x y ≠ 0 := by
    funext x y; rw [hA]
  have hS : ((List.finRange n).map e.symm).Perm (S₀.map e.symm) := (hperm₀.map e.symm).symm
  have hndτ : ((List.finRange n).map e.symm).Nodup :=
    (List.nodup_finRange n).map e.symm.injective
  have hlτ : l.Perm ((List.finRange n).map e.symm) :=
    (List.perm_ext_iff_of_nodup hnd hndτ).2 fun i =>
      iff_of_true (hall i) (List.mem_map.2 ⟨e i, List.mem_finRange _, e.symm_apply_apply i⟩)
  exact ⟨_, hS.nodup_iff.1 hndτ, hfun ▸ hel₀.map_equiv e, hlτ.trans hS, hS⟩

/-- **All Coxeter elements have the same characteristic polynomial** (of their matrices on the
simple roots) when the Dynkin diagram of the base has an elimination order. -/
theorem charpoly_prod_reflMatrix_eq_of_isElimOrder [DecidableEq ι] (b : P.Base)
    {S : List b.support} (hnd : S.Nodup)
    (hel : List.IsElimOrder (fun x y => b.cartanMatrix x y ≠ 0) S) {l l' : List b.support}
    (hl : l.Perm S) (hl' : l'.Perm S) :
    ((l.map (reflMatrix b.cartanMatrix)).prod).charpoly =
      ((l'.map (reflMatrix b.cartanMatrix)).prod).charpoly :=
  List.eq_of_isElimOrder (fun _ _ h h' => h (b.cartanMatrix_apply_eq_zero_iff_symm.2 h')) hnd hel
    (fun l => ((l.map (reflMatrix b.cartanMatrix)).prod).charpoly)
    (fun l l' _ hce => by
      have hw : wordProd P b l = wordProd P b l' := wordProd_eq_of_commEquiv b hce
      have hl' : ActsBy b (wordProd P b l) ((l'.map (reflMatrix b.cartanMatrix)).prod) := by
        rw [hw]; exact actsBy_wordProd b l'
      rw [(actsBy_wordProd b l).unique hl'])
    (fun a t _ => by
      simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_nil, mul_one]
      exact charpoly_mul_comm _ _)
    hl hl'

end RootPairing.Base

namespace TauCeti.Coxeter

/-! ### The elimination orders of the exceptional diagrams list every vertex -/

/-- The elimination order of `E₈` lists every vertex once. -/
private theorem perm_finRange_E8 :
    ([0, 2, 3, 1, 4, 5, 6, 7] : List (Fin 8)).Perm (List.finRange 8) := by
  decide

/-- The elimination order of `E₇` lists every vertex once. -/
private theorem perm_finRange_E7 :
    ([0, 2, 3, 1, 4, 5, 6] : List (Fin 7)).Perm (List.finRange 7) := by
  decide

/-- The elimination order of `E₆` lists every vertex once. -/
private theorem perm_finRange_E6 :
    ([0, 2, 3, 1, 4, 5] : List (Fin 6)).Perm (List.finRange 6) := by
  decide

/-- The elimination order of `F₄` lists every vertex once. -/
private theorem perm_finRange_F4 :
    ([0, 1, 2, 3] : List (Fin 4)).Perm (List.finRange 4) := by
  decide

/-- The elimination order of `G₂` lists every vertex once. -/
private theorem perm_finRange_G2 :
    ([0, 1] : List (Fin 2)).Perm (List.finRange 2) := by
  decide

/-! ### Independence of the ordering -/

/-- The characteristic polynomial of any Coxeter element of a base of Cartan type `t`, with standard
Cartan matrix `A`, is that of `coxeterElement A` when the diagram of `t` has an elimination
order. -/
theorem charpoly_of_isElimOrder_of_hasCartanType_of_actsBy [DecidableEq ι] {t : DynkinType}
    {A : Matrix (Fin t.rank) (Fin t.rank) ℤ} (ht : t.cartanMatrix = A) {S₀ : List (Fin t.rank)}
    (hel₀ : List.IsElimOrder (fun i j => A i j ≠ 0) S₀)
    (hperm₀ : S₀.Perm (List.finRange t.rank)) {b : P.Base} (h : HasCartanType P b t)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) : W.charpoly = (coxeterElement A).charpoly := by
  subst ht
  obtain ⟨e, hA⟩ := (hasCartanType_iff b t).1 h
  obtain ⟨S, hndS, hel, hlS, hτS⟩ :=
    Base.exists_isElimOrder_of_cartanMatrix_eq b _ e hA S₀ hel₀ hperm₀ hnd hall
  rw [hW.unique (b.actsBy_wordProd l),
    b.charpoly_prod_reflMatrix_eq_of_isElimOrder hndS hel hlS hτS, b.prod_reflMatrix_eq _ e hA,
    coe_reindexAlgEquiv, charpoly_reindex]

/-- Any Coxeter element of a base of Cartan type `t`, with standard Cartan matrix `A`, has the
order of `coxeterElement A` when the diagram of `t` has an elimination order. -/
theorem orderOf_wordProd_of_isElimOrder_of_hasCartanType [Finite ι] {t : DynkinType}
    {A : Matrix (Fin t.rank) (Fin t.rank) ℤ} (ht : t.cartanMatrix = A) {S₀ : List (Fin t.rank)}
    (hel₀ : List.IsElimOrder (fun i j => A i j ≠ 0) S₀)
    (hperm₀ : S₀.Perm (List.finRange t.rank)) {b : P.Base} (h : HasCartanType P b t)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = orderOf (coxeterElement A) := by
  subst ht
  obtain ⟨e, hA⟩ := (hasCartanType_iff b t).1 h
  obtain ⟨S, hndS, hel, hlS, hτS⟩ :=
    Base.exists_isElimOrder_of_cartanMatrix_eq b _ e hA S₀ hel₀ hperm₀ hnd hall
  rw [b.orderOf_wordProd_eq_of_isElimOrder hndS hel hlS hτS,
    b.orderOf_wordProd_of_cartanMatrix_eq _ e hA]

/-! ### The exceptional types -/

variable {b : P.Base} {l : List b.support}

/-- **Every Coxeter element of a base of type `E₆` has order 12.** -/
theorem orderOf_wordProd_of_hasCartanType_E6 [Finite ι] (h : HasCartanType P b .E6) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 12 :=
  (orderOf_wordProd_of_isElimOrder_of_hasCartanType (t := .E6)
    DynkinType.cartanMatrix_E6 isElimOrder_E6 perm_finRange_E6 h hnd
    hall).trans orderOf_coxE6

/-- **Every Coxeter element of a base of type `E₇` has order 18.** -/
theorem orderOf_wordProd_of_hasCartanType_E7 [Finite ι] (h : HasCartanType P b .E7) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 18 :=
  (orderOf_wordProd_of_isElimOrder_of_hasCartanType (t := .E7)
    DynkinType.cartanMatrix_E7 isElimOrder_E7 perm_finRange_E7 h hnd
    hall).trans orderOf_coxE7

/-- **Every Coxeter element of a base of type `E₈` has order 30.** -/
theorem orderOf_wordProd_of_hasCartanType_E8 [Finite ι] (h : HasCartanType P b .E8) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 30 :=
  (orderOf_wordProd_of_isElimOrder_of_hasCartanType (t := .E8)
    DynkinType.cartanMatrix_E8 isElimOrder_E8 perm_finRange_E8 h hnd
    hall).trans orderOf_coxE8

/-- **Every Coxeter element of a base of type `F₄` has order 12.** -/
theorem orderOf_wordProd_of_hasCartanType_F4 [Finite ι] (h : HasCartanType P b .F4) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 12 :=
  (orderOf_wordProd_of_isElimOrder_of_hasCartanType (t := .F4)
    DynkinType.cartanMatrix_F4 isElimOrder_F4 perm_finRange_F4 h hnd
    hall).trans orderOf_coxF4

/-- **Every Coxeter element of a base of type `G₂` has order 6.** -/
theorem orderOf_wordProd_of_hasCartanType_G2 [Finite ι] (h : HasCartanType P b .G2) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = 6 :=
  (orderOf_wordProd_of_isElimOrder_of_hasCartanType (t := .G2)
    DynkinType.cartanMatrix_G2 isElimOrder_G2 perm_finRange_G2 h hnd
    hall).trans orderOf_coxG2

/-- **Every Coxeter element of a base of type `E₆`** has characteristic polynomial `Φ₁₂ Φ₃` on the
simple roots. -/
theorem charpoly_of_hasCartanType_E6_of_actsBy [DecidableEq ι] (h : HasCartanType P b .E6)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 12 ℤ * Polynomial.cyclotomic 3 ℤ :=
  (charpoly_of_isElimOrder_of_hasCartanType_of_actsBy (t := .E6)
    DynkinType.cartanMatrix_E6 isElimOrder_E6 perm_finRange_E6 h hnd
    hall hW).trans charpoly_coxE6

/-- **Every Coxeter element of a base of type `E₇`** has characteristic polynomial `Φ₁₈ Φ₂` on the
simple roots. -/
theorem charpoly_of_hasCartanType_E7_of_actsBy [DecidableEq ι] (h : HasCartanType P b .E7)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 18 ℤ * Polynomial.cyclotomic 2 ℤ :=
  (charpoly_of_isElimOrder_of_hasCartanType_of_actsBy (t := .E7)
    DynkinType.cartanMatrix_E7 isElimOrder_E7 perm_finRange_E7 h hnd
    hall hW).trans charpoly_coxE7

/-- **Every Coxeter element of a base of type `E₈`** has characteristic polynomial `Φ₃₀` on the
simple roots. -/
theorem charpoly_of_hasCartanType_E8_of_actsBy [DecidableEq ι] (h : HasCartanType P b .E8)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 30 ℤ :=
  (charpoly_of_isElimOrder_of_hasCartanType_of_actsBy (t := .E8)
    DynkinType.cartanMatrix_E8 isElimOrder_E8 perm_finRange_E8 h hnd
    hall hW).trans charpoly_coxE8

/-- **Every Coxeter element of a base of type `F₄`** has characteristic polynomial `Φ₁₂` on the
simple roots. -/
theorem charpoly_of_hasCartanType_F4_of_actsBy [DecidableEq ι] (h : HasCartanType P b .F4)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 12 ℤ :=
  (charpoly_of_isElimOrder_of_hasCartanType_of_actsBy (t := .F4)
    DynkinType.cartanMatrix_F4 isElimOrder_F4 perm_finRange_F4 h hnd
    hall hW).trans charpoly_coxF4

/-- **Every Coxeter element of a base of type `G₂`** has characteristic polynomial `Φ₆` on the
simple roots. -/
theorem charpoly_of_hasCartanType_G2_of_actsBy [DecidableEq ι] (h : HasCartanType P b .G2)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 6 ℤ :=
  (charpoly_of_isElimOrder_of_hasCartanType_of_actsBy (t := .G2)
    DynkinType.cartanMatrix_G2 isElimOrder_G2 perm_finRange_G2 h hnd
    hall hW).trans charpoly_coxG2

end TauCeti.Coxeter

end
