/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Connect
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.DynkinType

/-!
# Every Coxeter element of an exceptional type has order the Coxeter number

A *Coxeter element* is a product of all the simple reflections, each once, in any order. The Dynkin
diagrams `E₆`, `E₇`, `E₈`, `F₄`, `G₂` are trees, so their vertices admit an elimination order
(checked by `decide`), and `TauCeti.Coxeter.eq_of_isElimOrder` shows that the order of the product
does not depend on the ordering.

## Main results

* `TauCeti.Coxeter.orderOf_wordProd_eq_of_isElimOrder`: for a base whose Dynkin diagram has an
  elimination order, all Coxeter elements have the same order.
* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_E8` (and `E7`, `E6`, `F4`, `G2`): **every**
  Coxeter element of a base of type `E₈` has order 30 (and 18, 12, 12, 6).
-/

@[expose] public section

open Matrix RootPairing TauCeti

namespace TauCeti.Coxeter

section ElimOrder

variable {α β : Type*} {adj : α → α → Prop}

theorem isElimOrder_nil : IsElimOrder adj [] := fun S₁ z S₂ h => by simp at h

theorem IsElimOrder.append_singleton {S : List α} {z : α} (h : IsElimOrder adj S)
    (hz : ∀ x ∈ S, ∀ y ∈ S, adj z x → adj z y → x = y) : IsElimOrder adj (S ++ [z]) := by
  intro S₁ w S₂ hS
  rcases List.eq_nil_or_concat S₂ with rfl | ⟨L, c, rfl⟩
  · obtain ⟨rfl, hzw⟩ := List.append_inj' hS rfl
    obtain rfl : z = w := by simpa using hzw
    exact hz
  · have hS' : S ++ [z] = (S₁ ++ w :: L) ++ [c] := by rw [hS]; simp
    exact h S₁ w L (List.append_inj' hS' rfl).1

theorem IsElimOrder.map_equiv {adj' : β → β → Prop} {S : List β} (h : IsElimOrder adj' S)
    (e : α ≃ β) : IsElimOrder (fun x y => adj' (e x) (e y)) (S.map e.symm) := by
  intro S₁ z S₂ hS x hx y hy hxz hyz
  have hS' : S = S₁.map e ++ e z :: S₂.map e := by
    simpa [List.map_map] using congrArg (List.map e) hS
  exact e.injective (h _ _ _ hS' (e x) (List.mem_map_of_mem hx) (e y) (List.mem_map_of_mem hy)
    hxz hyz)

end ElimOrder

/-! ### Elimination orders of the exceptional diagrams (Bourbaki numbering, from 0) -/

theorem isElimOrder_E8 :
    IsElimOrder (fun i j : Fin 8 => CartanMatrix.E 8 i j ≠ 0) [0, 2, 3, 1, 4, 5, 6, 7] :=
  ((((((((isElimOrder_nil.append_singleton (z := 0) (by decide)).append_singleton (z := 2)
    (by decide)).append_singleton (z := 3) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 4) (by decide)).append_singleton (z := 5)
    (by decide)).append_singleton (z := 6) (by decide)).append_singleton (z := 7) (by decide))

theorem isElimOrder_E7 :
    IsElimOrder (fun i j : Fin 7 => CartanMatrix.E 7 i j ≠ 0) [0, 2, 3, 1, 4, 5, 6] :=
  (((((((isElimOrder_nil.append_singleton (z := 0) (by decide)).append_singleton (z := 2)
    (by decide)).append_singleton (z := 3) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 4) (by decide)).append_singleton (z := 5)
    (by decide)).append_singleton (z := 6) (by decide))

theorem isElimOrder_E6 :
    IsElimOrder (fun i j : Fin 6 => CartanMatrix.E 6 i j ≠ 0) [0, 2, 3, 1, 4, 5] :=
  ((((((isElimOrder_nil.append_singleton (z := 0) (by decide)).append_singleton (z := 2)
    (by decide)).append_singleton (z := 3) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 4) (by decide)).append_singleton (z := 5) (by decide))

theorem isElimOrder_F4 :
    IsElimOrder (fun i j : Fin 4 => CartanMatrix.F₄ i j ≠ 0) [0, 1, 2, 3] :=
  ((((isElimOrder_nil.append_singleton (z := 0) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 2) (by decide)).append_singleton (z := 3) (by decide))

theorem isElimOrder_G2 :
    IsElimOrder (fun i j : Fin 2 => CartanMatrix.G₂.transpose i j ≠ 0) [0, 1] :=
  ((isElimOrder_nil.append_singleton (z := 0) (by decide)).append_singleton (z := 1) (by decide))

/-! ### Independence of the ordering -/

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]

/-- **All Coxeter elements have the same order** when the Dynkin diagram of the base has an
elimination order (i.e. is a forest). -/
theorem orderOf_wordProd_eq_of_isElimOrder (b : P.Base) {S : List b.support} (hnd : S.Nodup)
    (hel : IsElimOrder (fun x y => b.cartanMatrix x y ≠ 0) S) {l l' : List b.support}
    (hl : l.Perm S) (hl' : l'.Perm S) :
    orderOf (wordProd P b l) = orderOf (wordProd P b l') :=
  eq_of_isElimOrder (fun _ _ h h' => h (b.cartanMatrix_apply_eq_zero_iff_symm.2 h')) hnd hel
    (fun l => orderOf (wordProd P b l))
    (fun _ _ _ hce => congrArg orderOf
      (wordProd_eq_of_perm b hce.1 fun x y hxy hyx => not_not.1 (hce.2 x y hxy hyx)))
    (fun a t _ => orderOf_wordProd_cons_eq b a t) hl hl'

omit [IsDomain R] [CharZero R] in
/-- Transport of an elimination order of a standard Cartan matrix to a base of that type: any
Coxeter element and the one in the numbering order are orderings of a common elimination order. -/
theorem exists_isElimOrder_of_cartanMatrix_eq {n : ℕ} (b : P.Base) (A : Matrix (Fin n) (Fin n) ℤ)
    (e : b.support ≃ Fin n) (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) (S₀ : List (Fin n))
    (hel₀ : IsElimOrder (fun i j : Fin n => A i j ≠ 0) S₀) (hperm₀ : S₀.Perm (List.finRange n))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    ∃ S : List b.support, S.Nodup ∧ IsElimOrder (fun x y => b.cartanMatrix x y ≠ 0) S ∧
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

theorem orderOf_wordProd_eq_of_cartanMatrix_eq_of_isElimOrder {n : ℕ} (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (e : b.support ≃ Fin n) (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) (S₀ : List (Fin n))
    (hel₀ : IsElimOrder (fun i j : Fin n => A i j ≠ 0) S₀) (hperm₀ : S₀.Perm (List.finRange n))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = orderOf (wordProd P b ((List.finRange n).map e.symm)) := by
  obtain ⟨S, hndS, hel, hlS, hτS⟩ :=
    exists_isElimOrder_of_cartanMatrix_eq b A e hA S₀ hel₀ hperm₀ hnd hall
  exact orderOf_wordProd_eq_of_isElimOrder b hndS hel hlS hτS

/-- **All Coxeter elements have the same characteristic polynomial** (of their matrices on the
simple roots) when the Dynkin diagram of the base has an elimination order. -/
theorem charpoly_prod_reflMatrix_eq_of_isElimOrder [DecidableEq ι] (b : P.Base)
    {S : List b.support} (hnd : S.Nodup)
    (hel : IsElimOrder (fun x y => b.cartanMatrix x y ≠ 0) S) {l l' : List b.support}
    (hl : l.Perm S) (hl' : l'.Perm S) :
    ((l.map (reflMatrix b.cartanMatrix)).prod).charpoly =
      ((l'.map (reflMatrix b.cartanMatrix)).prod).charpoly :=
  eq_of_isElimOrder (fun _ _ h h' => h (b.cartanMatrix_apply_eq_zero_iff_symm.2 h')) hnd hel
    (fun l => ((l.map (reflMatrix b.cartanMatrix)).prod).charpoly)
    (fun l l' _ hce => by
      have hw : wordProd P b l = wordProd P b l' :=
        wordProd_eq_of_perm b hce.1 fun x y hxy hyx => not_not.1 (hce.2 x y hxy hyx)
      have hl' : ActsBy b (wordProd P b l) ((l'.map (reflMatrix b.cartanMatrix)).prod) := by
        rw [hw]; exact actsBy_wordProd b l'
      rw [eq_of_actsBy_of_actsBy (actsBy_wordProd b l) hl'])
    (fun a t _ => by
      simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_nil, mul_one]
      exact charpoly_mul_comm _ _)
    hl hl'

/-- The characteristic polynomial of any Coxeter element of a base whose Cartan matrix is `A`
(up to relabelling, with an elimination order) is that of `coxeterElement A`. -/
theorem charpoly_of_actsBy_of_elim [DecidableEq ι] {n : ℕ} (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : b.support ≃ Fin n)
    (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) (S₀ : List (Fin n))
    (hel₀ : IsElimOrder (fun i j : Fin n => A i j ≠ 0) S₀) (hperm₀ : S₀.Perm (List.finRange n))
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) : W.charpoly = (coxeterElement A).charpoly := by
  obtain ⟨S, hndS, hel, hlS, hτS⟩ :=
    exists_isElimOrder_of_cartanMatrix_eq b A e hA S₀ hel₀ hperm₀ hnd hall
  rw [eq_of_actsBy_of_actsBy hW (actsBy_wordProd b l),
    charpoly_prod_reflMatrix_eq_of_isElimOrder b hndS hel hlS hτS, prod_reflMatrix_eq b A e hA,
    coe_reindexAlgEquiv, charpoly_reindex]

variable [Finite ι]

/-- **Every Coxeter element of a base of type `E₈` has order 30.** -/
theorem orderOf_wordProd_of_hasCartanType_E8 {b : P.Base} (h : HasCartanType P b .E8)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 30 := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 8 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.E8.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_E8] at hA
  rw [orderOf_wordProd_eq_of_cartanMatrix_eq_of_isElimOrder b _ e hA _ isElimOrder_E8 (by decide)
    hnd hall]
  exact orderOf_coxeterElement_E8 b e hA

/-- **Every Coxeter element of a base of type `E₇` has order 18.** -/
theorem orderOf_wordProd_of_hasCartanType_E7 {b : P.Base} (h : HasCartanType P b .E7)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 18 := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 7 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.E7.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_E7] at hA
  rw [orderOf_wordProd_eq_of_cartanMatrix_eq_of_isElimOrder b _ e hA _ isElimOrder_E7 (by decide)
    hnd hall]
  exact orderOf_coxeterElement_E7 b e hA

/-- **Every Coxeter element of a base of type `E₆` has order 12.** -/
theorem orderOf_wordProd_of_hasCartanType_E6 {b : P.Base} (h : HasCartanType P b .E6)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 12 := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 6 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.E6.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_E6] at hA
  rw [orderOf_wordProd_eq_of_cartanMatrix_eq_of_isElimOrder b _ e hA _ isElimOrder_E6 (by decide)
    hnd hall]
  exact orderOf_coxeterElement_E6 b e hA

/-- **Every Coxeter element of a base of type `F₄` has order 12.** -/
theorem orderOf_wordProd_of_hasCartanType_F4 {b : P.Base} (h : HasCartanType P b .F4)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 12 := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 4 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.F4.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_F4] at hA
  rw [orderOf_wordProd_eq_of_cartanMatrix_eq_of_isElimOrder b _ e hA _ isElimOrder_F4 (by decide)
    hnd hall]
  exact orderOf_coxeterElement_F4 b e hA

/-- **Every Coxeter element of a base of type `G₂` has order 6.** -/
theorem orderOf_wordProd_of_hasCartanType_G2 {b : P.Base} (h : HasCartanType P b .G2)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 6 := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 2 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.G2.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_G2] at hA
  rw [orderOf_wordProd_eq_of_cartanMatrix_eq_of_isElimOrder b _ e hA _ isElimOrder_G2 (by decide)
    hnd hall,
    orderOf_wordProd_of_cartanMatrix_eq b _ e hA]
  exact orderOf_coxG2_transpose

/-! ### Characteristic polynomial of every Coxeter element -/

omit [Finite ι] in
/-- **Every Coxeter element of a base of type `E₈`** has characteristic polynomial
`cyclotomic 30` on the simple roots. -/
theorem charpoly_of_actsBy_of_hasCartanType_E8 [DecidableEq ι] {b : P.Base}
    (h : HasCartanType P b .E8) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : ActsBy b (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 30 ℤ := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 8 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.E8.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_E8] at hA
  rw [charpoly_of_actsBy_of_elim b _ e hA _ isElimOrder_E8 (by decide) hnd hall hW]
  exact charpoly_coxE8

omit [Finite ι] in
/-- **Every Coxeter element of a base of type `E₇`** has characteristic polynomial
`cyclotomic 18 * cyclotomic 2` on the simple roots. -/
theorem charpoly_of_actsBy_of_hasCartanType_E7 [DecidableEq ι] {b : P.Base}
    (h : HasCartanType P b .E7) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : ActsBy b (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 18 ℤ * Polynomial.cyclotomic 2 ℤ := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 7 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.E7.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_E7] at hA
  rw [charpoly_of_actsBy_of_elim b _ e hA _ isElimOrder_E7 (by decide) hnd hall hW]
  exact charpoly_coxE7

omit [Finite ι] in
/-- **Every Coxeter element of a base of type `E₆`** has characteristic polynomial
`cyclotomic 12 * cyclotomic 3` on the simple roots. -/
theorem charpoly_of_actsBy_of_hasCartanType_E6 [DecidableEq ι] {b : P.Base}
    (h : HasCartanType P b .E6) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : ActsBy b (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 12 ℤ * Polynomial.cyclotomic 3 ℤ := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 6 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.E6.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_E6] at hA
  rw [charpoly_of_actsBy_of_elim b _ e hA _ isElimOrder_E6 (by decide) hnd hall hW]
  exact charpoly_coxE6

omit [Finite ι] in
/-- **Every Coxeter element of a base of type `F₄`** has characteristic polynomial
`cyclotomic 12` on the simple roots. -/
theorem charpoly_of_actsBy_of_hasCartanType_F4 [DecidableEq ι] {b : P.Base}
    (h : HasCartanType P b .F4) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : ActsBy b (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 12 ℤ := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 4 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.F4.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_F4] at hA
  rw [charpoly_of_actsBy_of_elim b _ e hA _ isElimOrder_F4 (by decide) hnd hall hW]
  exact charpoly_coxF4

omit [Finite ι] in
/-- **Every Coxeter element of a base of type `G₂`** has characteristic polynomial
`cyclotomic 6` on the simple roots. -/
theorem charpoly_of_actsBy_of_hasCartanType_G2 [DecidableEq ι] {b : P.Base}
    (h : HasCartanType P b .G2) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : ActsBy b (wordProd P b l) W) :
    W.charpoly = Polynomial.cyclotomic 6 ℤ := by
  obtain ⟨e₀, hA₀⟩ := (hasCartanType_iff b _).1 h
  let e : b.support ≃ Fin 2 := e₀
  have hA : ∀ i j, b.cartanMatrix i j = DynkinType.G2.cartanMatrix (e i) (e j) := hA₀
  simp only [DynkinType.cartanMatrix_G2] at hA
  rw [charpoly_of_actsBy_of_elim b _ e hA _ isElimOrder_G2 (by decide) hnd hall hW]
  exact charpoly_coxG2_transpose

end TauCeti.Coxeter

end
