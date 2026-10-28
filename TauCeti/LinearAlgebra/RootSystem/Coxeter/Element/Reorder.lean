/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Moves on words in the simple reflections

The two moves that relate the Coxeter elements of a forest Dynkin diagram.

* **Commutation.** `TauCeti.Coxeter.prod_map_eq_of_perm`: two orderings of the same letters have the
  same product in any monoid if every pair of letters whose relative order differs commutes. For
  words in the simple reflections, `TauCeti.Coxeter.wordProd_eq_of_perm` asks the inverted pairs to
  be orthogonal, i.e. to have Cartan entry zero.
* **Cyclic shift.** `TauCeti.Coxeter.orderOf_wordProd_cons_eq`: moving the first letter of a word to
  the end does not change the order of its product, since `s w` and `w s` are conjugate.

That for a forest every ordering of the simple reflections is reached from any other by these moves
is `TauCeti.Coxeter.eq_of_isElimOrder`.
-/

@[expose] public section

open RootPairing

namespace TauCeti.Coxeter

/-- Two orderings of the same letters have the same product if every pair of letters whose
relative order differs commutes. -/
theorem prod_map_eq_of_perm {α G : Type*} [Monoid G] (f : α → G) {l l' : List α}
    (hp : l.Perm l')
    (h : ∀ x y, List.Sublist [x, y] l → List.Sublist [y, x] l' → Commute (f x) (f y)) :
    (l.map f).prod = (l'.map f).prod := by
  induction l generalizing l' with
  | nil => rw [List.nil_perm.1 hp]
  | cons a t ih =>
    obtain ⟨u, v, rfl⟩ := List.append_of_mem (hp.subset List.mem_cons_self)
    have hp' : t.Perm (u ++ v) := (hp.trans List.perm_middle).cons_inv
    have hcomm : ∀ x ∈ u.map f, Commute (f a) x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have hyt : y ∈ t := hp'.symm.subset (List.mem_append_left v hy)
      refine h a y (List.cons_sublist_cons.2 (List.singleton_sublist.2 hyt)) ?_
      exact (List.singleton_sublist.2 hy).append (List.singleton_sublist.2 List.mem_cons_self)
    have key : ((u ++ a :: v).map f).prod = f a * ((u ++ v).map f).prod := by
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
      rw [← mul_assoc, ← (Commute.list_prod_right _ _ hcomm).eq, mul_assoc]
    rw [List.map_cons, List.prod_cons, key,
      ih hp' fun x y hxy hyx => h x y (hxy.trans (List.sublist_cons_self a t))
        (hyx.trans ((List.sublist_cons_self a v).append_left u))]

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

theorem wordProd_eq_prod_map (b : P.Base) (l : List b.support) :
    TauCeti.wordProd P b l = (l.map fun i : b.support => weylGroup.ofIdx P (i : ι)).prod := by
  induction l with
  | nil => simp [TauCeti.wordProd_nil]
  | cons i l ih => rw [TauCeti.wordProd_cons, ih, List.map_cons, List.prod_cons]

/-- **Commutation move.** Two orderings of the same simple reflections spell the same Weyl-group
element if every pair whose relative order differs is orthogonal (Cartan entry zero). -/
theorem wordProd_eq_of_perm [P.IsCrystallographic] [IsDomain R] [CharZero R] (b : P.Base)
    {l l' : List b.support}
    (hp : l.Perm l')
    (h : ∀ x y, List.Sublist [x, y] l → List.Sublist [y, x] l' → b.cartanMatrix x y = 0) :
    TauCeti.wordProd P b l = TauCeti.wordProd P b l' := by
  rw [wordProd_eq_prod_map, wordProd_eq_prod_map]
  refine prod_map_eq_of_perm _ hp fun x y hxy hyx => ?_
  have hxy0 := h x y hxy hyx
  exact weylGroup.commute_ofIdx_of_isOrthogonal P
    ⟨b.cartanMatrix_apply_eq_zero_iff_pairing.1 hxy0,
      b.cartanMatrix_apply_eq_zero_iff_pairing.1 (b.cartanMatrix_apply_eq_zero_iff_symm.1 hxy0)⟩

/-- **Cyclic-shift move.** Moving the first simple reflection of a word to the end conjugates its
product, so the order is unchanged. -/
theorem orderOf_wordProd_cons_eq (b : P.Base) (i : b.support) (l : List b.support) :
    orderOf (TauCeti.wordProd P b (i :: l)) = orderOf (TauCeti.wordProd P b (l ++ [i])) := by
  rw [TauCeti.wordProd_cons, TauCeti.wordProd_append, TauCeti.wordProd_cons,
    TauCeti.wordProd_nil, mul_one]
  exact SemiconjBy.orderOf_eq (TauCeti.wordProd P b l) (mul_assoc _ _ _).symm

/-- In a list without duplicates, two letters cannot occur in both orders. -/
theorem eq_of_sublist_pair_of_sublist_pair {α : Type*} {l : List α} (hnd : l.Nodup) {x y : α}
    (hxy : List.Sublist [x, y] l) (hyx : List.Sublist [y, x] l) : x = y := by
  induction l with
  | nil => simp at hxy
  | cons c m ih =>
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.1 hxy with hxy' | ⟨r, hr, -⟩ <;>
      rcases List.sublist_cons_iff.1 hyx with hyx' | ⟨s, hs, -⟩
    · exact ih hnd.2 hxy' hyx'
    · obtain ⟨rfl, -⟩ := List.cons.inj hs
      exact absurd (hxy'.subset (by simp)) hnd.1
    · obtain ⟨rfl, -⟩ := List.cons.inj hr
      exact absurd (hyx'.subset (by simp)) hnd.1
    · exact (List.cons.inj hr).1.trans (List.cons.inj hs).1.symm

/-- **Source move, first half.** If every simple reflection before `a` in a duplicate-free word is
orthogonal to `a` (so `a` is a source of the orientation the word induces on the Dynkin diagram),
moving `a` to the front does not change the product. -/
theorem wordProd_eq_cons_erase [DecidableEq ι] [P.IsCrystallographic] [IsDomain R] [CharZero R]
    (b : P.Base) {l : List b.support} (hnd : l.Nodup) {a : b.support} (ha : a ∈ l)
    (hsrc : ∀ x, List.Sublist [x, a] l → b.cartanMatrix x a = 0) :
    TauCeti.wordProd P b l = TauCeti.wordProd P b (a :: l.erase a) := by
  refine wordProd_eq_of_perm b (List.perm_cons_erase ha) fun x y hxy hyx => ?_
  rcases List.sublist_cons_iff.1 hyx with hyx' | ⟨r, hr, -⟩
  · obtain rfl := eq_of_sublist_pair_of_sublist_pair hnd hxy (hyx'.trans List.erase_sublist)
    exact absurd hxy (List.nodup_iff_sublist.1 hnd x)
  · obtain ⟨rfl, -⟩ := List.cons.inj hr
    exact hsrc x hxy

/-- **Source move.** Moving a source `a` of a duplicate-free word to the end does not change the
order of its product. On orientations of the Dynkin diagram this turns the source `a` into a
sink. -/
theorem orderOf_wordProd_eq_of_source [DecidableEq ι] [P.IsCrystallographic] [IsDomain R]
    [CharZero R] (b : P.Base) {l : List b.support} (hnd : l.Nodup) {a : b.support} (ha : a ∈ l)
    (hsrc : ∀ x, List.Sublist [x, a] l → b.cartanMatrix x a = 0) :
    orderOf (TauCeti.wordProd P b l) = orderOf (TauCeti.wordProd P b (l.erase a ++ [a])) := by
  rw [wordProd_eq_cons_erase b hnd ha hsrc, orderOf_wordProd_cons_eq]

end TauCeti.Coxeter

end
