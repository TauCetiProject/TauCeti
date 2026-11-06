/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.Algebra.BigOperators.Group.List
public import TauCeti.Data.List.ElimOrder
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Moves on words in the simple reflections

The two moves that relate the Coxeter elements of a forest Dynkin diagram.

* **Commutation.** `RootPairing.Base.wordProd_eq_of_perm`: two orderings of the same simple
  reflections spell the same element if the inverted pairs are orthogonal, i.e. have Cartan entry
  zero. This specializes `List.prod_map_eq_of_perm`.
* **Cyclic shift.** `RootPairing.Base.orderOf_wordProd_cons_eq`: moving the first letter of a word
  to the end does not change the order of its product, since `s w` and `w s` are conjugate.

For a forest, every ordering of the simple reflections is reached from any other by these moves:
this is the content of `List.eq_of_isElimOrder`.

## Main results

* `RootPairing.Base.wordProd_eq_of_commEquiv`: commuting non-adjacent letters does not change the
  element a word spells.
* `RootPairing.Base.orderOf_wordProd_eq_of_isElimOrder`: for a base whose Dynkin diagram has an
  elimination order, all Coxeter elements have the same order.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16.
-/

public section

open TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **Commutation move.** Two orderings of the same simple reflections spell the same Weyl-group
element if every pair whose relative order differs is orthogonal (Cartan entry zero). -/
theorem wordProd_eq_of_perm [P.IsCrystallographic] [IsDomain R] [CharZero R] (b : P.Base)
    {l l' : List b.support}
    (hp : l.Perm l')
    (h : ∀ x y, List.Sublist [x, y] l → List.Sublist [y, x] l' → b.cartanMatrix x y = 0) :
    wordProd P b l = wordProd P b l' := by
  rw [wordProd_def, wordProd_def]
  refine List.prod_map_eq_of_perm _ hp fun x y hxy hyx => ?_
  have hxy0 := h x y hxy hyx
  exact weylGroup.commute_ofIdx_of_isOrthogonal P
    ⟨b.cartanMatrix_apply_eq_zero_iff_pairing.1 hxy0,
      b.cartanMatrix_apply_eq_zero_iff_pairing.1 (b.cartanMatrix_apply_eq_zero_iff_symm.1 hxy0)⟩

/-- **Cyclic-shift move.** Moving the first simple reflection of a word to the end conjugates its
product, so the order is unchanged. -/
theorem orderOf_wordProd_cons_eq (b : P.Base) (i : b.support) (l : List b.support) :
    orderOf (wordProd P b (i :: l)) = orderOf (wordProd P b (l ++ [i])) := by
  rw [wordProd_cons, wordProd_append, wordProd_cons,
    wordProd_nil, mul_one]
  exact SemiconjBy.orderOf_eq (wordProd P b l) (mul_assoc _ _ _).symm

/-- Commuting non-adjacent letters of a word does not change the element it spells. -/
theorem wordProd_eq_of_commEquiv [P.IsCrystallographic] [IsDomain R] [CharZero R] (b : P.Base)
    {l l' : List b.support} (hce : List.CommEquiv (fun x y => b.cartanMatrix x y ≠ 0) l l') :
    wordProd P b l = wordProd P b l' := by
  obtain ⟨hp, h⟩ := List.commEquiv_iff.1 hce
  exact wordProd_eq_of_perm b hp fun x y hxy hyx => not_not.1 (h x y hxy hyx)

/-- **All Coxeter elements have the same order** when the Dynkin diagram of the base has an
elimination order. -/
theorem orderOf_wordProd_eq_of_isElimOrder [P.IsCrystallographic] [IsDomain R] [CharZero R]
    (b : P.Base) {S : List b.support} (hnd : S.Nodup)
    (hel : List.IsElimOrder (fun x y => b.cartanMatrix x y ≠ 0) S) {l l' : List b.support}
    (hl : l.Perm S) (hl' : l'.Perm S) :
    orderOf (wordProd P b l) = orderOf (wordProd P b l') :=
  List.eq_of_isElimOrder (fun _ _ h h' => h (b.cartanMatrix_apply_eq_zero_iff_symm.2 h')) hnd hel
    (fun l => orderOf (wordProd P b l))
    (fun _ _ _ hce => congrArg orderOf (wordProd_eq_of_commEquiv b hce))
    (fun a t _ => orderOf_wordProd_cons_eq b a t) hl hl'

end RootPairing.Base

end
