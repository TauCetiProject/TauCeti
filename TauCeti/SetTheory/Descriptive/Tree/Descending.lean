/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Tree
import Mathlib.Data.List.ChainOfFn

/-!
# The descending tree of a relation

For a relation `r` on a type `α`, the **descending tree** `Descriptive.Tree.descendingTree r` is
the descriptive tree of finite sequences `[a₀, a₁, …, aₙ]` with `r aᵢ₊₁ aᵢ` for each `i`. Its
infinite branches are the infinite `r`-descending sequences, so it is well-founded exactly when `r`
is. Below a node, the tree depends only on the last entry of the node. When `r` is well-founded,
the rank of the tree below a node is the successor of the `r`-rank of the node's last entry, and
the rank of the whole tree is the successor of the supremum of the successors of the `r`-ranks; for
a well-order the order type is therefore at most the rank of the tree. The empty sequence always
lies in the tree, so even on an empty carrier its rank is `1`.

No countability of the carrier is assumed. Combined with the analytic boundedness theorem for
families of well-founded trees, this bounds the order types of analytic families of well-orders.

## Main definitions

* `Descriptive.Tree.descendingTree`: the tree of finite `r`-descending sequences.

## Main results

* `Descriptive.Tree.isWellFounded_descendingTree_iff`: the descending tree is well-founded exactly
  when `r` is.
* `Descriptive.Tree.rank_subAt_descendingTree_singleton`: when `r` is well-founded, the rank below
  `x` is the successor of the `r`-rank of `x`.
* `Descriptive.Tree.rank_descendingTree`: the rank of the descending tree of a well-founded
  relation.
* `Descriptive.Tree.type_le_rank_descendingTree`: for a well-order, the order type is at most the
  rank of the descending tree.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Section 2.E (well-founded trees and their ranks).
-/

public section

universe u

namespace Descriptive.Tree


variable {α : Type u} (r : α → α → Prop)

/-- The **descending tree** of a relation `r`: the finite sequences whose consecutive entries
descend, each entry `r`-related to the one before, `r aᵢ₊₁ aᵢ`. -/
def descendingTree : tree α :=
  ⟨{l | l.IsChain fun a b => r b a}, fun _ _ h => List.IsChain.left_of_append h⟩

variable {r}

/-- A list lies in the descending tree when each entry is `r`-related to the one before. -/
@[simp]
theorem mem_descendingTree {l : List α} : l ∈ descendingTree r ↔ l.IsChain fun a b => r b a :=
  Iff.rfl

/-- The empty sequence lies in every descending tree, whatever the carrier. -/
theorem nil_mem_descendingTree : [] ∈ descendingTree r :=
  List.isChain_nil

/-- Every one-term sequence lies in the descending tree. -/
theorem singleton_mem_descendingTree (x : α) : [x] ∈ descendingTree r :=
  List.isChain_singleton x

/-- A sequence is a branch of the descending tree exactly when it is `r`-descending. -/
theorem forall_ofFn_mem_descendingTree_iff (f : ℕ → α) :
    (∀ n, List.ofFn (fun i : Fin n => f i) ∈ descendingTree r) ↔ ∀ n, r (f (n + 1)) (f n) := by
  simp only [mem_descendingTree, List.isChain_ofFn]
  exact ⟨fun H n => H (n + 2) n (by omega), fun H _ i _ => H i⟩

/-- **The descending tree is well-founded exactly when `r` is**: a branch is an infinite
`r`-descending sequence. -/
theorem isWellFounded_descendingTree_iff : IsWellFounded (descendingTree r) ↔ WellFounded r := by
  rw [wellFounded_iff_isEmpty_descending_chain, ← not_iff_not, not_isWellFounded_iff,
    not_isEmpty_iff, nonempty_subtype]
  exact exists_congr forall_ofFn_mem_descendingTree_iff

/-- Below a node, the descending tree depends only on the node's last entry. -/
theorem subAt_descendingTree_append_singleton {l : List α} {x : α}
    (h : l ++ [x] ∈ descendingTree r) :
    subAt (descendingTree r) (l ++ [x]) = subAt (descendingTree r) [x] := by
  ext y
  simp only [mem_subAt, mem_descendingTree] at h ⊢
  rw [List.isChain_append (l₁ := l ++ [x]), List.isChain_append (l₁ := [x])]
  simp [h]

/-- When `r` is well-founded, the rank of the descending tree below `x` is the successor of the
`r`-rank of `x`. -/
theorem rank_subAt_descendingTree_singleton [hr : WellFounded r] (x : α) :
    rank (subAt (descendingTree r) [x]) = Order.succ (WellFounded.rank r x) := by
  have hT : IsWellFounded (descendingTree r) := isWellFounded_descendingTree_iff.2 hr
  induction x using hr.induction with
  | _ x ih =>
  rw [hT.rank_subAt_eq_succ_iSup (List.isChain_singleton x), Order.succ_eq_succ_iff,
    WellFounded.rank_eq]
  refine le_antisymm (Ordinal.iSup_le fun a => ?_) (Ordinal.iSup_le fun b => ?_)
  · by_cases hxa : r a x
    · have hmem : [x] ++ [a] ∈ descendingTree r := by simp [mem_descendingTree, hxa]
      rw [subAt_descendingTree_append_singleton hmem, ih a hxa]
      exact Ordinal.le_iSup (fun b : {b // r b x} => Order.succ (WellFounded.rank r b.val)) ⟨a, hxa⟩
    · have hnot : [x] ++ [a] ∉ descendingTree r := by simp [mem_descendingTree, hxa]
      rw [rank_subAt_eq_zero_of_notMem hnot]
      exact zero_le
  · have hmem : [x] ++ [b.val] ∈ descendingTree r := by simp [mem_descendingTree, b.property]
    have := Ordinal.le_iSup (fun a : α => rank (subAt (descendingTree r) ([x] ++ [a]))) b.val
    rwa [subAt_descendingTree_append_singleton hmem, ih b.val b.property] at this

/-- **The rank of the descending tree** of a well-founded relation: the successor of the supremum,
over the carrier, of the successors of the `r`-ranks. -/
theorem rank_descendingTree [hr : WellFounded r] :
    rank (descendingTree r) = Order.succ (⨆ x, Order.succ (WellFounded.rank r x)) := by
  have hT : IsWellFounded (descendingTree r) := isWellFounded_descendingTree_iff.2 hr
  rw [hT.rank_eq_succ_iSup List.isChain_nil]
  simp only [rank_subAt_descendingTree_singleton]

/-- **The order type is at most the tree rank.** For a well-order, the order type is at most the
rank of its descending tree. -/
theorem type_le_rank_descendingTree [IsWellOrder α r] :
    Ordinal.type r ≤ rank (descendingTree r) := by
  rw [rank_descendingTree]
  refine le_of_forall_lt fun o ho => ?_
  obtain ⟨x, rfl⟩ := Ordinal.typein_surj r ho
  have h := Ordinal.le_iSup (fun y => Order.succ (WellFounded.rank r y)) x
  rw [congrFun (WellFounded.rank_eq_typein r) x] at h
  exact (Order.lt_succ _).trans_le (h.trans (Order.le_succ _))

end Descriptive.Tree
