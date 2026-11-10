/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Rotate

/-!
# Primitive-recursive list operations

Rotation and cyclic-permutation testing are primitive recursive on the standard list
encoding. The bounded rotation criterion includes the empty list, so it also applies to
cyclic reductions of trivial free-group words.

Searching a list for its first element passing a test, `List.find?`, is primitive recursive.
Over `List.range n` this is the bounded least-witness search of finite-stage constructions,
returning `none` when no number below `n` passes the test. A relation searched over all numbers
up to the length of a primitive-recursively computed list stays primitive recursive
(`PrimrecRel.exists_le_length`).
-/

public section

namespace Primrec

variable {α : Type*} [Primcodable α]

/-- Rotating a list by a natural number is primitive recursive. -/
theorem list_rotate : Primrec₂ (List.rotate : List α → ℕ → List α) := by
  have index : Primrec fun p : List α × ℕ => p.2 % p.1.length :=
    nat_mod.comp snd (list_length.comp fst)
  exact (list_append.comp (list_drop.comp index fst)
    (list_take.comp index fst)).to₂.of_eq fun l n =>
      (List.rotate_eq_drop_append_take_mod (l := l) (n := n)).symm

/-- The first element of a list passing a test, if any, is primitive recursive, uniformly in a
parameter on which the list and the test depend primitive recursively. -/
theorem list_find? {β : Type*} [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).find? (p a) :=
  (list_getElem?.comp hf (list_findIdx hf hp)).of_eq fun _ =>
    List.find?_eq_getElem?_findIdx.symm

end Primrec

namespace PrimrecRel

/-- A relation searched over all `n ≤ (f b).length`, for `f` primitive recursive, stays
primitive recursive. -/
theorem exists_le_length {β γ : Type*} [Primcodable β] [Primcodable γ]
    {f : β → List γ} {R : ℕ → β → Prop} (hR : PrimrecRel R) (hf : Primrec f) :
    PrimrecPred fun b => ∃ n ≤ (f b).length, R n b :=
  (hR.exists_mem_list.comp
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp hf)))
    Primrec.id).of_eq fun _ => by simp only [List.mem_range, Nat.lt_succ_iff, id_eq]

end PrimrecRel

namespace List

variable {α : Type*} [Primcodable α]

/-- Cyclic permutation is a primitive-recursive relation, including for empty lists. -/
theorem primrecRel_isRotated : PrimrecRel (IsRotated : List α → List α → Prop) := by
  have test : PrimrecRel fun n (p : List α × List α) => p.1.rotate n = p.2 :=
    Primrec.eq.comp (Primrec.list_rotate.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  exact (test.exists_mem_list.comp
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))
    Primrec.id).primrecRel.of_eq fun u v => by
      simp only [List.mem_range, Nat.lt_succ_iff, id_eq, isRotated_iff_mod]

end List
