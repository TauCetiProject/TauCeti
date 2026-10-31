/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Rotate

/-!
# Primitive-recursive list rotations

Rotation and cyclic-permutation testing are primitive recursive on the standard list
encoding. The bounded rotation criterion includes the empty list, so it also applies to
cyclic reductions of trivial free-group words.
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

end Primrec

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
