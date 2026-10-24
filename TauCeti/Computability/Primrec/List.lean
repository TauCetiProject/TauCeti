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

Rotation and the cyclic-rotation relation are primitive recursive on the standard list
encoding. The relation tests a bounded family of rotations, including the empty list.
These results allow cyclic word comparisons to be used in primitive-recursive predicates.
-/

public section

namespace TauCeti

variable {α : Type*} [Primcodable α]

/-- List rotation is primitive recursive on standard list codes. -/
theorem primrec_list_rotate : Primrec₂ (List.rotate : List α → ℕ → List α) := by
  have hmod : Primrec fun p : List α × ℕ => p.2 % p.1.length :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.list_length.comp Primrec.fst)
  exact (Primrec.list_append.comp
    (Primrec.list_drop.comp hmod Primrec.fst)
    (Primrec.list_take.comp hmod Primrec.fst)).to₂.of_eq fun _ _ =>
      List.rotate_eq_drop_append_take_mod.symm

/-- Being cyclic rotations of one another is a primitive-recursive relation on lists. -/
theorem primrecRel_list_isRotated : PrimrecRel (List.IsRotated : List α → List α → Prop) := by
  have htest : PrimrecRel fun n (p : List α × List α) => p.1.rotate n = p.2 :=
    Primrec.eq.comp
      (primrec_list_rotate.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  exact (htest.exists_mem_list.comp
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))
    (Primrec.pair Primrec.fst Primrec.snd)).of_eq fun p => by
      simp only [List.mem_range, List.isRotated_iff_mod, Nat.lt_succ_iff]

end TauCeti
