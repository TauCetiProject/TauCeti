/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import TauCeti.Data.Nat.BitIndices
import TauCeti.Data.Finset.Sort

/-!
# Primitive recursive operations on binary codes of finite sets

A finite set `s` of naturals has the canonical binary code `∑ i ∈ s, 2 ^ i`, and Mathlib's
`Finset.equivBitIndices : ℕ ≃ Finset ℕ` decodes a number as the set of its bit indices. This file
shows that the basic operations on finite sets are primitive recursive on the codes, so that a
computation can manipulate finite sets, such as the finite stages of an enumeration, as numbers.

No `Primcodable (Finset ℕ)` instance is introduced: Mathlib's `Encodable (Finset ℕ)` instance
uses a different encoding. All statements are about functions between natural numbers, lists and
options.

## Main results

* `Primrec.nat_pow`, `Primrec.nat_testBit`: powers and binary digits are primitive recursive.
* `Primrec.nat_bitIndices`: decoding a number to its increasing list of bit indices is primitive
  recursive.
* `Primrec.equivBitIndices_symm_toFinset`: the code of the set of entries of a list.
* `Primrec.mem_equivBitIndices`: membership in a coded set is a primitive recursive relation.
* `Primrec.equivBitIndices_union`, `Primrec.equivBitIndices_inter`,
  `Primrec.equivBitIndices_sdiff`: union, intersection and difference of coded sets.
* `Primrec.equivBitIndices_filter`, `Primrec.equivBitIndices_symm_range`: filtering a coded set by
  a primitive recursive relation, and the code of `Finset.range n`; together they give bounded
  filtering.
* `Primrec.equivBitIndices_min'`: the least element of a coded set, or `none` when it is empty.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.2, for the
  canonical indexing of finite sets.
-/

public section

open Finset (equivBitIndices equivBitIndices_apply equivBitIndices_symm_apply)

namespace Primrec

variable {α : Type*} [Primcodable α]

/-- Exponentiation of natural numbers is primitive recursive. -/
theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The binary digits of a natural number are primitive recursive. -/
theorem nat_testBit : Primrec₂ Nat.testBit :=
  (Primrec.eq.comp (nat_mod.comp (nat_div.comp fst (nat_pow.comp (const 2) snd)) (const 2))
    (const 1)).decide.of_eq fun _ => Nat.testBit_eq_decide_div_mod_eq.symm

/-- Decoding a number to the increasing list of its bit indices is primitive recursive. -/
theorem nat_bitIndices : Primrec Nat.bitIndices :=
  ((PrimrecRel.listFilter (R := fun i n : ℕ => n.testBit i = true)
    (Primrec.eq.comp (nat_testBit.comp snd fst) (const true))).comp list_range .id).of_eq
    fun n => by simp [Nat.bitIndices_eq_filter_range]

/-- The code of the set of entries of a list is primitive recursive. -/
theorem equivBitIndices_symm_toFinset :
    Primrec fun l : List ℕ => equivBitIndices.symm l.toFinset := by
  -- add `2 ^ x` for each entry `x` whose bit is not yet set
  refine (list_foldr (h := fun _ (p : ℕ × ℕ) => bif p.2.testBit p.1 then p.2 else p.2 + 2 ^ p.1)
    .id (const 0) (cond (nat_testBit.comp (snd.comp snd) (fst.comp snd)) (snd.comp snd)
      (nat_add.comp (snd.comp snd) (nat_pow.comp (const 2) (fst.comp snd))))).of_eq fun l => ?_
  simp only [id]
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.toFinset_cons]
    by_cases hx : x ∈ l.toFinset <;> simp [hx, Finset.sum_insert, add_comm]

/-- Membership in a coded finite set is a primitive recursive relation. -/
theorem mem_equivBitIndices : PrimrecRel fun (x n : ℕ) => x ∈ equivBitIndices n :=
  (Primrec.eq.comp (nat_testBit.comp snd fst) (const true)).of_eq fun p => by simp

/-- Union of coded finite sets is primitive recursive. -/
theorem equivBitIndices_union :
    Primrec₂ fun m n => equivBitIndices.symm (equivBitIndices m ∪ equivBitIndices n) :=
  (equivBitIndices_symm_toFinset.comp
    (list_append.comp (nat_bitIndices.comp fst) (nat_bitIndices.comp snd))).of_eq fun p => by
    simp [List.toFinset_append]

/-- Filtering a coded finite set by a primitive recursive relation is primitive recursive. -/
theorem equivBitIndices_filter {p : α → ℕ → Prop} [∀ a, DecidablePred (p a)]
    (hp : PrimrecRel p) :
    Primrec₂ fun a n => equivBitIndices.symm ((equivBitIndices n).filter (p a)) :=
  (equivBitIndices_symm_toFinset.comp ((PrimrecRel.listFilter (R := fun x a => p a x)
    (hp.comp snd fst)).comp (nat_bitIndices.comp snd) fst)).of_eq fun q => by
    simp [List.toFinset_filter]

/-- Intersection of coded finite sets is primitive recursive. -/
theorem equivBitIndices_inter :
    Primrec₂ fun m n => equivBitIndices.symm (equivBitIndices m ∩ equivBitIndices n) :=
  ((equivBitIndices_filter (p := fun n x => x ∈ equivBitIndices n)
    (mem_equivBitIndices.comp snd fst)).comp snd fst).of_eq fun _ => by
    rw [Finset.filter_mem_eq_inter]

/-- Difference of coded finite sets is primitive recursive. -/
theorem equivBitIndices_sdiff :
    Primrec₂ fun m n => equivBitIndices.symm (equivBitIndices m \ equivBitIndices n) :=
  ((equivBitIndices_filter (p := fun n x => x ∉ equivBitIndices n)
    (mem_equivBitIndices.comp snd fst).not).comp snd fst).of_eq fun _ => by
    rw [Finset.filter_notMem_eq_sdiff]

/-- The code `2 ^ n - 1` of `Finset.range n` is primitive recursive in `n`. -/
theorem equivBitIndices_symm_range : Primrec fun n => equivBitIndices.symm (Finset.range n) :=
  (equivBitIndices_symm_toFinset.comp list_range).of_eq fun n => by rw [List.toFinset_range]

/-- The least element of a coded finite set, or `none` when the set is empty, is primitive
recursive. -/
theorem equivBitIndices_min' :
    Primrec fun n =>
      if h : (equivBitIndices n).Nonempty then some ((equivBitIndices n).min' h) else none :=
  (list_head?.comp nat_bitIndices).of_eq fun n => by
    rw [← Finset.head?_sort, equivBitIndices_apply, Nat.sort_toFinset_bitIndices]

end Primrec
