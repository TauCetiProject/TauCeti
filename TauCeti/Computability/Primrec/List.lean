/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Sections

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

Repeating an element and enumerating the sections of a list of lists (`List.sections`, all
ways of choosing one entry from each list) are primitive recursive. Together they enumerate
the tuples of a given length over a finite list of choices, which is the search space of
bounded exhaustive searches. The product of two lists (`l₁ ×ˢ l₂`) and, when addition is
primitive recursive, the sum of a list are primitive recursive as well.

Converting finite tuples `Fin n → α` to lists (`List.ofFn`), extracting `Fin n`-indexed tuples
from lists with a default entry (`List.getD`), and `Fin.cons` / `Fin.tail` on tuples are also
primitive recursive.
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

/-- The list of `n` copies of an element is primitive recursive in `n` and the element. -/
theorem list_replicate : Primrec₂ (List.replicate : ℕ → α → List α) :=
  (nat_rec' fst (const []) (list_cons.comp (snd.comp fst) (snd.comp snd)).to₂).to₂.of_eq
    fun n a => by induction n <;> simp_all [List.replicate_succ]

/-- The sections of a list of lists, all ways of choosing one entry from each list, are
primitive recursive. -/
theorem list_sections : Primrec (List.sections : List (List α) → List (List α)) := by
  have step : Primrec₂ fun (_ : List (List α)) (q : List α × List (List α)) =>
      q.2.flatMap fun s => q.1.map fun a => a :: s :=
    (list_flatMap (snd.comp snd) (list_map (fst.comp (snd.comp fst))
      (list_cons.comp snd (snd.comp fst)).to₂).to₂).to₂
  exact (list_foldr .id (const [[]]) step).of_eq fun L => by
    induction L <;> simp_all [List.sections]

/-- The product `l₁ ×ˢ l₂` of two lists, all pairs of an entry of `l₁` and an entry of `l₂`, is
primitive recursive. -/
theorem list_product {β : Type*} [Primcodable β] :
    Primrec₂ ((· ×ˢ ·) : List α → List β → List (α × β)) :=
  (list_flatMap fst (list_map (snd.comp fst) (pair (snd.comp fst) snd).to₂).to₂).to₂.of_eq
    fun _ _ => rfl

/-- The sum of a list is primitive recursive when addition is. -/
theorem list_sum [Add α] [Zero α] (hadd : Primrec₂ ((· + ·) : α → α → α)) :
    Primrec (List.sum : List α → α) :=
  (list_foldr .id (const 0) (hadd.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun l => by
    induction l <;> simp_all

/-- Converting a finite tuple `Fin n → α` to a list via `List.ofFn` is primitive recursive. -/
theorem list_ofFn' {n : ℕ} : Primrec (List.ofFn : (Fin n → α) → List α) :=
  (vector_toList.comp vector_ofFn').of_eq fun x => List.Vector.toList_ofFn x

/-- Extracting the first `n` entries of a list with default `d` as a finite tuple `Fin n → α` is
primitive recursive in the list and the default value. -/
theorem list_getD_fin {n : ℕ} :
    Primrec₂ fun (l : List α) (d : α) => (fun i : Fin n => l.getD i d) :=
  fin_curry.2
    ((option_getD.comp (list_getElem?.comp (fst.comp fst) (fin_val.comp snd))
      (snd.comp fst)).of_eq fun p => by simp [List.getD_eq_getElem?_getD])

/-- Prepending an element to a finite tuple `Fin n → α` via `Fin.cons` is primitive recursive. -/
theorem fin_cons {n : ℕ} : Primrec₂ (@Fin.cons n (fun _ => α)) :=
  (vector_get'.comp (vector_cons.comp fst (vector_ofFn'.comp snd))).to₂.of_eq fun _ _ =>
    funext fun i => Fin.cases (by simp) (by simp) i

/-- Dropping the first element of a finite tuple `Fin (n + 1) → α` via `Fin.tail` is primitive
recursive. -/
theorem fin_tail {n : ℕ} : Primrec (Fin.tail : (Fin (n + 1) → α) → Fin n → α) :=
  (vector_get'.comp (vector_tail.comp vector_ofFn')).of_eq fun _ =>
    funext fun _ => by simp [Fin.tail]

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
