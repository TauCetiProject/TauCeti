/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.List
public import TauCeti.GroupTheory.FreeGroup.Computability
public import TauCeti.GroupTheory.FreeGroup.Conjugacy.Basic

/-!
# Primitive-recursive conjugacy of free-group words

Cyclic reduction and conjugacy testing are primitive recursive over every primitively
encodable alphabet. Inputs may be unreduced: free reduction is followed by cyclic reduction,
and conjugacy is tested by cyclic permutation. No encoding of free-group elements is needed.

Cyclic reduction is Mathlib's `FreeGroup.reduceCyclically`. Its primitive recursiveness
follows by bounding the number of cancellations at the two ends by the input length.
The conjugacy criterion is `FreeGroup.isConj_iff_isRotated_reduceCyclically`.

## References

* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Chapter I, §1
  (cyclic reduction and conjugacy of words).
-/

public section

namespace FreeGroup

variable {α : Type*} [DecidableEq α]

-- One cancellation at the two ends; words of length less than two are left alone.
private def peel (w : List (α × Bool)) : List (α × Bool) :=
  if 2 ≤ w.length ∧
      w.head? = w.reverse.head?.map (fun a => (a.1, !a.2)) then
    w.tail.reverse.tail.reverse
  else w

private theorem peel_nil : peel ([] : List (α × Bool)) = [] := by simp [peel]

private theorem peel_singleton (a : α × Bool) : peel [a] = [a] := by simp [peel]

private theorem peel_cons_append (a b : α × Bool) (w : List (α × Bool)) :
    peel (a :: (w ++ [b])) =
      if b.1 = a.1 ∧ (!b.2) = a.2 then w else a :: (w ++ [b]) := by
  simp [peel, List.reverse_cons, List.reverse_append, Prod.ext_iff, eq_comm]

-- The length bound works on arbitrary words, not only reduced words.
private theorem peel_iterate_eq (w : List (α × Bool)) (n : ℕ) (hn : w.length ≤ n) :
    peel^[n] w = reduceCyclically w := by
  induction w using List.bidirectionalRec generalizing n with
  | nil => simpa using Function.iterate_fixed peel_nil n
  | singleton a => simpa using Function.iterate_fixed (peel_singleton a) n
  | cons_append a w b ih =>
    rw [reduceCyclically.cons_append]
    split_ifs with h
    · cases n with
      | zero => simp at hn
      | succ n =>
        rw [Function.iterate_succ_apply, peel_cons_append, ite_eq_left h]
        exact ih n (by simp only [List.length_cons, List.length_append] at hn; omega)
    · exact Function.iterate_fixed (by rw [peel_cons_append, ite_eq_right h]) n

/-- Cyclic reduction is primitive recursive on the standard encoding of signed-letter
lists. The input need not be reduced. -/
theorem primrec_reduceCyclically [Primcodable α] :
    Primrec (reduceCyclically : List (α × Bool) → List (α × Bool)) := by
  have inverseLetter : Primrec fun a : α × Bool => (a.1, !a.2) :=
    Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
  have lastInverse : Primrec fun w : List (α × Bool) =>
      w.reverse.head?.map (fun a => (a.1, !a.2)) :=
    (Primrec.option_map₁ inverseLetter).comp (Primrec.list_head?.comp Primrec.list_reverse)
  have step : Primrec (peel : List (α × Bool) → List (α × Bool)) :=
    Primrec.ite
      ((Primrec.nat_le.comp (Primrec.const 2) Primrec.list_length).and
        (Primrec.eq.comp Primrec.list_head? lastInverse))
      (Primrec.list_reverse.comp (Primrec.list_tail.comp
        (Primrec.list_reverse.comp Primrec.list_tail))) Primrec.id
  exact (Primrec.nat_iterate Primrec.list_length Primrec.id
    (step.comp₂ Primrec₂.right)).of_eq fun w => peel_iterate_eq w w.length le_rfl

omit [DecidableEq α] in
/-- Conjugacy of the free-group elements represented by arbitrary words is primitive
recursive. This includes the identity and does not require a finite alphabet. -/
theorem primrecRel_isConj_mk [Primcodable α] :
    PrimrecRel fun u v : List (α × Bool) => IsConj (mk u) (mk v) := by
  classical
  have cyclic : Primrec fun w : List (α × Bool) => reduceCyclically (reduce w) :=
    primrec_reduceCyclically.comp primrec_reduce
  exact (List.primrecRel_isRotated.comp₂ (cyclic.comp₂ Primrec₂.left)
    (cyclic.comp₂ Primrec₂.right)).of_eq fun u v => by
      simp only [← toWord_mk, ← isConj_iff_isRotated_reduceCyclically]

end FreeGroup
