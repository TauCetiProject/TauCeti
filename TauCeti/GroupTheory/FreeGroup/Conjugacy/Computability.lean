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

Conjugacy of elements represented by arbitrary signed-letter lists is primitive recursive
on Mathlib's standard list encoding. No reducedness hypothesis is imposed on the inputs.
The proof uses the cyclic-reduction criterion
`FreeGroup.isConj_iff_isRotated_reduceCyclically`, together with primitive-recursive free
reduction and list rotation. There is no additional free-group carrier or encoding.

Cyclic reduction itself is primitive recursive: removing an inverse pair of end letters
is a primitive-recursive operation, and at most the original word length many iterations
are needed. The bounded iteration agrees with Mathlib's `FreeGroup.reduceCyclically`,
including on unreduced lists.

## References

* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter I
  (cyclic reduction and the conjugacy criterion).
-/

public section

namespace TauCeti

open FreeGroup

variable {α : Type*}

/-- Remove one inverse pair of end letters, leaving other words unchanged. -/
private def cyclicReductionStep [DecidableEq α] : List (α × Bool) → List (α × Bool)
  | [] => []
  | a :: L =>
    match L.reverse with
    | [] => [a]
    | b :: R => if b.1 = a.1 ∧ (!b.2) = a.2 then R.reverse else a :: L

private theorem cyclicReductionStep_cons_append [DecidableEq α]
    (a b : α × Bool) (L : List (α × Bool)) :
    cyclicReductionStep (a :: (L ++ [b])) =
      if b.1 = a.1 ∧ (!b.2) = a.2 then L else a :: (L ++ [b]) := by
  simp [cyclicReductionStep]

private theorem iterate_cyclicReductionStep [DecidableEq α] (L : List (α × Bool))
    (n : ℕ) (hn : L.length ≤ n) :
    cyclicReductionStep^[n] L = reduceCyclically L := by
  induction L using List.bidirectionalRec generalizing n with
  | nil =>
    simpa using Function.iterate_fixed (f := cyclicReductionStep) (x := []) rfl n
  | singleton a =>
    simpa using Function.iterate_fixed (f := cyclicReductionStep) (x := [a]) rfl n
  | cons_append a L b ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [Function.iterate_succ_apply, cyclicReductionStep_cons_append,
        reduceCyclically.cons_append]
      split <;> rename_i h
      · apply ih n
        simp only [List.length_cons, List.length_append] at hn
        omega
      · have hfix : cyclicReductionStep (a :: (L ++ [b])) = a :: (L ++ [b]) := by
          simp only [cyclicReductionStep_cons_append, h, ite_false]
        exact Function.iterate_fixed hfix n

variable [Primcodable α]

private theorem primrec_cyclicReductionStep [DecidableEq α] :
    Primrec (cyclicReductionStep : List (α × Bool) → List (α × Bool)) := by
  have hstep : Primrec fun p : (α × Bool) × List (α × Bool) =>
      List.casesOn (motive := fun _ => List (α × Bool)) p.2.reverse [p.1] fun b R =>
        if b.1 = p.1.1 ∧ (!b.2) = p.1.2 then R.reverse else p.1 :: p.2 := by
    refine Primrec.list_casesOn
      (f := fun p : (α × Bool) × List (α × Bool) => p.2.reverse)
      (h := fun p q => if q.1.1 = p.1.1 ∧ (!q.1.2) = p.1.2
        then q.2.reverse else p.1 :: p.2)
      (Primrec.list_reverse.comp Primrec.snd)
      (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) ?_
    apply Primrec₂.mk
    refine Primrec.ite ?_ (Primrec.list_reverse.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst))
    exact (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).and
      (Primrec.eq.comp (Primrec.not.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  exact (Primrec.list_casesOn Primrec.id (Primrec.const [])
    (hstep.comp Primrec.snd).to₂).of_eq fun L => by
      cases L with
      | nil => rfl
      | cons a L => cases h : L.reverse <;> simp [cyclicReductionStep, h]

/-- Cyclic reduction is primitive recursive on standard signed-letter list codes, even
when its input is not freely reduced. -/
theorem primrec_reduceCyclically [DecidableEq α] :
    Primrec (reduceCyclically : List (α × Bool) → List (α × Bool)) := by
  exact (Primrec.nat_iterate Primrec.list_length Primrec.id
    (primrec_cyclicReductionStep.comp Primrec.snd).to₂).of_eq fun L =>
      iterate_cyclicReductionStep L L.length le_rfl

/-- Conjugacy in a free group is primitive recursive on the standard codes of arbitrary
word representatives. In particular, freely reducing the inputs is not a precondition. -/
theorem primrecRel_isConj_mk_mk :
    PrimrecRel fun u v : List (α × Bool) => IsConj (mk u) (mk v) := by
  classical
  have hcyclic : Primrec fun L : List (α × Bool) => reduceCyclically (reduce L) :=
    primrec_reduceCyclically.comp FreeGroup.primrec_reduce
  exact (primrecRel_list_isRotated.comp (hcyclic.comp Primrec.fst)
    (hcyclic.comp Primrec.snd)).of_eq fun p => by
      simpa only [toWord_mk] using
        (isConj_iff_isRotated_reduceCyclically (x := mk p.1) (y := mk p.2)).symm

end TauCeti
