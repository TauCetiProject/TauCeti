/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Primitive-recursive operations on free-group words

For a primitively encodable alphabet, free reduction, reducedness, word equality,
inversion and multiplication are primitive recursive on Mathlib's standard list encoding.
The inputs to the word problem may be unreduced. Multiplication returns the reduced word
of the product, and inversion preserves reducedness when its input is reduced.

These results provide finite-word operations for coding equations over free groups. They
use `FreeGroup.reduce` itself and do not introduce another free-group carrier or encoding.
In particular, reduced words are exactly the fixed points of reduction; Mathlib's
`mk_toWord`, `toWord_mk` and `isReduced_iff_reduce_eq` give their correspondence with
free-group elements.

The computability arguments use Mathlib's primitive-recursion theorems for lists,
especially `Primrec.list_rec` and `Primrec.list_casesOn`.

`primrecPred_exists_encode_toWord` recognizes exactly the natural numbers encoding
reduced representatives. It uses `Encodable.decode₂`, which rejects noncanonical
codes even if the alphabet's decoder accepts redundant codes.
-/

public section

namespace FreeGroup

variable {α : Type*} [Primcodable α]

/-- Free reduction is primitive recursive on the standard encoding of signed-letter lists. -/
theorem primrec_reduce [DecidableEq α] : Primrec (reduce : List (α × Bool) → List (α × Bool)) := by
  have step : Primrec fun p : (α × Bool) × List (α × Bool) =>
      List.casesOn (motive := fun _ => List (α × Bool)) p.2 [p.1] fun q l =>
        if p.1.1 = q.1 ∧ p.1.2 = !q.2 then l else p.1 :: q :: l := by
    refine Primrec.list_casesOn
      (f := fun p : (α × Bool) × List (α × Bool) => p.2)
      (h := fun p q => if p.1.1 = q.1.1 ∧ p.1.2 = !q.1.2
        then q.2 else p.1 :: q.1 :: q.2) Primrec.snd
      (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) ?_
    apply Primrec₂.mk
    refine Primrec.ite (c := fun p : ((α × Bool) × List (α × Bool)) ×
        ((α × Bool) × List (α × Bool)) => p.1.1.1 = p.2.1.1 ∧ p.1.1.2 = !p.2.1.2)
      ?_ (Primrec.snd.comp Primrec.snd) ?_
    · exact (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).and
        (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.not.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
    · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))
  refine (Primrec.list_rec Primrec.id (Primrec.const [])
    (Primrec.to₂ <| step.comp <| Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).of_eq fun w => ?_
  induction w with
  | nil => exact reduce_nil.symm
  | cons a w ih =>
    dsimp only [id_eq, List.recOn] at *
    rw [reduce.cons, ← ih]

/-- Reduced-word validity is primitive recursive, rather than merely decidable. -/
theorem primrecPred_isReduced : PrimrecPred (IsReduced : List (α × Bool) → Prop) := by
  classical
  exact (Primrec.eq.comp primrec_reduce Primrec.id).of_eq fun _ =>
    isReduced_iff_reduce_eq.symm

/-- Equality of the group elements represented by two arbitrary words is primitive recursive. -/
theorem primrecRel_mk_eq_mk :
    PrimrecRel fun u v : List (α × Bool) => mk u = mk v := by
  classical
  exact (Primrec.eq.comp₂ (primrec_reduce.comp₂ Primrec₂.left)
    (primrec_reduce.comp₂ Primrec₂.right)).of_eq fun _ _ => ⟨reduce.exact, reduce.sound⟩

/-- The trivial-word predicate is primitive recursive, including on unreduced inputs. -/
theorem primrecPred_mk_eq_one :
    PrimrecPred fun w : List (α × Bool) => mk w = 1 := by
  exact (primrecRel_mk_eq_mk.comp Primrec.id (Primrec.const [])).of_eq
    fun _ => by simp only [one_eq_mk, id_eq]

/-- Reversing a word and inverting every letter is primitive recursive. -/
theorem primrec_invRev : Primrec (invRev : List (α × Bool) → List (α × Bool)) := by
  exact (Primrec.list_reverse.comp
    (Primrec.list_map (Primrec.id (α := List (α × Bool)))
      (Primrec.to₂ <| Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.not.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => by
    simp only [invRev, id_eq]

/-- Multiplication of represented group elements, with a reduced word as output, is
primitive recursive. -/
theorem primrec_toWord_mk_mul_mk [DecidableEq α] :
    Primrec₂ fun u v : List (α × Bool) => (mk u * mk v).toWord := by
  exact (primrec_reduce.comp₂ Primrec.list_append).of_eq fun _ _ => by
    rw [mul_mk, toWord_mk]

/-- Inversion of represented group elements, with a reduced word as output, is
primitive recursive even when the input word is unreduced. -/
theorem primrec_toWord_inv_mk [DecidableEq α] :
    Primrec fun w : List (α × Bool) => (mk w)⁻¹.toWord := by
  simpa only [toWord_inv, toWord_mk] using primrec_invRev.comp primrec_reduce

/-- Valid codes of reduced representatives of free-group elements form a
primitive-recursive predicate on natural numbers. Invalid codes are rejected. -/
theorem primrecPred_exists_encode_toWord [DecidableEq α] :
    PrimrecPred fun n : ℕ => ∃ x : FreeGroup α, Encodable.encode x.toWord = n := by
  classical
  have test : Primrec fun n : ℕ =>
      ((Encodable.decode₂ (List (α × Bool)) n).map
        (fun w => decide (IsReduced w))).getD false :=
    Primrec.option_getD.comp
      (Primrec.option_map Primrec.decode₂
        (primrecPred_isReduced.decide.comp Primrec.snd).to₂) (Primrec.const false)
  refine (Primrec.eq.comp test (Primrec.const true)).of_eq fun n => ?_
  cases hd : Encodable.decode₂ (List (α × Bool)) n with
  | none =>
    simp only [Option.map_none, Option.getD_none, Bool.false_eq_true, false_iff]
    rintro ⟨x, hx⟩
    have := Encodable.decode₂_eq_some.mpr hx
    simp [hd] at this
  | some w =>
    simp only [Option.map_some, Option.getD_some, decide_eq_true_eq]
    constructor
    · intro hw
      refine ⟨mk w, ?_⟩
      rw [toWord_mk, hw.reduce_eq]
      exact Encodable.decode₂_eq_some.mp hd
    · rintro ⟨x, hx⟩
      have hw : x.toWord = w := by
        simpa only [← hx, Encodable.decode₂_encode, Option.some.injEq] using hd
      exact hw ▸ isReduced_toWord

end FreeGroup
