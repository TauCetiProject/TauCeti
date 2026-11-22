/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Computability
public import TauCeti.Algebra.Group.ProperPower
import TauCeti.Computability.Primrec.List
import TauCeti.GroupTheory.FreeGroup.ProperPower.Word

/-!
# Primitive-recursive proper-power membership

Proper-power membership is primitive recursive on signed-letter lists over any primitively
encodable alphabet, including unreduced inputs. No encoding of free-group elements is needed.

The test searches, as in the bounded word criterion
`FreeGroup.isProperPower_mk_iff_exists_bounded_replicate`, for a conjugating prefix, a repeating
block immediately after it, and an exponent. All three lengths are bounded by the reduced input
length. The identity is treated separately, since it is a proper power but has no nonempty
repeating block. This supplies a finite-word test suitable for coding equations and maximal-root
data.

The mathematical background is the cyclic reduction and power normal form in Lyndon and Schupp,
*Combinatorial Group Theory*, Chapter I. No second cyclic-reduction procedure is introduced.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- The relation saying that a word is a conjugate of a block repeated `n ≥ 2` times, with
the conjugator and block given by two lengths, is primitive recursive. Once all three indices
are fixed, the test uses only primitive-recursive list operations. -/
private theorem primrecRel_repeatedBlock [Primcodable α] :
    PrimrecRel fun n (p : List (α × Bool) × ℕ × ℕ) => 2 ≤ n ∧
      p.1 = p.1.take p.2.1 ++
        (List.replicate n ((p.1.drop p.2.1).take p.2.2)).flatten ++
        invRev (p.1.take p.2.1) := by
  have word : Primrec fun p : ℕ × (List (α × Bool) × ℕ × ℕ) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have start : Primrec fun p : ℕ × (List (α × Bool) × ℕ × ℕ) => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have size : Primrec fun p : ℕ × (List (α × Bool) × ℕ × ℕ) => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have initial := Primrec.list_take.comp start word
  have block := Primrec.list_take.comp size (Primrec.list_drop.comp start word)
  have repeated : Primrec fun p : ℕ × (List (α × Bool) × ℕ × ℕ) =>
      (List.replicate p.1 ((p.2.1.drop p.2.2.1).take p.2.2.2)).flatten := by
    exact (Primrec.list_flatten.comp
      (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
        (Primrec.to₂ <| block.comp Primrec.fst))).of_eq fun _ => by
          simp only [List.map_const', List.length_range]
  exact (Primrec.nat_le.comp (Primrec.const 2) Primrec.fst).and
    (Primrec.eq.comp word (Primrec.list_append.comp
      (Primrec.list_append.comp initial repeated) (primrec_invRev.comp initial)))

/-- Proper-power membership of the element represented by an arbitrary word is primitive
recursive on Mathlib's standard list encoding. The alphabet need not be finite. -/
theorem primrecPred_isProperPower_mk [Primcodable α] :
    PrimrecPred fun w : List (α × Bool) => Monoid.IsProperPower (mk w) := by
  classical
  -- Eliminate the indices in turn by bounded list searches, then freely reduce the input.
  have exponent : PrimrecPred fun p : List (α × Bool) × ℕ × ℕ =>
      ∃ n ≤ p.1.length, 2 ≤ n ∧ p.1 = p.1.take p.2.1 ++
        (List.replicate n ((p.1.drop p.2.1).take p.2.2)).flatten ++
        invRev (p.1.take p.2.1) := by
    exact primrecRel_repeatedBlock.exists_le_length Primrec.fst
  have blockSize : PrimrecRel fun j (p : List (α × Bool) × ℕ) =>
      ∃ n ≤ p.1.length, 2 ≤ n ∧ p.1 = p.1.take p.2 ++
        (List.replicate n ((p.1.drop p.2).take j)).flatten ++
        invRev (p.1.take p.2) :=
    exponent.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))
  have blockSearch : PrimrecPred fun p : List (α × Bool) × ℕ =>
      ∃ j ≤ p.1.length, ∃ n ≤ p.1.length, 2 ≤ n ∧ p.1 = p.1.take p.2 ++
        (List.replicate n ((p.1.drop p.2).take j)).flatten ++
        invRev (p.1.take p.2) := by
    exact blockSize.exists_le_length Primrec.fst
  have conjugatorSize : PrimrecRel fun i (w : List (α × Bool)) =>
      ∃ j ≤ w.length, ∃ n ≤ w.length, 2 ≤ n ∧ w = w.take i ++
        (List.replicate n ((w.drop i).take j)).flatten ++ invRev (w.take i) :=
    blockSearch.comp (Primrec.pair Primrec.snd Primrec.fst)
  have search : PrimrecPred fun w : List (α × Bool) =>
      ∃ i ≤ w.length, ∃ j ≤ w.length, ∃ n ≤ w.length, 2 ≤ n ∧
        w = w.take i ++ (List.replicate n ((w.drop i).take j)).flatten ++
          invRev (w.take i) := by
    exact conjugatorSize.exists_le_length Primrec.id
  have test := (Primrec.eq.comp (Primrec.id (α := List (α × Bool))) (Primrec.const [])).or search
  exact (test.comp primrec_reduce).of_eq fun w => by
    simp only [id_eq]
    rw [← isProperPower_mk_iff_exists_bounded_replicate
      (IsReduced.of_reduce_eq reduce.idem), reduce.self]

end FreeGroup
