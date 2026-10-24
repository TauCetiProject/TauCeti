/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Computability
public import TauCeti.GroupTheory.FreeGroup.Conjugacy
public import TauCeti.GroupTheory.ProperPower

/-!
# Primitive-recursive proper-power membership

Proper-power membership is primitive recursive on signed-letter lists over any primitively
encodable alphabet, including unreduced inputs. No encoding of free-group elements is needed.

The bounded word criterion searches for a conjugating prefix, a repeating block immediately
after it, and an exponent. All three lengths are bounded by the reduced input length. The
identity is treated separately, since it is a proper power but has no nonempty repeating block.
This supplies a finite-word test suitable for coding equations and maximal-root data.

The word decomposition uses Mathlib's
`FreeGroup.reduceCyclically.reduce_flatten_replicate`. The mathematical background is the
cyclic reduction and power normal form in Lyndon and Schupp, *Combinatorial Group Theory*,
Chapter I. No second cyclic-reduction procedure is introduced.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- A reduced word represents a proper power exactly when it is empty or is a conjugate
of a repeated block. The conjugator and block are extracted from the input by bounded
indices, and the exponent is bounded by its length. -/
theorem isProperPower_mk_iff_exists_bounded_replicate {w : List (α × Bool)}
    (hw : IsReduced w) :
    Group.IsProperPower (mk w) ↔ w = [] ∨
      ∃ i ≤ w.length, ∃ j ≤ w.length, ∃ n ≤ w.length, 2 ≤ n ∧
        w = w.take i ++ (List.replicate n ((w.drop i).take j)).flatten ++
          invRev (w.take i) := by
  classical
  constructor
  · intro h
    by_cases hw0 : w = []
    · exact Or.inl hw0
    obtain ⟨y, n, hn, hy⟩ := Group.isProperPower_iff.mp h
    let c := reduceCyclically.conjugator y.toWord
    let v := reduceCyclically y.toWord
    have heq : w = c ++ (List.replicate n v).flatten ++ invRev c := by
      have hword := congrArg toWord hy
      simpa only [toWord_mk, hw.reduce_eq, toWord_pow,
        reduceCyclically.reduce_flatten_replicate isReduced_toWord,
        ite_eq_right (by omega : n ≠ 0)] using hword
    have hv : v ≠ [] := by
      intro hv0
      have hy1 : y = 1 := by
        have hc := mk_conjugator_mul_mk_reduceCyclically y.toWord
        dsimp only [v] at hv0
        rw [hv0, ← one_eq_mk, mul_one, mul_inv_cancel, mk_toWord] at hc
        exact hc.symm
      simp only [hy1, one_pow] at hy
      exact hw0 (hw.eq_of_mk_eq IsReduced.nil hy)
    have hlen : w.length = c.length + n * v.length + c.length := by
      rw [heq]
      simp [Nat.add_assoc]
    have hi : c.length ≤ w.length := by omega
    have hj : v.length ≤ w.length := by
      have := Nat.le_mul_of_pos_left v.length (by omega : 0 < n)
      omega
    have hnlen : n ≤ w.length := by
      have := Nat.le_mul_of_pos_right n (List.length_pos_iff.mpr hv)
      omega
    have htake : w.take c.length = c := by
      rw [heq, List.append_assoc]
      simp
    have hblock : (w.drop c.length).take v.length = v := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [heq, List.append_assoc]
      simp [List.replicate_succ, List.append_assoc]
    exact Or.inr ⟨c.length, hi, v.length, hj, n, hnlen, hn,
      by simpa only [htake, hblock] using heq⟩
  · rintro (rfl | ⟨i, _, j, _, n, _, hn, heq⟩)
    · simpa only [← one_eq_mk] using (Group.IsProperPower.one (G := FreeGroup α))
    · rw [heq, ← mul_mk, ← mul_mk, ← inv_mk, ← pow_mk]
      exact (Group.isProperPower_conj_iff _ _).mpr
        (Group.isProperPower_pow _ hn)

/-- Proper-power membership of the element represented by an arbitrary word is primitive
recursive on Mathlib's standard list encoding. The alphabet need not be finite. -/
theorem primrecPred_isProperPower_mk [Primcodable α] :
    PrimrecPred fun w : List (α × Bool) => Group.IsProperPower (mk w) := by
  classical
  let W := List (α × Bool)
  -- With all three indices fixed, the test uses only primitive-recursive list operations.
  have step : PrimrecRel fun n (p : W × ℕ × ℕ) => 2 ≤ n ∧
      p.1 = p.1.take p.2.1 ++
        (List.replicate n ((p.1.drop p.2.1).take p.2.2)).flatten ++
        invRev (p.1.take p.2.1) := by
    have word : Primrec fun p : ℕ × (W × ℕ × ℕ) => p.2.1 :=
      Primrec.fst.comp Primrec.snd
    have start : Primrec fun p : ℕ × (W × ℕ × ℕ) => p.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have size : Primrec fun p : ℕ × (W × ℕ × ℕ) => p.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have initial := Primrec.list_take.comp start word
    have block := Primrec.list_take.comp size (Primrec.list_drop.comp start word)
    have repeated : Primrec fun p : ℕ × (W × ℕ × ℕ) =>
        (List.replicate p.1 ((p.2.1.drop p.2.2.1).take p.2.2.2)).flatten := by
      exact (Primrec.list_flatten.comp
        (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
          (Primrec.to₂ <| block.comp Primrec.fst))).of_eq fun _ => by
            simp only [List.map_const', List.length_range]
    exact (Primrec.nat_le.comp (Primrec.const 2) Primrec.fst).and
      (Primrec.eq.comp word (Primrec.list_append.comp
        (Primrec.list_append.comp initial repeated) (primrec_invRev.comp initial)))
  -- Eliminate the indices in turn by bounded list searches, then freely reduce the input.
  have exponent : PrimrecPred fun p : W × ℕ × ℕ =>
      ∃ n ≤ p.1.length, 2 ≤ n ∧ p.1 = p.1.take p.2.1 ++
        (List.replicate n ((p.1.drop p.2.1).take p.2.2)).flatten ++
        invRev (p.1.take p.2.1) := by
    exact (step.exists_mem_list.comp
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))
      Primrec.id).of_eq fun _ => by simp only [List.mem_range, Nat.lt_succ_iff, id_eq]
  have blockSize : PrimrecRel fun j (p : W × ℕ) =>
      ∃ n ≤ p.1.length, 2 ≤ n ∧ p.1 = p.1.take p.2 ++
        (List.replicate n ((p.1.drop p.2).take j)).flatten ++
        invRev (p.1.take p.2) :=
    exponent.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))
  have blockSearch : PrimrecPred fun p : W × ℕ =>
      ∃ j ≤ p.1.length, ∃ n ≤ p.1.length, 2 ≤ n ∧ p.1 = p.1.take p.2 ++
        (List.replicate n ((p.1.drop p.2).take j)).flatten ++
        invRev (p.1.take p.2) := by
    exact (blockSize.exists_mem_list.comp
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))
      Primrec.id).of_eq fun _ => by simp only [List.mem_range, Nat.lt_succ_iff, id_eq]
  have conjugatorSize : PrimrecRel fun i (w : W) =>
      ∃ j ≤ w.length, ∃ n ≤ w.length, 2 ≤ n ∧ w = w.take i ++
        (List.replicate n ((w.drop i).take j)).flatten ++ invRev (w.take i) :=
    blockSearch.comp (Primrec.pair Primrec.snd Primrec.fst)
  have search : PrimrecPred fun w : W =>
      ∃ i ≤ w.length, ∃ j ≤ w.length, ∃ n ≤ w.length, 2 ≤ n ∧
        w = w.take i ++ (List.replicate n ((w.drop i).take j)).flatten ++
          invRev (w.take i) := by
    exact (conjugatorSize.exists_mem_list.comp
      (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
      Primrec.id).of_eq fun _ => by simp only [List.mem_range, Nat.lt_succ_iff, id_eq]
  have test := (Primrec.eq.comp (Primrec.id (α := W)) (Primrec.const [])).or search
  exact (test.comp primrec_reduce).of_eq fun w => by
    simp only [id_eq]
    rw [← isProperPower_mk_iff_exists_bounded_replicate
      (IsReduced.of_reduce_eq reduce.idem), reduce.self]

end FreeGroup
