/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.PartitionTable
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Cancellation schemes of a system of equations and inequations

Let `S` be a finite system of equations `s = 1` and inequations `t ≠ 1` over the free group
`F(A)`, in the variables `X`. An inequation `t ≠ 1` holds exactly when `t = z` for some `z ≠ 1`,
so `S` is equivalent to a system of equations in the variables `X` and one new *witness* `z_t` for
each inequation, together with the conditions `z_t ≠ 1`. This file defines the finite family of
*cancellation schemes* of `S` and proves its soundness: solutions of the generalised equations of
the schemes give solutions of `S`. The cancellation schemes of `S` are the partition tables of the
system of words

* `s`, for each equation `s = 1`;
* `t z_t⁻¹` and `z_t z_t⁻¹`, for each inequation `t ≠ 1`,

in which the words of the occurrences of the witnesses are nonempty. A solution `U` of the
generalised equation `Ω_T` of a scheme gives the solution `x ↦ P_x(U)` of `S`, inequations
included; in a group `H` with a homomorphism `F(A) → H`, a solution of the system `Ω_T*` gives a
solution of the equations of `S`, and of its inequations exactly when the witnesses stay
nontrivial.

## Main definitions

* `TauCeti.EqIneqSystem.toWords`: the words of the equations and of the witnessed inequations.
* `TauCeti.EqIneqSystem.IsCancellationScheme`: partition tables of `toWords` with nonempty
  witnesses.
* `TauCeti.EqIneqSystem.genEq`, `TauCeti.EqIneqSystem.wordMap`,
  `TauCeti.EqIneqSystem.witnessWord`: the generalised equation of a table, the word maps `P_x` of
  the variables and of the witnesses.
* `TauCeti.EqIneqSystem.cancellationFamily`: the finite set of cancellation schemes with
  `systemSize S.toWords` letters.

## Main results

* `TauCeti.EqIneqSystem.isSolution_iff_exists_forall_mem_toWords`: the solutions of `S` are the
  solutions of `toWords` with nontrivial witnesses.
* `TauCeti.EqIneqSystem.length_wordMap_le`: the word maps of a partition table are no longer than
  the total length `N` of the words of the system.
* `TauCeti.EqIneqSystem.systemSize_toWords_le`, `TauCeti.EqIneqSystem.numItems_genEq_le`: the size
  of the words of the system, and so the number of items of the generalised equation of a
  partition table, are at most `N ^ 2`.
* `TauCeti.EqIneqSystem.isCancellationScheme_iff_witnessWord_ne_nil`: the cancellation schemes are
  the partition tables in which the word map of every witness is nonempty.
* `TauCeti.EqIneqSystem.isReduced_substituteVars_witnessWord`: in a solution of the generalised
  equation of a partition table, the word of every witness is reduced as written.
* `TauCeti.EqIneqSystem.IsCancellationScheme.mk_substituteVars_witnessWord_ne_one`: in a solution
  of the generalised equation of a scheme, every witness is nontrivial.
* `TauCeti.EqIneqSystem.eval_eq_one_of_mem_V`, `TauCeti.EqIneqSystem.eval_getElem_ineqs_of_mem_V`:
  in a group `H` with a homomorphism `F(A) → H`, a solution of `Ω_T*` gives a solution of the
  equations of `S`, and gives each inequation the value of its witness.
* `TauCeti.EqIneqSystem.isSolution_iff_of_mem_V`: in a group `H` with a homomorphism
  `F(A) → H`, a solution of `Ω_T*` gives a solution of `S` exactly when the witnesses stay
  nontrivial.
* `TauCeti.EqIneqSystem.IsCancellationScheme.isSolution`: a solution of the generalised equation
  of a scheme gives a solution of `S`, inequations included.
* `TauCeti.EqIneqSystem.card_cancellationFamily_le`: the cancellation family has at most
  `(2 (n + |A|) + 1) ^ n` members, for `n = systemSize S.toWords`.
* `TauCeti.EqIneqSystem.cancellationFamily_empty`, `TauCeti.EqIneqSystem.genEq_empty`: the
  cancellation family of the empty system has one member, the empty table, and its generalised
  equation is empty.

## Implementation notes

The second word `z_t z_t⁻¹` of an inequation is a trivial equation. It is there because a
generalised equation only forces the word of a base to be reduced as written, and a variable
occurring once has no base: with the word `t z_t⁻¹` alone, the items in the word of `z_t` could
be nonempty and still cancel each other (for `x y ≠ 1` the items `a`, `a⁻¹`, `a`, `a⁻¹` would
solve the generalised equation of the table `(z₁, z₂, z₂⁻¹ z₁⁻¹)` with `x y = 1`). With the second
occurrence, the word of `z_t` carries a base, hence is nonempty and reduced in every solution, so
`z_t ≠ 1`.

A variable of `X` which occurs neither in an equation nor in an inequation has the empty word
map.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.2, Lemmas 13 and 14.
* V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups and
  monoids with involution*, Inform. and Comput. 251 (2016), §1.3 (an inequation as an equation
  with a new variable different from `1`).
-/

public section

namespace TauCeti

namespace EqIneqSystem

open GenEq GroupAlgGeom
open FreeGroup (substituteVars)

variable {X Z A : Type*} [DecidableEq X] [DecidableEq A]

/-- The words of a system of equations and inequations, in the variables of the system and one
new *witness* variable `z_k` for each inequation: the reduced word of each equation, and for the
`k`-th inequation `t ≠ 1` the words `t z_k⁻¹` and `z_k z_k⁻¹`. -/
def toWords (S : EqIneqSystem X A) : List (List (((X ⊕ Fin S.ineqs.length) ⊕ A) × Bool)) :=
  S.eqs.map (fun e => e.toWord.map (Prod.map (Sum.map Sum.inl id) id)) ++
    (List.finRange S.ineqs.length).flatMap fun k =>
      [S.ineqs[k].toWord.map (Prod.map (Sum.map Sum.inl id) id) ++ [(Sum.inl (Sum.inr k), false)],
        [(Sum.inl (Sum.inr k), true), (Sum.inl (Sum.inr k), false)]]

/-- The words of a system are, in order, the reduced words of its equations and, for each
inequation `t ≠ 1` in turn, the words `t z_k⁻¹` and `z_k z_k⁻¹`. -/
theorem toWords_def (S : EqIneqSystem X A) :
    S.toWords = S.eqs.map (fun e => e.toWord.map (Prod.map (Sum.map Sum.inl id) id)) ++
      (List.finRange S.ineqs.length).flatMap fun k =>
        [S.ineqs[k].toWord.map (Prod.map (Sum.map Sum.inl id) id) ++
            [(Sum.inl (Sum.inr k), false)],
          [(Sum.inl (Sum.inr k), true), (Sum.inl (Sum.inr k), false)]] := (rfl)

/-- The words of a system are the reduced words of its equations and, for the `k`-th inequation
`t ≠ 1`, the words `t z_k⁻¹` and `z_k z_k⁻¹`. -/
theorem mem_toWords {S : EqIneqSystem X A} {w : List (((X ⊕ Fin S.ineqs.length) ⊕ A) × Bool)} :
    w ∈ S.toWords ↔ (∃ e ∈ S.eqs, e.toWord.map (Prod.map (Sum.map Sum.inl id) id) = w) ∨
      ∃ k : Fin S.ineqs.length, S.ineqs[k].toWord.map (Prod.map (Sum.map Sum.inl id) id) ++
          [(Sum.inl (Sum.inr k), false)] = w ∨
        [(Sum.inl (Sum.inr k), true), (Sum.inl (Sum.inr k), false)] = w := by
  simp only [toWords, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.not_mem_nil, or_false, eq_comm (a := w)]

/-- The empty system has no words. -/
@[simp]
theorem toWords_empty : (empty X A).toWords = [] := by
  simp [toWords]

/-- The empty system has no words, so no occurrences of letters. -/
instance : IsEmpty (Fin (empty X A).toWords.length) := by
  rw [toWords_empty, List.length_nil]
  infer_instance

/-- A system has one word for each equation and two for each inequation. -/
@[simp]
theorem length_toWords (S : EqIneqSystem X A) :
    S.toWords.length = S.eqs.length + 2 * S.ineqs.length := by
  simp [toWords, List.length_flatMap, mul_comm]

omit [DecidableEq X] [DecidableEq A] in
/-- Mapping a function over the indices of the inequations of a system is mapping it over the
inequations. -/
private theorem map_finRange_getElem_ineqs {β : Type*} (S : EqIneqSystem X A)
    (f : FreeGroup (X ⊕ A) → β) :
    (List.finRange S.ineqs.length).map (fun k => f S.ineqs[k]) = S.ineqs.map f := by
  conv_rhs => rw [← List.map_getElem_finRange S.ineqs]
  rw [List.map_map]
  rfl

/-- The total length of the words of a system: the lengths of the reduced words of its equations
and inequations, and three letters for each inequation. -/
theorem sum_length_toWords (S : EqIneqSystem X A) :
    (S.toWords.map List.length).sum = (S.eqs.map fun e => e.toWord.length).sum +
      (S.ineqs.map fun e => e.toWord.length).sum + 3 * S.ineqs.length := by
  simp only [toWords, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    List.length_map, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.length_append, List.length_cons,
    List.length_nil, List.sum_map_add, S.map_finRange_getElem_ineqs fun e => e.toWord.length,
    List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
  lia

/-- The size of the words of a system: `(l - 1) l` for each equation of length `l`, and
`l (l + 1) + 2` for each inequation of length `l`. -/
theorem systemSize_toWords (S : EqIneqSystem X A) :
    systemSize S.toWords = (S.eqs.map fun e => (e.toWord.length - 1) * e.toWord.length).sum +
      (S.ineqs.map fun e => e.toWord.length * (e.toWord.length + 1)).sum + 2 * S.ineqs.length := by
  simp only [systemSize_def, toWords, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, List.length_map, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_append,
    List.length_cons, List.length_nil, Nat.add_sub_cancel, List.sum_map_add,
    S.map_finRange_getElem_ineqs fun e => e.toWord.length * (e.toWord.length + 1),
    List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
  lia

/-- The size of the words of a system is at most `N ^ 2`, for the total length `N` of these
words. -/
theorem systemSize_toWords_le (S : EqIneqSystem X A) :
    systemSize S.toWords ≤ ((S.eqs.map fun e => e.toWord.length).sum +
      (S.ineqs.map fun e => e.toWord.length).sum + 3 * S.ineqs.length) ^ 2 := by
  rw [← sum_length_toWords, sq]
  exact (systemSize_le _).trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

section Eval

variable {G : Type*} [Group G]

/-- An assignment of the variables and of the witnesses solves the words of a system exactly when
it solves the equations and each witness is the value of its inequation. -/
theorem forall_mem_toWords_eval_eq_one_iff (S : EqIneqSystem X A) (v : X ⊕ Fin S.ineqs.length → G)
    (c : A → G) :
    (∀ w ∈ S.toWords, eval v c (FreeGroup.mk w) = 1) ↔
      (∀ e ∈ S.eqs, eval (v ∘ Sum.inl) c e = 1) ∧
        ∀ k : Fin S.ineqs.length, eval (v ∘ Sum.inl) c S.ineqs[k] = v (Sum.inr k) := by
  have hmk (e : FreeGroup (X ⊕ A)) :
      FreeGroup.mk (e.toWord.map (Prod.map (Sum.map Sum.inl id) id)) =
        FreeGroup.map (Sum.map (Sum.inl : X → X ⊕ Fin S.ineqs.length) id) e := by
    conv_rhs => rw [← FreeGroup.mk_toWord (x := e)]
    rw [FreeGroup.map.mk]
    rfl
  have h₁ (k : Fin S.ineqs.length) : eval v c (FreeGroup.mk
      (S.ineqs[k].toWord.map (Prod.map (Sum.map Sum.inl id) id) ++
        [(Sum.inl (Sum.inr k), false)])) = eval (v ∘ Sum.inl) c S.ineqs[k] * (v (Sum.inr k))⁻¹ := by
    rw [← FreeGroup.mul_mk, map_mul, hmk, eval_map_sumMap, eval_eq_lift v,
      FreeGroup.lift_mk_singleton]
    rfl
  have h₂ (k : Fin S.ineqs.length) :
      eval v c (FreeGroup.mk [(Sum.inl (Sum.inr k), true), (Sum.inl (Sum.inr k), false)]) = 1 := by
    simp [eval_eq_lift, FreeGroup.lift_mk]
  simp only [toWords, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap,
    List.mem_finRange, List.forall_mem_cons, h₁, h₂, hmk, eval_map_sumMap, mul_inv_eq_one]
  simp

/-- An assignment solves a system of equations and inequations exactly when it extends, by
nontrivial values of the witnesses, to a solution of the words of the system. -/
theorem isSolution_iff_exists_forall_mem_toWords (S : EqIneqSystem X A) (v : X → G) (c : A → G) :
    S.IsSolution v c ↔ ∃ z : Fin S.ineqs.length → G, (∀ k, z k ≠ 1) ∧
      ∀ w ∈ S.toWords, eval (Sum.elim v z) c (FreeGroup.mk w) = 1 := by
  rw [isSolution_iff]
  constructor
  · rintro ⟨he, hi⟩
    refine ⟨fun k => eval v c S.ineqs[k], fun k => hi _ (List.getElem_mem _), ?_⟩
    rw [forall_mem_toWords_eval_eq_one_iff, Sum.elim_comp_inl]
    exact ⟨he, fun k => by simp⟩
  · rintro ⟨z, hz, h⟩
    rw [forall_mem_toWords_eval_eq_one_iff, Sum.elim_comp_inl] at h
    refine ⟨h.1, fun w hw => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact (h.2 ⟨k, hk⟩).trans_ne (hz ⟨k, hk⟩)

end Eval

/-- A *cancellation scheme* of a system of equations and inequations: a partition table of the
words of the system in which the word of every occurrence of a witness is nonempty. -/
structure IsCancellationScheme (S : EqIneqSystem X A)
    (T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)) : Prop where
  /-- A cancellation scheme is a partition table of the words of the system. -/
  isPartitionTable : IsPartitionTable S.toWords T
  /-- The word of an occurrence of a witness is nonempty. -/
  ne_nil (o : Occurrence S.toWords) (k : Fin S.ineqs.length)
    (h : S.toWords[o.1][o.2].1 = Sum.inl (Sum.inr k)) : T o ≠ []

/-- A cancellation scheme is a partition table of the words of the system with nonempty
witnesses. -/
theorem isCancellationScheme_iff {S : EqIneqSystem X A}
    {T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)} :
    S.IsCancellationScheme T ↔ IsPartitionTable S.toWords T ∧
      ∀ (o : Occurrence S.toWords) (k : Fin S.ineqs.length),
        S.toWords[o.1][o.2].1 = Sum.inl (Sum.inr k) → T o ≠ [] :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The generalised equation `Ω_T` of a table of the words of a system. -/
noncomputable abbrev genEq (S : EqIneqSystem X A)
    (T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)) : GenEq A :=
  ofEntries (tableEntries S.toWords T)

/-- The word map `P_x` of a variable of a system, for a table of its words. -/
noncomputable abbrev wordMap (S : EqIneqSystem X A)
    (T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)) (x : X) :
    List ((Fin (S.genEq T).numItems ⊕ A) × Bool) :=
  GenEq.wordMap (tableEntries S.toWords T) (Sum.inl x)

/-- The word map of the witness of the `k`-th inequation of a system, for a table of its words. -/
noncomputable abbrev witnessWord (S : EqIneqSystem X A)
    (T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)) (k : Fin S.ineqs.length) :
    List ((Fin (S.genEq T).numItems ⊕ A) × Bool) :=
  GenEq.wordMap (tableEntries S.toWords T) (Sum.inr k)

variable {S : EqIneqSystem X A} {T : Occurrence S.toWords → List ((Z ⊕ A) × Bool)}

/-- In a cancellation scheme, the entries of the witnesses have nonempty words. -/
private theorem IsCancellationScheme.getElem_tableEntries_ne_nil (hT : S.IsCancellationScheme T)
    {k : Fin S.ineqs.length} (i : Fin (tableEntries S.toWords T).length)
    (hi : (tableEntries S.toWords T)[i].1.1 = Sum.inl (Sum.inr k)) :
    (tableEntries S.toWords T)[i].2 ≠ [] := by
  obtain ⟨o, ho⟩ := mem_tableEntries.1 (List.getElem_mem i.isLt)
  simp only [Fin.getElem_fin] at hi ⊢
  rw [← ho] at hi ⊢
  exact hT.ne_nil o k hi

/-- The word map of a witness is read at an entry of the witness, and the witness has a second
entry. -/
private theorem exists_witnessWord_eq (k : Fin S.ineqs.length) :
    ∃ p : Fin (tableEntries S.toWords T).length × Fin (tableEntries S.toWords T).length,
      p.1 ≠ p.2 ∧ (tableEntries S.toWords T)[p.1].1.1 = Sum.inl (Sum.inr k) ∧
      (tableEntries S.toWords T)[p.2].1.1 = Sum.inl (Sum.inr k) ∧
      S.witnessWord T k = (S.genEq T).segment (entryStart (tableEntries S.toWords T) p.1)
        (entryStart (tableEntries S.toWords T) ((p.1 : ℕ) + 1))
        (tableEntries S.toWords T)[p.1].1.2 := by
  -- The two occurrences of the witness in the word `z_k z_k⁻¹`.
  have hw : [(Sum.inl (Sum.inr k), true), (Sum.inl (Sum.inr k), false)] ∈ S.toWords :=
    mem_toWords.2 (Or.inr ⟨k, Or.inr rfl⟩)
  obtain ⟨o₁, ho₁⟩ := exists_occurrence_of_mem hw (j := 0) (by simp)
  obtain ⟨o₂, ho₂⟩ := exists_occurrence_of_mem hw (j := 1) (by simp)
  obtain ⟨i₁, hi₁⟩ := exists_getElem_tableEntries T o₁
  obtain ⟨i₂, hi₂⟩ := exists_getElem_tableEntries T o₂
  have h₁ : (tableEntries S.toWords T)[i₁].1 = (Sum.inl (Sum.inr k), true) :=
    (congrArg Prod.fst hi₁).trans ho₁
  have h₂ : (tableEntries S.toWords T)[i₂].1 = (Sum.inl (Sum.inr k), false) :=
    (congrArg Prod.fst hi₂).trans ho₂
  have h₁₂ : i₁ ≠ i₂ := by
    rintro rfl
    simpa using h₁.symm.trans h₂
  obtain ⟨k₀, hk₀, hw₀⟩ := exists_wordMap_eq _ i₁ (by rw [h₁])
  obtain ⟨k₁, hk₁, hne⟩ : ∃ k₁ : Fin (tableEntries S.toWords T).length,
      (tableEntries S.toWords T)[k₁].1.1 = Sum.inl (Sum.inr k) ∧ k₀ ≠ k₁ := by
    by_cases h : k₀ = i₁
    · exact ⟨i₂, by rw [h₂], h ▸ h₁₂⟩
    · exact ⟨i₁, by rw [h₁], h⟩
  exact ⟨(k₀, k₁), hne, hk₀, hk₁, hw₀⟩

/-- The word map of a variable, for a partition table of the words of a system, is no longer than
the total length of these words. -/
theorem length_wordMap_le (hT : IsPartitionTable S.toWords T) (x : X) :
    (S.wordMap T x).length ≤ (S.eqs.map fun e => e.toWord.length).sum +
      (S.ineqs.map fun e => e.toWord.length).sum + 3 * S.ineqs.length :=
  (hT.length_wordMap_le_sum (Sum.inl x)).trans (sum_length_toWords S).le

/-- The word map of a witness, for a partition table of the words of a system, is no longer than
the total length of these words. -/
theorem length_witnessWord_le (hT : IsPartitionTable S.toWords T) (k : Fin S.ineqs.length) :
    (S.witnessWord T k).length ≤ (S.eqs.map fun e => e.toWord.length).sum +
      (S.ineqs.map fun e => e.toWord.length).sum + 3 * S.ineqs.length :=
  (hT.length_wordMap_le_sum (Sum.inr k)).trans (sum_length_toWords S).le

/-- The generalised equation of a partition table of the words of a system has at most `N ^ 2`
items, for the total length `N` of these words. -/
theorem numItems_genEq_le (hT : IsPartitionTable S.toWords T) :
    (S.genEq T).numItems ≤ ((S.eqs.map fun e => e.toWord.length).sum +
      (S.ineqs.map fun e => e.toWord.length).sum + 3 * S.ineqs.length) ^ 2 :=
  hT.numItems_ofEntries_le.trans (systemSize_toWords_le S)

/-! ### Solutions of `Ω_T` give solutions of the system -/

/-- In a cancellation scheme the word map of a witness is nonempty: a witness is never assigned
zero items. -/
theorem IsCancellationScheme.witnessWord_ne_nil (hT : S.IsCancellationScheme T)
    (k : Fin S.ineqs.length) : S.witnessWord T k ≠ [] := by
  obtain ⟨p, -, hp, -, hw⟩ := exists_witnessWord_eq (T := T) k
  rw [hw, ← List.length_pos_iff, length_segment_entryStart _ p.1.isLt]
  exact List.length_pos_iff.2 (hT.getElem_tableEntries_ne_nil p.1 hp)

/-- In a partition table of the words of a system, the word map of a witness is empty exactly when
the word of an occurrence of the witness is empty. -/
theorem witnessWord_eq_nil_iff (hT : IsPartitionTable S.toWords T) {k : Fin S.ineqs.length}
    {o : Occurrence S.toWords} (ho : S.toWords[o.1][o.2].1 = Sum.inl (Sum.inr k)) :
    S.witnessWord T k = [] ↔ T o = [] := by
  obtain ⟨p, -, hp, -, hw⟩ := exists_witnessWord_eq (T := T) k
  rw [hw, ← List.length_eq_zero_iff, length_segment_entryStart _ p.1.isLt,
    List.length_eq_zero_iff]
  exact hT.eq_nil_iff_of_mem_tableEntries (List.getElem_mem p.1.isLt)
    (mem_tableEntries.2 ⟨o, rfl⟩) (hp.trans ho.symm)

/-- A cancellation scheme is a partition table of the words of the system in which the word map of
every witness is nonempty. -/
theorem isCancellationScheme_iff_witnessWord_ne_nil :
    S.IsCancellationScheme T ↔ IsPartitionTable S.toWords T ∧ ∀ k, S.witnessWord T k ≠ [] :=
  ⟨fun hT => ⟨hT.isPartitionTable, hT.witnessWord_ne_nil⟩,
    fun h => ⟨h.1, fun _ k ho => (witnessWord_eq_nil_iff h.1 ho).not.1 (h.2 k)⟩⟩

/-- In a solution of the generalised equation of a partition table of the words of a system, the
word of every witness is reduced as written: it is empty, or it spans a base. -/
theorem isReduced_substituteVars_witnessWord (hT : IsPartitionTable S.toWords T)
    (U : (S.genEq T).Solution) (k : Fin S.ineqs.length) :
    FreeGroup.IsReduced (substituteVars U.word (S.witnessWord T k)) := by
  obtain ⟨p, hne, h₁, h₂, hw⟩ := exists_witnessWord_eq (T := T) k
  by_cases h : (tableEntries S.toWords T)[p.1].2 = []
  · rw [hw, List.eq_nil_of_length_eq_zero ((length_segment_entryStart _ p.1.isLt _).trans
      (List.length_eq_zero_iff.2 h))]
    exact FreeGroup.IsReduced.nil
  -- The two entries of the witness have nonempty words, so they are joined by dual bases.
  have hp : IsVarPair (tableEntries S.toWords T) p := (isVarPair_iff _).2 ⟨hne,
    (congrArg Sum.isLeft h₁).trans rfl, h₁.trans h₂.symm, h,
    (hT.eq_nil_iff_of_mem_tableEntries (List.getElem_mem p.1.isLt) (List.getElem_mem p.2.isLt)
      (h₁.trans h₂.symm)).not.1 h⟩
  rw [hw]
  exact (U.isReduced_subst _ (mem_equations_ofEntries_of_isVarPair _ hp)).1

/-- A solution of the generalised equation of a cancellation scheme gives every witness a
nontrivial value: its word is nonempty and reduced as written. -/
theorem IsCancellationScheme.mk_substituteVars_witnessWord_ne_one (hT : S.IsCancellationScheme T)
    (U : (S.genEq T).Solution) (k : Fin S.ineqs.length) :
    FreeGroup.mk (substituteVars U.word (S.witnessWord T k)) ≠ 1 := fun h =>
  U.substituteVars_word_ne_nil (hT.witnessWord_ne_nil k)
    ((isReduced_substituteVars_witnessWord hT.isPartitionTable U k).eq_nil_of_mk_eq_one h)

/-- At a solution of `Ω_T*`, the word maps solve the equations of a system and give each
inequation the value of its witness. -/
private theorem forall_eval_wordMap (hT : IsPartitionTable S.toWords T) {H : Type*} [Group H]
    {ι : FreeGroup A →* H} {v : Fin (S.genEq T).numItems → H} (hv : v ∈ V ι (S.genEq T).toSystem) :
    (∀ e ∈ S.eqs, eval (fun x => eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x)))
      (ι ∘ FreeGroup.of) e = 1) ∧
    ∀ k : Fin S.ineqs.length, eval (fun x => eval v (ι ∘ FreeGroup.of)
      (FreeGroup.mk (S.wordMap T x))) (ι ∘ FreeGroup.of) S.ineqs[k] =
        eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.witnessWord T k)) :=
  (forall_mem_toWords_eval_eq_one_iff S _ _).1 fun _ hw => hT.eval_eq_one_of_mem_V hv hw

/-- **Kharlampovich–Myasnikov, Lemma 14(4).** If `v` is a solution of `Ω_T*` in a group `H` with a
homomorphism `ι : F(A) → H`, for a partition table `T` of the words of a system, then the word
maps give a solution `x ↦ P_x(v)` of the equations of the system in `H`. -/
theorem eval_eq_one_of_mem_V (hT : IsPartitionTable S.toWords T) {H : Type*} [Group H]
    {ι : FreeGroup A →* H} {v : Fin (S.genEq T).numItems → H} (hv : v ∈ V ι (S.genEq T).toSystem)
    {e : FreeGroup (X ⊕ A)} (he : e ∈ S.eqs) :
    eval (fun x => eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x))) (ι ∘ FreeGroup.of) e =
      1 :=
  (forall_eval_wordMap hT hv).1 e he

/-- If `v` is a solution of `Ω_T*` in a group `H` with a homomorphism `ι : F(A) → H`, for a
partition table `T` of the words of a system, then the word maps give each inequation of the
system the value at `v` of the word map of its witness. -/
theorem eval_getElem_ineqs_of_mem_V (hT : IsPartitionTable S.toWords T) {H : Type*} [Group H]
    {ι : FreeGroup A →* H} {v : Fin (S.genEq T).numItems → H} (hv : v ∈ V ι (S.genEq T).toSystem)
    (k : Fin S.ineqs.length) :
    eval (fun x => eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x))) (ι ∘ FreeGroup.of)
      S.ineqs[k] = eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.witnessWord T k)) :=
  (forall_eval_wordMap hT hv).2 k

/-- If `v` is a solution of `Ω_T*` in a group `H` with a homomorphism `ι : F(A) → H`, for a
partition table `T` of the words of a system, then the word maps give a solution `x ↦ P_x(v)` of
the system in `H`, inequations included, exactly when the witnesses have nontrivial values at
`v`. -/
theorem isSolution_iff_of_mem_V (hT : IsPartitionTable S.toWords T) {H : Type*} [Group H]
    {ι : FreeGroup A →* H} {v : Fin (S.genEq T).numItems → H} (hv : v ∈ V ι (S.genEq T).toSystem) :
    S.IsSolution (fun x => eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x)))
      (ι ∘ FreeGroup.of) ↔
      ∀ k, eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.witnessWord T k)) ≠ 1 := by
  rw [isSolution_iff]
  refine ⟨fun h k => eval_getElem_ineqs_of_mem_V hT hv k ▸ h.2 _ (List.getElem_mem _),
    fun h => ⟨fun e he => eval_eq_one_of_mem_V hT hv he, fun w hw => ?_⟩⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
  exact (eval_getElem_ineqs_of_mem_V hT hv ⟨k, hk⟩).trans_ne (h ⟨k, hk⟩)

/-- A solution `U` of the generalised equation of a cancellation scheme of a system gives, through
the word maps, the solution `x ↦ P_x(U)` of the system in `F(A)`, inequations included. -/
theorem IsCancellationScheme.isSolution (hT : S.IsCancellationScheme T) (U : (S.genEq T).Solution) :
    S.IsSolution (fun x => FreeGroup.mk (substituteVars U.word (S.wordMap T x))) FreeGroup.of := by
  have h := (isSolution_iff_of_mem_V hT.isPartitionTable U.point_mem_V).2 fun k => by
    simpa only [MonoidHom.coe_id, Function.id_comp, Solution.eval_point_mk] using
      hT.mk_substituteVars_witnessWord_ne_one U k
  simpa only [MonoidHom.coe_id, Function.id_comp, Solution.eval_point_mk] using h

/-! ### The cancellation family -/

section Family

variable [Finite A]

open scoped Classical in
/-- The cancellation family of a system of equations and inequations: the finite set of its
cancellation schemes with letters `Z = Fin (systemSize S.toWords)`. Each member `T` gives the
generalised equation `S.genEq T` and the word maps `S.wordMap T`. -/
noncomputable def cancellationFamily (S : EqIneqSystem X A) :
    Finset (Occurrence S.toWords → List ((Fin (systemSize S.toWords) ⊕ A) × Bool)) :=
  (GenEq.cancellationFamily S.toWords).filter fun T =>
    ∀ (o : Occurrence S.toWords) (k : Fin S.ineqs.length),
      S.toWords[o.1][o.2].1 = Sum.inl (Sum.inr k) → T o ≠ []

/-- The members of the cancellation family are the cancellation schemes. -/
@[simp]
theorem mem_cancellationFamily {S : EqIneqSystem X A}
    {T : Occurrence S.toWords → List ((Fin (systemSize S.toWords) ⊕ A) × Bool)} :
    T ∈ S.cancellationFamily ↔ S.IsCancellationScheme T := by
  rw [cancellationFamily, Finset.mem_filter, GenEq.mem_cancellationFamily, isCancellationScheme_iff]

/-- The cancellation family of a system is contained in the cancellation family of its words. -/
theorem cancellationFamily_subset (S : EqIneqSystem X A) :
    S.cancellationFamily ⊆ GenEq.cancellationFamily S.toWords :=
  Finset.filter_subset _ _

end Family

/-- The cancellation family of a system over a finite alphabet `A` whose words have size
`n = systemSize S.toWords` has at most `(2 (n + |A|) + 1) ^ n` members: there are at most that
many cancellation schemes with letters `Z = Fin n`. -/
theorem card_cancellationFamily_le [Fintype A] (S : EqIneqSystem X A) :
    S.cancellationFamily.card ≤
      (2 * (systemSize S.toWords + Fintype.card A) + 1) ^ systemSize S.toWords :=
  (Finset.card_le_card (cancellationFamily_subset S)).trans (GenEq.card_cancellationFamily_le _)

/-! ### The empty system -/

section Empty

variable (T : Occurrence (empty X A).toWords → List ((Z ⊕ A) × Bool))

/-- Every table of the words of the empty system is a cancellation scheme. -/
@[simp]
theorem isCancellationScheme_empty : (empty X A).IsCancellationScheme T :=
  ⟨⟨isEmptyElim, isEmptyElim, isEmptyElim, fun o => isEmptyElim o, fun o => isEmptyElim o⟩,
    fun o => isEmptyElim o⟩

/-- The generalised equation of a table of the empty system is the empty generalised equation. -/
theorem genEq_empty : (empty X A).genEq T = GenEq.empty :=
  eq_empty_of_numItems_eq_zero (by rw [numItems_ofEntries, length_flatMap_tableEntries]; simp)

/-- The word maps of a table of the empty system are empty. -/
@[simp]
theorem wordMap_empty (x : X) : (empty X A).wordMap T x = [] :=
  wordMap_eq_nil _ fun k => (mem_tableEntries.1 (List.getElem_mem k.isLt)).elim fun o _ =>
    isEmptyElim o

/-- The cancellation family of the empty system has exactly one member, the empty table. -/
@[simp]
theorem cancellationFamily_empty [Finite A] :
    (empty X A).cancellationFamily = {fun o => isEmptyElim o} :=
  Finset.eq_singleton_iff_unique_mem.2
    ⟨mem_cancellationFamily.2 (isCancellationScheme_empty _), fun _ _ => Subsingleton.elim _ _⟩

end Empty

/-! ### Examples -/

section Examples

/-- For the empty system the empty generalised equation supplies the trivial cancellation
scheme. -/
example {X A : Type*} [DecidableEq X] [DecidableEq A] [Finite A] :
    ∃ T ∈ (empty X A).cancellationFamily, (empty X A).genEq T = GenEq.empty :=
  ⟨fun o => isEmptyElim o, by simp, genEq_empty _⟩

/-- For the inequation `x ≠ 1`, the table with empty words is a partition table of the words
`x z⁻¹`, `z z⁻¹` of the system. -/
example {X A : Type*} [DecidableEq X] [DecidableEq A] (x : X) :
    IsPartitionTable (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).toWords
      (fun _ => ([] : List ((Empty ⊕ A) × Bool))) := by
  refine ⟨fun _ => .nil, fun _ => by
    rw [List.flatMap_eq_nil_iff.2 fun _ _ => rfl]
    exact FreeGroup.one_eq_mk.symm, fun _ => by simp,
    fun o a h => ?_, fun _ _ _ => Iff.rfl⟩
  -- Every letter of the words of `x ≠ 1` is a variable or a witness.
  have hl : ∀ w ∈ (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).toWords, ∀ l ∈ w,
      l.1.isLeft := by
    intro w hw l hl
    obtain ⟨e, he, -⟩ | ⟨k, rfl | rfl⟩ := mem_toWords.1 hw
    · simp at he
    · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.getElem_fin,
        Fin.val_eq_zero, List.getElem_cons_zero, FreeGroup.toWord_of, List.map_cons,
        Prod.map_apply, Sum.map_inl, id_eq, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> rfl
  simp only [Fin.getElem_fin] at h
  simpa [h] using hl _ (List.getElem_mem o.1.isLt) _ (List.getElem_mem o.2.isLt)

/-- For the inequation `x ≠ 1`, the table with empty words is not a cancellation scheme: it
assigns the witness zero items. -/
example {X A : Type*} [DecidableEq X] [DecidableEq A] (x : X) :
    ¬ (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsCancellationScheme
      (fun _ => ([] : List ((Empty ⊕ A) × Bool))) := by
  intro h
  -- The first letter of the word `z z⁻¹` of the witness.
  obtain ⟨o, ho⟩ := exists_occurrence_of_mem
    ((mem_toWords (S := (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A))).2
      (Or.inr ⟨⟨0, Nat.zero_lt_one⟩, Or.inr rfl⟩)) (j := 0) (by simp)
  exact h.ne_nil o ⟨0, Nat.zero_lt_one⟩ (by rw [ho]; rfl) rfl

/-- The table `(a | a⁻¹; a | a⁻¹)` of the words `x z⁻¹`, `z z⁻¹` of `x ≠ 1` over `F(a)`. -/
private def xNeOneTable (o : Occurrence (⟨[], [FreeGroup.of (Sum.inl 0)]⟩ :
    EqIneqSystem (Fin 1) (Fin 1)).toWords) :
    List ((Fin (systemSize (⟨[], [FreeGroup.of (Sum.inl 0)]⟩ :
      EqIneqSystem (Fin 1) (Fin 1)).toWords) ⊕ Fin 1) × Bool) :=
  [(Sum.inr 0, decide ((o.2 : ℕ) = 0))]

/-- The inequation `x ≠ 1` over `F(a)` has a cancellation scheme, assigning `a` to `x` and to the
witness. -/
example : xNeOneTable ∈ (⟨[], [FreeGroup.of (Sum.inl 0)]⟩ :
    EqIneqSystem (Fin 1) (Fin 1)).cancellationFamily :=
  mem_cancellationFamily.2 ⟨⟨fun _ => .singleton, by decide, by decide, by decide, by decide⟩,
    by decide⟩

end Examples

end EqIneqSystem

end TauCeti
