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
each inequation, together with the conditions `z_t ≠ 1`. This file reduces `S` to a finite family
of generalised equations: the *cancellation schemes* of `S` are the partition tables of the
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
* `TauCeti.EqIneqSystem.cancellationFamily`: the finite set of cancellation schemes with `|S|`
  letters.

## Main results

* `TauCeti.EqIneqSystem.isSolution_iff_exists_forall_mem_toWords`: the solutions of `S` are the
  solutions of `toWords` with nontrivial witnesses.
* `TauCeti.EqIneqSystem.length_wordMap_le`: the word maps of a partition table are no longer than
  the total length of the words of the system.
* `TauCeti.EqIneqSystem.IsCancellationScheme.mk_substituteVars_witnessWord_ne_one`: in a solution
  of the generalised equation of a scheme, every witness is nontrivial.
* `TauCeti.EqIneqSystem.isSolution_iff_of_mem_V`: in a group `H` with a homomorphism
  `F(A) → H`, a solution of `Ω_T*` gives a solution of `S` exactly when the witnesses stay
  nontrivial.
* `TauCeti.EqIneqSystem.IsCancellationScheme.isSolution`: a solution of the generalised equation
  of a scheme gives a solution of `S`, inequations included.
* `TauCeti.EqIneqSystem.card_cancellationFamily_le`: the cancellation family has at most
  `(2 (|S| + |A|) + 1) ^ |S|` members.

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

/-- The total length of the words of a system: the lengths of the reduced words of its equations
and inequations, and three letters for each inequation. -/
theorem sum_length_toWords (S : EqIneqSystem X A) :
    (S.toWords.map List.length).sum = (S.eqs.map fun e => e.toWord.length).sum +
      (S.ineqs.map fun e => e.toWord.length).sum + 3 * S.ineqs.length := by
  have h : (List.finRange S.ineqs.length).map (fun k => S.ineqs[k].toWord.length) =
      S.ineqs.map fun e => e.toWord.length := by
    conv_rhs => rw [← List.map_getElem_finRange S.ineqs]
    rw [List.map_map]
    rfl
  simp only [toWords, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    List.length_map, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.length_append, List.length_cons,
    List.length_nil, List.sum_map_add, h, List.map_const', List.length_finRange,
    List.sum_replicate, smul_eq_mul]
  lia

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

/-- In a cancellation scheme, the word map of a witness is read at an entry of the witness which,
with a second entry of the witness, forms a pair of entries joined by dual bases. -/
private theorem IsCancellationScheme.exists_isVarPair_witnessWord (hT : S.IsCancellationScheme T)
    (k : Fin S.ineqs.length) : ∃ p, IsVarPair (tableEntries S.toWords T) p ∧
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
  exact ⟨(k₀, k₁), (isVarPair_iff _).2 ⟨hne, (congrArg Sum.isLeft hk₀).trans rfl,
    hk₀.trans hk₁.symm, hT.getElem_tableEntries_ne_nil k₀ hk₀,
    hT.getElem_tableEntries_ne_nil k₁ hk₁⟩, hw₀⟩

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

/-! ### Solutions of `Ω_T` give solutions of the system -/

/-- In a cancellation scheme the word map of a witness is nonempty: a witness is never assigned
zero items. -/
theorem IsCancellationScheme.witnessWord_ne_nil (hT : S.IsCancellationScheme T)
    (k : Fin S.ineqs.length) : S.witnessWord T k ≠ [] := by
  obtain ⟨p, hp, hw⟩ := hT.exists_isVarPair_witnessWord k
  rw [hw, ← List.length_pos_iff, length_segment_entryStart _ p.1.isLt]
  exact List.length_pos_iff.2 ((isVarPair_iff _).1 hp).2.2.2.1

/-- A solution of the generalised equation of a cancellation scheme gives every witness a
nontrivial value: its word is nonempty and reduced as written. -/
theorem IsCancellationScheme.mk_substituteVars_witnessWord_ne_one (hT : S.IsCancellationScheme T)
    (U : (S.genEq T).Solution) (k : Fin S.ineqs.length) :
    FreeGroup.mk (substituteVars U.word (S.witnessWord T k)) ≠ 1 := by
  obtain ⟨p, hp, hw⟩ := hT.exists_isVarPair_witnessWord k
  have hred := (U.isReduced_subst _ (mem_equations_ofEntries_of_isVarPair _ hp)).1
  rw [← hw] at hred
  exact fun h => U.substituteVars_word_ne_nil (hT.witnessWord_ne_nil k)
    (hred.eq_of_mk_eq FreeGroup.IsReduced.nil (h.trans FreeGroup.one_eq_mk))

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
partition table `T` of the words of a system, then the word maps give a solution `x ↦ P_x(v)` of
the system in `H`, inequations included, exactly when the witnesses have nontrivial values at
`v`. -/
theorem isSolution_iff_of_mem_V (hT : IsPartitionTable S.toWords T) {H : Type*} [Group H]
    {ι : FreeGroup A →* H} {v : Fin (S.genEq T).numItems → H} (hv : v ∈ V ι (S.genEq T).toSystem) :
    S.IsSolution (fun x => eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.wordMap T x)))
      (ι ∘ FreeGroup.of) ↔
      ∀ k, eval v (ι ∘ FreeGroup.of) (FreeGroup.mk (S.witnessWord T k)) ≠ 1 := by
  obtain ⟨he, hi⟩ := forall_eval_wordMap hT hv
  rw [isSolution_iff]
  refine ⟨fun h k => hi k ▸ h.2 _ (List.getElem_mem _), fun h => ⟨he, fun w hw => ?_⟩⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
  exact (hi ⟨k, hk⟩).trans_ne (h ⟨k, hk⟩)

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
cancellation schemes with letters `Z = {0, …, |S| - 1}`. Each member `T` gives the generalised
equation `S.genEq T` and the word maps `S.wordMap T`. -/
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

/-- A system over an alphabet `A` whose words have size `|S|` has at most
`(2 (|S| + |A|) + 1) ^ |S|` cancellation schemes. -/
theorem card_cancellationFamily_le [Fintype A] (S : EqIneqSystem X A) :
    S.cancellationFamily.card ≤
      (2 * (systemSize S.toWords + Fintype.card A) + 1) ^ systemSize S.toWords :=
  (Finset.card_le_card (cancellationFamily_subset S)).trans (GenEq.card_cancellationFamily_le _)

/-! ### Examples -/

section Examples

/-- For the empty system the empty generalised equation supplies the trivial cancellation
scheme. -/
example {X A : Type*} [DecidableEq X] [DecidableEq A] [Finite A] :
    ∃ T ∈ (empty X A).cancellationFamily, (empty X A).genEq T = GenEq.empty := by
  have h : IsEmpty (Fin (empty X A).toWords.length) := by
    rw [toWords_empty, List.length_nil]
    infer_instance
  refine ⟨fun _ => [], mem_cancellationFamily.2 ⟨⟨fun o => (h.false o.1).elim,
    fun i => (h.false i).elim, fun o => (h.false o.1).elim, fun o => (h.false o.1).elim,
    fun o => (h.false o.1).elim⟩, fun o => (h.false o.1).elim⟩, eq_empty_of_numItems_eq_zero ?_⟩
  rw [numItems_ofEntries, length_flatMap_tableEntries]
  simp

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

/-- The table `(a | a⁻¹ ; a | a⁻¹)` of the words `x z⁻¹`, `z z⁻¹` of `x ≠ 1` over `F(a)`. -/
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
