/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.RE
public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.Basic
public import TauCeti.GroupTheory.FreeGroup.Substitution

/-!
# Bounded solvability of systems over a free group is primitive recursive

A finite system of equations and inequations over the free group `F(A)` on a finite alphabet
is coded by its two lists of words in the variables and the letters of `A`; the words are
arbitrary, possibly unreduced. The relation

> the system coded by `p` has a solution in `F(A)` all of whose values have length at most `N`

is primitive recursive in `p` and `N`
(`TauCeti.EqIneqSystem.primrecRel_exists_norm_le_isSolution`). The variables are numbered by
natural numbers, so the statement is uniform in the number of variables; the version for a fixed
primitively encodable variable alphabet follows
(`TauCeti.EqIneqSystem.primrecRel_exists_norm_le_isSolution_of_primcodable`).

Consequently, a computable bound on the length of a shortest solution makes solvability a
computable predicate of the code
(`TauCeti.EqIneqSystem.computablePred_exists_isSolution_of_norm_le`).

The procedure is the exhaustive search by which a recursive bound on the length of a shortest
solution yields Makanin's decidability theorem: there are finitely
many tuples of words of length at most `N` over the finite alphabet `A`
(`FreeGroup.wordsOfLengthLE`), only the variables occurring in the system matter
(`TauCeti.EqIneqSystem.eval_mk_congr`), and each tuple is tested by substitution and free
reduction.

## References

* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR-Izv. 25 (1985), 75–88, §3, proof of Theorem 1.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, §4.4.
-/

public section

namespace TauCeti.EqIneqSystem

open FreeGroup

variable {A : Type*}

/-- A number exceeding every variable of a word in variables numbered by `ℕ`. -/
private def varBound (w : List ((ℕ ⊕ A) × Bool)) : ℕ :=
  w.foldr (fun y m => max (Sum.elim Nat.succ (fun _ => 0) y.1) m) 0

private theorem lt_varBound {w : List ((ℕ ⊕ A) × Bool)} {x : ℕ} {b : Bool}
    (h : (Sum.inl x, b) ∈ w) : x < varBound w := by
  induction w with
  | nil => simp at h
  | cons y w ih =>
    rw [varBound, List.foldr_cons, ← varBound]
    rcases List.mem_cons.mp h with rfl | h
    · exact lt_max_of_lt_left (Nat.lt_succ_self x)
    · exact lt_max_of_lt_right (ih h)

private theorem primrec_varBound [Primcodable A] :
    Primrec (varBound : List ((ℕ ⊕ A) × Bool) → ℕ) :=
  Primrec.list_foldr .id (.const 0) <| .to₂ <| Primrec.nat_max.comp
    (Primrec.sumCasesOn (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.succ.comp Primrec.snd).to₂ (Primrec.const 0).to₂)
    (Primrec.snd.comp Primrec.snd)

/-- The tuples of words tested for a system: one word of length at most `N` for each variable
below a bound on the variables of the system. -/
private noncomputable def candidates [Finite A]
    (p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool))) (N : ℕ) :
    List (List (List (A × Bool))) :=
  (List.replicate (varBound (p.1 ++ p.2).flatten) (wordsOfLengthLE A N)).sections

private theorem mem_candidates [Finite A]
    {p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool))} {N : ℕ}
    {u : List (List (A × Bool))} :
    u ∈ candidates p N ↔ u.length = varBound (p.1 ++ p.2).flatten ∧ ∀ w ∈ u, w.length ≤ N := by
  simp [candidates, List.mem_sections_replicate]

private theorem primrec₂_candidates [Finite A] [Primcodable A] :
    Primrec₂ (candidates (A := A)) :=
  (Primrec.list_sections.comp (Primrec.list_replicate.comp
    (primrec_varBound.comp (Primrec.list_flatten.comp
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))))
    (primrec_wordsOfLengthLE.comp Primrec.snd))).to₂

/-- A table of words solves a system exactly when its substitution into every equation
reduces to the empty word and its substitution into every inequation does not. -/
private theorem isSolution_mk_getD_iff
    (p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool)))
    (u : List (List (A × Bool))) :
    (ofWords p).IsSolution (fun x => FreeGroup.mk (u.getD x [])) of ↔
      (∀ w ∈ p.1, FreeGroup.mk (substituteVars (fun x => u.getD x []) w) = 1) ∧
        ∀ w ∈ p.2, ¬ FreeGroup.mk (substituteVars (fun x => u.getD x []) w) = 1 := by
  simp [isSolution_ofWords_iff, mk_substituteVars, eval_eq_lift]

private theorem primrecRel_isSolution_mk_getD [Primcodable A] :
    PrimrecRel fun (u : List (List (A × Bool)))
        (p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool))) =>
      (ofWords p).IsSolution (fun x => FreeGroup.mk (u.getD x [])) of := by
  have h : PrimrecRel fun (w : List ((ℕ ⊕ A) × Bool)) (u : List (List (A × Bool))) =>
      FreeGroup.mk (substituteVars (fun x => u.getD x []) w) = 1 :=
    primrecPred_mk_eq_one.comp (primrec₂_substituteVars_getD.comp Primrec.snd Primrec.fst)
  exact ((h.forall_mem_list.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).and
    (h.not.forall_mem_list.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)).of_eq
      fun q => (isSolution_mk_getD_iff q.2 q.1).symm

/-- A system has a solution with all values of length at most `N` exactly when one of the
finitely many tested tuples of words solves it. -/
private theorem exists_norm_le_isSolution_iff [Finite A] [DecidableEq A]
    (p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool))) (N : ℕ) :
    (∃ v : ℕ → FreeGroup A, (∀ x, (v x).norm ≤ N) ∧ (ofWords p).IsSolution v of) ↔
      ∃ u ∈ candidates p N,
        (ofWords p).IsSolution (fun x => FreeGroup.mk (u.getD x [])) of := by
  constructor
  · rintro ⟨v, hv, hs⟩
    refine ⟨(List.range (varBound (p.1 ++ p.2).flatten)).map fun x => (v x).toWord,
      mem_candidates.mpr ⟨by simp, by simpa [norm] using fun x _ => hv x⟩,
      (isSolution_ofWords_congr _ fun w hw x b hx => ?_).mpr hs⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (lt_varBound (List.mem_flatten_of_mem hw hx))]
    exact mk_toWord
  · rintro ⟨u, hu, hs⟩
    refine ⟨_, fun x => norm_mk_le.trans ?_, hs⟩
    rw [List.getD_eq_getElem?_getD]
    cases hx : u[x]? with
    | none => simp
    | some w => simpa using (mem_candidates.mp hu).2 w (List.mem_of_getElem? hx)

section Primrec

variable [Finite A] [Primcodable A] [DecidableEq A]

/-- **Bounded solvability is primitive recursive.** For a finite alphabet `A`, it is a
primitive-recursive relation of a pair of lists of words in variables numbered by `ℕ` and
letters of `A`, and of a number `N`, whether the system with these equations and inequations
has a solution in `F(A)` all of whose values have length at most `N`. The words need not be
reduced, and the number of variables is not fixed. -/
theorem primrecRel_exists_norm_le_isSolution :
    PrimrecRel fun (p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool))) (N : ℕ) =>
      ∃ v : ℕ → FreeGroup A, (∀ x, (v x).norm ≤ N) ∧ (ofWords p).IsSolution v of := by
  exact (primrecRel_isSolution_mk_getD.exists_mem_list.comp primrec₂_candidates
    Primrec.fst).of_eq fun q => (exists_norm_le_isSolution_iff q.1 q.2).symm

/-- Bounded solvability is primitive recursive for systems in a fixed primitively encodable
alphabet of variables. -/
theorem primrecRel_exists_norm_le_isSolution_of_primcodable {X : Type*} [Primcodable X] :
    PrimrecRel fun (p : List (List ((X ⊕ A) × Bool)) × List (List ((X ⊕ A) × Bool))) (N : ℕ) =>
      ∃ v : X → FreeGroup A, (∀ x, (v x).norm ≤ N) ∧ (ofWords p).IsSolution v of := by
  have hy : Primrec fun y : (X ⊕ A) × Bool => (Sum.map Encodable.encode id y.1, y.2) :=
    Primrec.pair ((Primrec.sumCasesOn Primrec.fst
      (Primrec.sumInl.comp (Primrec.encode.comp Primrec.snd)).to₂
      (Primrec.sumInr.comp Primrec.snd).to₂).of_eq fun y => by cases y.1 <;> rfl) Primrec.snd
  have hr : Primrec fun w : List ((X ⊕ A) × Bool) =>
      w.map fun y => (Sum.map Encodable.encode id y.1, y.2) :=
    Primrec.list_map Primrec.id (hy.comp Primrec.snd).to₂
  have hrs : Primrec fun l : List (List ((X ⊕ A) × Bool)) =>
      l.map (List.map fun y => (Sum.map Encodable.encode id y.1, y.2)) :=
    Primrec.list_map Primrec.id (hr.comp Primrec.snd).to₂
  refine (primrecRel_exists_norm_le_isSolution.comp ((hrs.comp Primrec.fst).pair
    (hrs.comp Primrec.snd) |>.comp Primrec.fst) Primrec.snd).of_eq fun q => ?_
  simp only [← relabel_ofWords, isSolution_relabel]
  constructor
  · rintro ⟨v, hv, hs⟩
    exact ⟨v ∘ Encodable.encode, fun x => hv _, hs⟩
  · rintro ⟨v, hv, hs⟩
    refine ⟨fun n => (Encodable.decode n).elim 1 v, fun n => ?_, by
      simpa [Function.comp_def] using hs⟩
    cases hn : (Encodable.decode n : Option X) <;> simp [hn, hv]

/-- **Solvability is decidable given a computable length bound.** If `B` is a computable
function of the code of a system such that every solvable system `p` has a solution all of
whose values have length at most `B p`, then solvability in `F(A)` is a computable predicate
of the code. -/
theorem computablePred_exists_isSolution_of_norm_le
    {B : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool)) → ℕ} (hB : Computable B)
    (h : ∀ p, (∃ v : ℕ → FreeGroup A, (ofWords p).IsSolution v of) →
      ∃ v : ℕ → FreeGroup A, (∀ x, (v x).norm ≤ B p) ∧ (ofWords p).IsSolution v of) :
    ComputablePred fun p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool)) =>
      ∃ v : ℕ → FreeGroup A, (ofWords p).IsSolution v of := by
  obtain ⟨_, hR⟩ := primrecRel_exists_norm_le_isSolution (A := A)
  exact (Computable.computablePred (hR.to_comp.comp (Computable.id.pair hB))).of_eq
    fun p => ⟨fun ⟨v, _, hv⟩ => ⟨v, hv⟩, h p⟩

end Primrec

section Examples

variable [DecidableEq A]

/-- The inequation `x ≠ 1` has a solution with values of length at most `N` exactly when
`N` is positive and the alphabet is nonempty: the bound matters, and at rank zero every
inequation fails. -/
theorem exists_norm_le_isSolution_var_ne_one_iff (N : ℕ) :
    (∃ v : ℕ → FreeGroup A, (∀ x, (v x).norm ≤ N) ∧
      (ofWords (X := ℕ) (A := A) ([], [[(Sum.inl 0, true)]])).IsSolution v of) ↔
      0 < N ∧ Nonempty A := by
  have hone : ∀ v : ℕ → FreeGroup A,
      eval v of (FreeGroup.mk [((Sum.inl 0 : ℕ ⊕ A), true)]) = v 0 := fun v => eval_of v of _
  simp only [isSolution_ofWords_iff, List.not_mem_nil, false_imp_iff, implies_true, true_and,
    List.mem_singleton, forall_eq, hone]
  constructor
  · rintro ⟨v, hv, h0⟩
    refine ⟨(Nat.pos_of_ne_zero fun h => h0 (norm_eq_zero.mp h)).trans_le (hv 0), ?_⟩
    by_contra hA
    rw [not_nonempty_iff] at hA
    exact h0 (Subsingleton.elim _ _)
  · rintro ⟨hN, ⟨a⟩⟩
    exact ⟨fun _ => of a, fun _ => by simpa using Nat.succ_le_of_lt hN, of_ne_one a⟩

/-- The empty system is solved by the all-identity assignment, of length zero. -/
example : ∃ v : ℕ → FreeGroup A, (∀ x, (v x).norm ≤ 0) ∧
    (ofWords (X := ℕ) (A := A) ([], [])).IsSolution v of :=
  ⟨fun _ => 1, by simp, by simp [isSolution_ofWords_iff]⟩

/-- The equation `[x, y] = [a, b]`, written as the unreduced word `x y x⁻¹ y⁻¹ b a b⁻¹ a⁻¹`,
has the solution `x = a`, `y = b` with values of length one. -/
example : ∃ v : ℕ → FreeGroup (Fin 2), (∀ x, (v x).norm ≤ 1) ∧
    (ofWords (X := ℕ) (A := Fin 2) ([[(Sum.inl 0, true), (Sum.inl 1, true), (Sum.inl 0, false),
      (Sum.inl 1, false), (Sum.inr 1, true), (Sum.inr 0, true), (Sum.inr 1, false),
      (Sum.inr 0, false)]], [])).IsSolution v of := by
  refine ⟨fun x => if x = 0 then of 0 else of 1, fun x => ?_, ?_⟩
  · dsimp only
    split <;> simp
  · simp [isSolution_ofWords_iff, eval_eq_lift, lift_mk]

/-- At rank zero the bound zero works for every system, so solvability over the trivial group
is a computable predicate of the code. -/
example [IsEmpty A] [Primcodable A] :
    ComputablePred fun p : List (List ((ℕ ⊕ A) × Bool)) × List (List ((ℕ ⊕ A) × Bool)) =>
      ∃ v : ℕ → FreeGroup A, (ofWords p).IsSolution v of :=
  computablePred_exists_isSolution_of_norm_le (B := fun _ => 0) (Computable.const 0)
    fun _ ⟨v, hv⟩ => ⟨v, fun _ => (norm_eq_zero.mpr (Subsingleton.elim _ _)).le, hv⟩

end Examples

end TauCeti.EqIneqSystem
