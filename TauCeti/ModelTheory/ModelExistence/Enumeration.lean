/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.ConsistencyProperty
import TauCeti.ModelTheory.Basic
import TauCeti.ModelTheory.Infinitary.Encoding
import Mathlib.Data.Nat.Pairing

/-!
# The fair enumeration of a consistency property

Let `C` be a consistency property over `L` and `s` a countable member of `C`. This file extends
`s` along an increasing chain of members of `C`, the **stages** `C.stage s e q n`, whose union
`C.limit s e q` contains the target of every clause of `C` whenever it contains the clause's
trigger: one chosen component of each disjunctive sentence, every component of each conjunctive
one, every Henkin-constant instance of a universal sentence, a witness to each negated
universal sentence, the reflexive equations, substitution of equals into atomic sentences, and an
equation naming each closed term by a Henkin constant. The limit contains neither `⊥` nor a
sentence together with its negation, since each of these would already lie in a stage. The limit
itself is not claimed to be a member of `C`. These are the properties from which the term model
of the model existence theorem is built.

Each stage adds at most one sentence to the previous one. A **request**
(`ConsistencyProperty.Request`) names one clause of `C` together with its parameters; the
sentences that trigger the clause are named by *sources* `ℕ ⊕ ℕ`, where `Sum.inl j` is the `j`-th
term of a sequence `e` enumerating `s`, and `Sum.inr m` is the `m`-th sentence added so far. Every
sentence of the limit is therefore named by a source that keeps naming it from some stage on, so
the requests can be enumerated in advance even though the limit is not known in advance. With
countably many function and relation symbols there are countably many requests. The schedule
`q : ℕ → Request L` is consulted at stage `n` at the request `q n.unpair.1`, so a surjective `q`
fires every request at arbitrarily late stages. For a countable `s` over a language with
countably many symbols, an enumeration `e` with `s ⊆ Set.range e` exists by
`Set.countable_iff_exists_subset_range`, and a surjective schedule by `exists_surjective_nat`.
A request fires by adding one target of its clause, chosen so that the stage stays a member of
`C`; when its triggers are present, the clause of `C` guarantees that such a target exists.

## Main definitions

* `FirstOrder.Language.ConsistencyProperty.Request`: the requests of the enumeration.
* `FirstOrder.Language.ConsistencyProperty.stage`: the stages of the enumeration.
* `FirstOrder.Language.ConsistencyProperty.limit`: their union.

## Main results

* `FirstOrder.Language.ConsistencyProperty.stage_mem`: every stage is a member.
* `FirstOrder.Language.ConsistencyProperty.monotone_stage`: the stages increase.
* `FirstOrder.Language.ConsistencyProperty.bot_notMem_limit` and
  `FirstOrder.Language.ConsistencyProperty.not_notMem_limit`: the limit contains neither `⊥` nor
  a sentence together with its negation.
* `FirstOrder.Language.ConsistencyProperty.limit_imp`, …,
  `FirstOrder.Language.ConsistencyProperty.limit_eq_name`: the limit contains the target of each
  clause whose trigger it contains, one lemma per clause.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.1.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
* `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/Henkin/CountableCompletion/FairEnumeration.lean`, which formalizes a
  fair enumeration of requests whose firing makes a classical choice and leaves its trigger in
  place. Divergences from that source: the requests name their triggers through the history of
  the enumeration rather than through a precomputed countable universe of sentences closed under
  the decomposition targets; the requests follow the clauses of `ConsistencyProperty`, which
  allows function symbols and has a naming clause for closed terms; and the schedule fires the
  request `q n.unpair.1` at stage `n` rather than sweeping prefixes.
-/

public section

universe u v u' w

namespace FirstOrder

namespace Language

open BoundedFormulaInf

namespace ConsistencyProperty

variable {L : Language.{u, v}}

/-- A **request** of the enumeration: a clause of `ConsistencyProperty` together with its
parameters. The sentences triggering the clause are named by sources `ℕ ⊕ ℕ`: `Sum.inl j` names
the `j`-th sentence of the enumeration of the starting set, and `Sum.inr m` the `m`-th sentence
added by the enumeration. -/
inductive Request (L : Language.{u, v}) : Type (max u v)
  /-- Decompose the implication named by the source. -/
  | imp (i : ℕ ⊕ ℕ)
  /-- Extract the hypothesis of the negated implication named by the source. -/
  | notImpLeft (i : ℕ ⊕ ℕ)
  /-- Extract the negated conclusion of the negated implication named by the source. -/
  | notImpRight (i : ℕ ⊕ ℕ)
  /-- Extract the `k`-th conjunct of the conjunction named by the source. -/
  | iInf (i : ℕ ⊕ ℕ) (k : ℕ)
  /-- Choose a negated conjunct of the negated conjunction named by the source. -/
  | notIInf (i : ℕ ⊕ ℕ)
  /-- Choose a disjunct of the disjunction named by the source. -/
  | iSup (i : ℕ ⊕ ℕ)
  /-- Extract the negated `k`-th disjunct of the negated disjunction named by the source. -/
  | notISup (i : ℕ ⊕ ℕ) (k : ℕ)
  /-- Instantiate the universal sentence named by the source at the Henkin constant `c`. -/
  | all (i : ℕ ⊕ ℕ) (c : ℕ)
  /-- Choose a witness to the negated universal sentence named by the source. -/
  | notAll (i : ℕ ⊕ ℕ)
  /-- Add the equation `t = t`. -/
  | eqRefl (t : L[[ℕ]].Term (Empty ⊕ Fin 0))
  /-- Substitute the equation named by `i` into the instance of `φ` named by `j`. -/
  | eqSubst (i j : ℕ ⊕ ℕ) (φ : {φ : L[[ℕ]].BoundedFormulaω Empty 1 // φ.IsAtomic})
  /-- Name the closed term `t` by a Henkin constant. -/
  | eqName (t : L[[ℕ]].Term (Empty ⊕ Fin 0))

namespace Request

/-- The data of a request, as a sum type. -/
private abbrev Data (L : Language.{u, v}) : Type (max u v) :=
  (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) ⊕ ((ℕ ⊕ ℕ) × ℕ) ⊕ (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) ⊕ ((ℕ ⊕ ℕ) × ℕ) ⊕
    ((ℕ ⊕ ℕ) × ℕ) ⊕ (ℕ ⊕ ℕ) ⊕ L[[ℕ]].Term (Empty ⊕ Fin 0) ⊕
    ((ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) × {φ : L[[ℕ]].BoundedFormulaω Empty 1 // φ.IsAtomic}) ⊕
    L[[ℕ]].Term (Empty ⊕ Fin 0)

/-- The data of a request. -/
private def toData : Request L → Data L
  | imp i => .inl i
  | notImpLeft i => .inr (.inl i)
  | notImpRight i => .inr (.inr (.inl i))
  | iInf i k => .inr (.inr (.inr (.inl (i, k))))
  | notIInf i => .inr (.inr (.inr (.inr (.inl i))))
  | iSup i => .inr (.inr (.inr (.inr (.inr (.inl i)))))
  | notISup i k => .inr (.inr (.inr (.inr (.inr (.inr (.inl (i, k)))))))
  | all i c => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (i, c))))))))
  | notAll i => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))
  | eqRefl t => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl t)))))))))
  | eqSubst i j φ =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (i, j, φ)))))))))))
  | eqName t => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr t))))))))))

/-- The request with given data. -/
private def ofData : Data L → Request L
  | .inl i => imp i
  | .inr (.inl i) => notImpLeft i
  | .inr (.inr (.inl i)) => notImpRight i
  | .inr (.inr (.inr (.inl (i, k)))) => iInf i k
  | .inr (.inr (.inr (.inr (.inl i)))) => notIInf i
  | .inr (.inr (.inr (.inr (.inr (.inl i))))) => iSup i
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (i, k))))))) => notISup i k
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (i, c)))))))) => all i c
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) => notAll i
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl t))))))))) => eqRefl t
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (i, j, φ))))))))))) =>
    eqSubst i j φ
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr t)))))))))) => eqName t

/-- With countably many function and relation symbols, there are countably many requests, so
that a surjective schedule `ℕ → Request L` exists. -/
instance [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)] :
    Countable (Request L) := by
  have : Countable (Σ l, L[[ℕ]].Relations l) := (Sum.inr_injective (α := Σ l,
    L[[ℕ]].Functions l)).countable
  exact (Function.LeftInverse.injective (f := toData) (g := ofData) fun r => by
    cases r <;> rfl).countable

instance : Nonempty (Request L) := ⟨imp (.inl 0)⟩

/-- `r.Target σ φ` says that adding `φ` answers the request `r`, when `σ` resolves its sources:
`φ` is a target of the clause of `r` at the sentences that `σ` assigns to the sources of `r`. -/
private def Target (σ : ℕ ⊕ ℕ → Option L[[ℕ]].Sentenceω) : Request L → L[[ℕ]].Sentenceω → Prop
  | imp i, φ =>
    ∃ θ ψ : L[[ℕ]].Sentenceω, σ i = some (θ.imp ψ) ∧ (φ = θ.not ∨ φ = ψ)
  | notImpLeft i, φ =>
    ∃ θ ψ : L[[ℕ]].Sentenceω, σ i = some (θ.imp ψ).not ∧ φ = θ
  | notImpRight i, φ =>
    ∃ θ ψ : L[[ℕ]].Sentenceω, σ i = some (θ.imp ψ).not ∧ φ = ψ.not
  | iInf i k, φ =>
    ∃ φs : ℕ → L[[ℕ]].Sentenceω, σ i = some (BoundedFormulaInf.iInf φs) ∧ φ = φs k
  | notIInf i, φ =>
    ∃ (φs : ℕ → L[[ℕ]].Sentenceω) (k : ℕ),
      σ i = some (BoundedFormulaInf.iInf φs).not ∧ φ = (φs k).not
  | iSup i, φ =>
    ∃ (φs : ℕ → L[[ℕ]].Sentenceω) (k : ℕ), σ i = some (BoundedFormulaInf.iSup φs) ∧ φ = φs k
  | notISup i k, φ =>
    ∃ φs : ℕ → L[[ℕ]].Sentenceω, σ i = some (BoundedFormulaInf.iSup φs).not ∧ φ = (φs k).not
  | all i c, φ =>
    ∃ θ : L[[ℕ]].BoundedFormulaω Empty 1, σ i = some θ.all ∧ φ = θ.inst (L.con c).term
  | notAll i, φ =>
    ∃ (θ : L[[ℕ]].BoundedFormulaω Empty 1) (c : ℕ),
      σ i = some θ.all.not ∧ φ = (θ.inst (L.con c).term).not
  | eqRefl t, φ => φ = equal t t
  | eqSubst i j θ, φ =>
    ∃ t t' : L[[ℕ]].Term (Empty ⊕ Fin 0),
      σ i = some (equal t t') ∧ σ j = some (θ.1.inst t) ∧ φ = θ.1.inst t'
  | eqName t, φ => ∃ c : ℕ, φ = equal (L.con c).term t

end Request

open Request

/-- The sentence named by a source, given the enumeration `e` of the starting set and the list `a`
of sentences added so far. -/
private def resolve (e : ℕ → L[[ℕ]].Sentenceω) (a : List L[[ℕ]].Sentenceω) :
    ℕ ⊕ ℕ → Option L[[ℕ]].Sentenceω
  | .inl j => some (e j)
  | .inr m => a[m]?

/-- One step of the enumeration: the sentence that the request `r` adds to the set `t`, if `r` has
a target whose addition to `t` gives a member. -/
private noncomputable def step (C : ConsistencyProperty L) (t : L[[ℕ]].Theoryω)
    (σ : ℕ ⊕ ℕ → Option L[[ℕ]].Sentenceω) (r : Request L) : Option L[[ℕ]].Sentenceω :=
  open Classical in
  if h : ∃ φ, r.Target σ φ ∧ insert φ t ∈ C.sets then some h.choose else none

private theorem step_spec {C : ConsistencyProperty L} {t : L[[ℕ]].Theoryω}
    {σ : ℕ ⊕ ℕ → Option L[[ℕ]].Sentenceω} {r : Request L} {φ : L[[ℕ]].Sentenceω}
    (h : C.step t σ r = some φ) : r.Target σ φ ∧ insert φ t ∈ C.sets := by
  unfold step at h
  split_ifs at h with h'
  exact Option.some_injective _ h ▸ h'.choose_spec

private theorem exists_step_eq_some {C : ConsistencyProperty L} {t : L[[ℕ]].Theoryω}
    {σ : ℕ ⊕ ℕ → Option L[[ℕ]].Sentenceω} {r : Request L}
    (h : ∃ φ, r.Target σ φ ∧ insert φ t ∈ C.sets) : ∃ φ, C.step t σ r = some φ :=
  ⟨h.choose, by simp [step, h]⟩

/-- The sentences added during the first `n` stages of the enumeration, in order. -/
private noncomputable def added (C : ConsistencyProperty L) (s : L[[ℕ]].Theoryω)
    (e : ℕ → L[[ℕ]].Sentenceω) (q : ℕ → Request L) : ℕ → List L[[ℕ]].Sentenceω
  | 0 => []
  | n + 1 => added C s e q n ++
    (C.step (s ∪ {φ | φ ∈ added C s e q n}) (resolve e (added C s e q n)) (q n.unpair.1)).toList

/-- The `n`-th **stage** of the enumeration of `C` starting from `s`, where `e` enumerates `s`
and `q` is the schedule of requests: `s` together with the sentences added by the first `n`
requests. -/
noncomputable def stage (C : ConsistencyProperty L) (s : L[[ℕ]].Theoryω)
    (e : ℕ → L[[ℕ]].Sentenceω) (q : ℕ → Request L) (n : ℕ) : L[[ℕ]].Theoryω :=
  s ∪ {φ | φ ∈ added C s e q n}

/-- The **limit** of the enumeration of `C` starting from `s`: the union of its stages. -/
noncomputable def limit (C : ConsistencyProperty L) (s : L[[ℕ]].Theoryω)
    (e : ℕ → L[[ℕ]].Sentenceω) (q : ℕ → Request L) : L[[ℕ]].Theoryω :=
  ⋃ n, C.stage s e q n

variable {C : ConsistencyProperty L} {s : L[[ℕ]].Theoryω} {e : ℕ → L[[ℕ]].Sentenceω}
  {q : ℕ → Request L}

/-- A sentence lies in the limit exactly when it lies in some stage. -/
@[simp]
theorem mem_limit {φ : L[[ℕ]].Sentenceω} : φ ∈ C.limit s e q ↔ ∃ n, φ ∈ C.stage s e q n :=
  Set.mem_iUnion

/-- Every stage is contained in the limit. -/
theorem stage_subset_limit (n : ℕ) : C.stage s e q n ⊆ C.limit s e q :=
  Set.subset_iUnion (C.stage s e q) n

/-- The starting set is the zeroth stage. -/
@[simp]
theorem stage_zero : C.stage s e q 0 = s := by
  simp [stage, added]

private theorem stage_succ (n : ℕ) : C.stage s e q (n + 1) = C.stage s e q n ∪
    {φ | φ ∈ C.step (C.stage s e q n) (resolve e (added C s e q n)) (q n.unpair.1)} := by
  ext φ
  simp only [stage, added, Set.mem_union, Set.mem_ofPred_eq, List.mem_append, Option.mem_toList]
  tauto

/-- Each stage is contained in the next. -/
theorem stage_subset_stage_succ (n : ℕ) : C.stage s e q n ⊆ C.stage s e q (n + 1) := by
  rw [stage_succ]
  exact Set.subset_union_left

/-- The stages of the enumeration increase. -/
theorem monotone_stage : Monotone (C.stage s e q) :=
  monotone_nat_of_le_succ stage_subset_stage_succ

/-- The starting set is contained in every stage. -/
theorem subset_stage (n : ℕ) : s ⊆ C.stage s e q n :=
  Set.subset_union_left

/-- The starting set is contained in the limit. -/
theorem subset_limit : s ⊆ C.limit s e q :=
  (subset_stage 0).trans (stage_subset_limit 0)

/-- Every stage of the enumeration starting from a member is a member. -/
theorem stage_mem (hs : s ∈ C.sets) (n : ℕ) : C.stage s e q n ∈ C.sets := by
  induction n with
  | zero => rwa [stage_zero]
  | succ n ih =>
    rw [stage_succ]
    cases h : C.step (C.stage s e q n) (resolve e (added C s e q n)) (q n.unpair.1) with
    | none => simpa using ih
    | some φ =>
      simpa [Set.union_singleton] using (step_spec h).2

/-- The limit of the enumeration starting from a member does not contain `⊥`. -/
theorem bot_notMem_limit (hs : s ∈ C.sets) : (⊥ : L[[ℕ]].Sentenceω) ∉ C.limit s e q := by
  rw [mem_limit]
  rintro ⟨n, hn⟩
  exact C.no_falsum _ (stage_mem hs n) hn

/-- The limit of the enumeration starting from a member does not contain a sentence together with
its negation. -/
theorem not_notMem_limit (hs : s ∈ C.sets) {φ : L[[ℕ]].Sentenceω} (h : φ ∈ C.limit s e q) :
    φ.not ∉ C.limit s e q := by
  rw [mem_limit] at h ⊢
  rintro ⟨m, hm⟩
  obtain ⟨n, hn⟩ := h
  exact C.no_contradiction _ (stage_mem hs (max n m)) φ (monotone_stage (le_max_left n m) hn)
    (monotone_stage (le_max_right n m) hm)

/-! ### Firing requests -/

private theorem exists_added_eq_append {n m : ℕ} (h : n ≤ m) :
    ∃ l, added C s e q m = added C s e q n ++ l := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨[], (List.append_nil _).symm⟩
  | succ m _ ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨l ++ _, by rw [added, hl, List.append_assoc]⟩

/-- Every sentence of a stage is named by a source that keeps naming it at all later stages. -/
private theorem exists_resolve_eq (he : s ⊆ Set.range e) {N : ℕ} {φ : L[[ℕ]].Sentenceω}
    (h : φ ∈ C.stage s e q N) :
    ∃ i, ∀ n, N ≤ n → resolve e (added C s e q n) i = some φ := by
  rcases h with h | h
  · obtain ⟨j, rfl⟩ := he h
    exact ⟨.inl j, fun _ _ => rfl⟩
  · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem h
    refine ⟨.inr m, fun n hn => ?_⟩
    obtain ⟨l, hl⟩ := exists_added_eq_append (C := C) (s := s) (e := e) (q := q) hn
    simp [resolve, hl, List.getElem?_append_left hm]

/-- A request whose clause has an admissible target at every stage from `N` on adds one of its
targets at some stage after `N`. -/
private theorem exists_target_mem_stage (hq : Function.Surjective q) (r : Request L) (N : ℕ)
    (h : ∀ n, N ≤ n → ∃ φ, r.Target (resolve e (added C s e q n)) φ ∧
      insert φ (C.stage s e q n) ∈ C.sets) :
    ∃ n, N ≤ n ∧ ∃ φ, r.Target (resolve e (added C s e q n)) φ ∧ φ ∈ C.limit s e q := by
  obtain ⟨i, rfl⟩ := hq r
  refine ⟨Nat.pair i N, Nat.right_le_pair i N, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_step_eq_some (h _ (Nat.right_le_pair i N))
  refine ⟨φ, (step_spec hφ).1, stage_subset_limit (Nat.pair i N + 1) ?_⟩
  rw [stage_succ, Nat.unpair_pair]
  exact .inr hφ

/-- The firing of a request with one source, as used by every decomposition clause: if the
sentence `χ` lies in the limit, and from every member containing `χ` the request `r` (built from
a source naming `χ`) can add an admissible target, then some target lies in the limit. -/
private theorem exists_target_mem_limit (hs : s ∈ C.sets) (he : s ⊆ Set.range e)
    (hq : Function.Surjective q) {χ : L[[ℕ]].Sentenceω} (hχ : χ ∈ C.limit s e q)
    (r : ℕ ⊕ ℕ → Request L) (P : L[[ℕ]].Sentenceω → Prop)
    (hr : ∀ (σ : ℕ ⊕ ℕ → Option L[[ℕ]].Sentenceω) i φ, σ i = some χ → ((r i).Target σ φ ↔ P φ))
    (hP : ∀ t ∈ C.sets, χ ∈ t → ∃ φ, P φ ∧ insert φ t ∈ C.sets) :
    ∃ φ, P φ ∧ φ ∈ C.limit s e q := by
  obtain ⟨N, hN⟩ := mem_limit.1 hχ
  obtain ⟨i, hi⟩ := exists_resolve_eq he hN
  obtain ⟨n, hn, φ, hφ, hφl⟩ := exists_target_mem_stage hq (r i) N fun n hn => by
    obtain ⟨φ, hφ, hφC⟩ := hP _ (stage_mem hs n) (monotone_stage hn hN)
    exact ⟨φ, (hr _ i φ (hi n hn)).2 hφ, hφC⟩
  exact ⟨φ, (hr _ i φ (hi n hn)).1 hφ, hφl⟩

/-- A request without sources has an admissible target in the limit. -/
private theorem exists_target_mem_limit_of_forall (hs : s ∈ C.sets) (hq : Function.Surjective q)
    (r : Request L) (P : L[[ℕ]].Sentenceω → Prop)
    (hr : ∀ (σ : ℕ ⊕ ℕ → Option L[[ℕ]].Sentenceω) φ, r.Target σ φ ↔ P φ)
    (hP : ∀ t ∈ C.sets, ∃ φ, P φ ∧ insert φ t ∈ C.sets) :
    ∃ φ, P φ ∧ φ ∈ C.limit s e q := by
  obtain ⟨n, -, φ, hφ, hφl⟩ := exists_target_mem_stage (e := e) hq r 0 fun n _ => by
    obtain ⟨φ, hφ, hφC⟩ := hP _ (stage_mem hs n)
    exact ⟨φ, (hr _ φ).2 hφ, hφC⟩
  exact ⟨φ, (hr _ φ).1 hφ, hφl⟩

/-! ### The clauses in the limit -/

variable (hs : s ∈ C.sets) (he : s ⊆ Set.range e) (hq : Function.Surjective q)
include hs he hq

/-- The limit contains the negated hypothesis or the conclusion of each of its implications. -/
theorem limit_imp {φ ψ : L[[ℕ]].Sentenceω} (h : φ.imp ψ ∈ C.limit s e q) :
    φ.not ∈ C.limit s e q ∨ ψ ∈ C.limit s e q := by
  obtain ⟨θ, hθ | rfl, hθl⟩ := exists_target_mem_limit hs he hq h Request.imp
    (fun θ => θ = φ.not ∨ θ = ψ)
    (fun σ i θ hi => by simp [Target, hi, BoundedFormulaInf.imp.injEq])
    fun t ht hφψ => (C.imp t ht φ ψ hφψ).elim (fun h => ⟨_, .inl rfl, h⟩)
      fun h => ⟨_, .inr rfl, h⟩
  exacts [.inl (hθ ▸ hθl), .inr hθl]

/-- The limit contains the hypothesis and the negated conclusion of each of its negated
implications. -/
theorem limit_not_imp {φ ψ : L[[ℕ]].Sentenceω} (h : (φ.imp ψ).not ∈ C.limit s e q) :
    φ ∈ C.limit s e q ∧ ψ.not ∈ C.limit s e q := by
  obtain ⟨_, hθ, hφ⟩ := exists_target_mem_limit hs he hq h Request.notImpLeft (· = φ)
    (fun σ i θ hi => by simp [Target, hi, BoundedFormulaInf.not, eq_comm])
    fun t ht hφψ => ⟨_, rfl, (C.not_imp t ht φ ψ hφψ).1⟩
  obtain ⟨_, rfl, hψ⟩ := exists_target_mem_limit hs he hq h Request.notImpRight (· = ψ.not)
    (fun σ i θ hi => by simp [Target, hi, BoundedFormulaInf.not])
    fun t ht hφψ => ⟨_, rfl, (C.not_imp t ht φ ψ hφψ).2⟩
  exact ⟨hθ ▸ hφ, hψ⟩

/-- The limit contains every conjunct of each of its countable conjunctions. -/
theorem limit_iInf {φs : ℕ → L[[ℕ]].Sentenceω} (h : BoundedFormulaInf.iInf φs ∈ C.limit s e q)
    (k : ℕ) : φs k ∈ C.limit s e q := by
  obtain ⟨_, rfl, hφ⟩ := exists_target_mem_limit hs he hq h (Request.iInf · k) (· = φs k)
    (fun σ i θ hi => by simp [Target, hi])
    fun t ht hφs => ⟨_, rfl, C.iInf t ht φs hφs k⟩
  exact hφ

/-- The limit contains the negation of some conjunct of each of its negated countable
conjunctions. -/
theorem limit_not_iInf {φs : ℕ → L[[ℕ]].Sentenceω}
    (h : (BoundedFormulaInf.iInf φs).not ∈ C.limit s e q) :
    ∃ k, (φs k).not ∈ C.limit s e q := by
  obtain ⟨_, ⟨k, rfl⟩, hφ⟩ := exists_target_mem_limit hs he hq h Request.notIInf
    (fun θ => ∃ k, θ = (φs k).not)
    (fun σ i θ hi => by simp [Target, hi, BoundedFormulaInf.not])
    fun t ht hφs => (C.not_iInf t ht φs hφs).elim fun k hk => ⟨_, ⟨k, rfl⟩, hk⟩
  exact ⟨k, hφ⟩

/-- The limit contains some disjunct of each of its countable disjunctions. -/
theorem limit_iSup {φs : ℕ → L[[ℕ]].Sentenceω} (h : BoundedFormulaInf.iSup φs ∈ C.limit s e q) :
    ∃ k, φs k ∈ C.limit s e q := by
  obtain ⟨_, ⟨k, rfl⟩, hφ⟩ := exists_target_mem_limit hs he hq h Request.iSup
    (fun θ => ∃ k, θ = φs k)
    (fun σ i θ hi => by simp [Target, hi])
    fun t ht hφs => (C.iSup t ht φs hφs).elim fun k hk => ⟨_, ⟨k, rfl⟩, hk⟩
  exact ⟨k, hφ⟩

/-- The limit contains the negation of every disjunct of each of its negated countable
disjunctions. -/
theorem limit_not_iSup {φs : ℕ → L[[ℕ]].Sentenceω}
    (h : (BoundedFormulaInf.iSup φs).not ∈ C.limit s e q) (k : ℕ) :
    (φs k).not ∈ C.limit s e q := by
  obtain ⟨_, rfl, hφ⟩ := exists_target_mem_limit hs he hq h (Request.notISup · k) (· = (φs k).not)
    (fun σ i θ hi => by simp [Target, hi, BoundedFormulaInf.not])
    fun t ht hφs => ⟨_, rfl, C.not_iSup t ht φs hφs k⟩
  exact hφ

/-- The limit contains the instance at every Henkin constant of each of its universal
sentences. -/
theorem limit_all {φ : L[[ℕ]].BoundedFormulaω Empty 1} (h : φ.all ∈ C.limit s e q) (c : ℕ) :
    φ.inst (L.con c).term ∈ C.limit s e q := by
  obtain ⟨_, rfl, hφ⟩ := exists_target_mem_limit hs he hq h (Request.all · c)
    (· = φ.inst (L.con c).term)
    (fun σ i θ hi => by simp [Target, hi])
    fun t ht hφ => ⟨_, rfl, C.all t ht φ hφ c⟩
  exact hφ

/-- The limit contains a witness at some Henkin constant to each of its negated universal
sentences. -/
theorem limit_not_all {φ : L[[ℕ]].BoundedFormulaω Empty 1} (h : φ.all.not ∈ C.limit s e q) :
    ∃ c : ℕ, (φ.inst (L.con c).term).not ∈ C.limit s e q := by
  obtain ⟨_, ⟨c, rfl⟩, hφ⟩ := exists_target_mem_limit hs he hq h Request.notAll
    (fun θ => ∃ c : ℕ, θ = (φ.inst (L.con c).term).not)
    (fun σ i θ hi => by simp [Target, hi, BoundedFormulaInf.not])
    fun t ht hφ => (C.not_all t ht φ hφ).elim fun c hc => ⟨_, ⟨c, rfl⟩, hc⟩
  exact ⟨c, hφ⟩

omit he in
/-- The limit contains every reflexive equation between closed terms. -/
theorem limit_eq_refl (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    (equal t t : L[[ℕ]].Sentenceω) ∈ C.limit s e q := by
  obtain ⟨_, rfl, h⟩ := exists_target_mem_limit_of_forall hs hq (Request.eqRefl t) (· = equal t t)
    (fun σ θ => Iff.rfl) fun u hu => ⟨_, rfl, C.eq_refl u hu t⟩
  exact h

/-- The limit is closed under substitution of equals into atomic sentences. -/
theorem limit_eq_subst {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hφ : φ.IsAtomic) (ht : (equal t t' : L[[ℕ]].Sentenceω) ∈ C.limit s e q)
    (h : φ.inst t ∈ C.limit s e q) : φ.inst t' ∈ C.limit s e q := by
  obtain ⟨N₁, hN₁⟩ := mem_limit.1 ht
  obtain ⟨N₂, hN₂⟩ := mem_limit.1 h
  obtain ⟨i, hi⟩ := exists_resolve_eq he hN₁
  obtain ⟨j, hj⟩ := exists_resolve_eq he hN₂
  have hT : ∀ n, max N₁ N₂ ≤ n → ∀ θ,
      (Request.eqSubst i j ⟨φ, hφ⟩).Target (resolve e (added C s e q n)) θ ↔ θ = φ.inst t' := by
    intro n hn θ
    simp [Target, hi n (le_of_max_le_left hn), hj n (le_of_max_le_right hn)]
  obtain ⟨n, hn, θ, hθ, hθl⟩ := exists_target_mem_stage hq (Request.eqSubst i j ⟨φ, hφ⟩) (max N₁ N₂)
    fun n hn => ⟨_, (hT n hn _).2 rfl, C.eq_subst _ (stage_mem hs n) t t' φ hφ
      (monotone_stage (le_of_max_le_left hn) hN₁) (monotone_stage (le_of_max_le_right hn) hN₂)⟩
  exact (hT n hn θ).1 hθ ▸ hθl

omit he in
/-- The limit contains, for every closed term, an equation naming it by a Henkin constant. -/
theorem limit_eq_name (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    ∃ c : ℕ, (equal (L.con c).term t : L[[ℕ]].Sentenceω) ∈ C.limit s e q := by
  obtain ⟨_, ⟨c, rfl⟩, h⟩ := exists_target_mem_limit_of_forall hs hq (Request.eqName t)
    (fun θ => ∃ c : ℕ, θ = equal (L.con c).term t) (fun σ θ => Iff.rfl)
    fun u hu => (C.eq_name u hu t).elim fun c hc => ⟨_, ⟨c, rfl⟩, hc⟩
  exact ⟨c, h⟩

end ConsistencyProperty

end Language

end FirstOrder
