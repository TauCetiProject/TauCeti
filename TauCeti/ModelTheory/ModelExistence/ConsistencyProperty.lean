/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.ConstantInstances
public import TauCeti.ModelTheory.Infinitary.Satisfiability

/-!
# Consistency properties

A **consistency property** over a language `L` is a family of sets of `L_{ω₁ω}` sentences of the
Henkin expansion `L[[ℕ]]` that contains no outright contradiction and is closed under the
decomposition of every connective and quantifier: whenever a member contains a compound sentence,
the family also contains the member enlarged by a suitable component of that sentence (one chosen
component for a disjunctive sentence, every component for a conjunctive one). The quantifier
clauses instantiate only the Henkin constants `L.con c`, and the equality clauses make every
closed term equal to some Henkin constant, so that a model built from a member can be one in
which every element is the interpretation of a Henkin constant.

The syntax has only implication and falsum as propositional primitives, with `¬φ` the formula
`φ.imp ⊥`. A negated compound sentence is therefore decomposed by its own clause, and double
negation is the negated-implication clause at `ψ = ⊥` (`ConsistencyProperty.not_not`).

Two clauses common in finitary presentations are absent. Closure under unions of increasing
chains is absent because `L_{ω₁ω}` is not compact, so the satisfiable sets of sentences are not
closed under unions of chains. A decision clause, adding `φ` or `¬φ` to every member, is absent
because model existence can be proved by a fair enumeration of decomposition requests that never
needs it. Substitution of equals is required only into atomic formulas.

The basic example is semantic: in an `L[[ℕ]]`-structure in which every element is the
interpretation of a Henkin constant, the sets of sentences true in the structure form a
consistency property (`ConsistencyProperty.ofModel`). The model existence theorem is the
converse: a countable member of a consistency property over a countable language has a countable
model of exactly this kind.

A second instance, the one behind the omitting types theorem, is built from satisfiability rather
than from one model. For a formation-closed fragment `A` and a theory `T` of sentences of `A`, the
satisfiable theories made of `T` and finitely many instances of members of `A` at tuples of Henkin
constants form a consistency property (`ConsistencyProperty.ofSatisfiable`). Only finitely many
Henkin constants occur in such a theory, so the witness clauses are met by reinterpreting a
fresh constant in a model; formation closure supplies the negations and the atomic sentences that
the clauses add.

## Main definitions

* `FirstOrder.Language.ConsistencyProperty`: consistency properties over `L[[ℕ]]`.
* `FirstOrder.Language.ConsistencyProperty.ofModel`: the sets of sentences true in a structure
  whose elements are all named by Henkin constants.
* `FirstOrder.Language.ConsistencyProperty.ofSatisfiable`: the satisfiable theories made of a
  theory of sentences of a formation-closed fragment and finitely many instances of its members.

## Main results

* `FirstOrder.Language.ConsistencyProperty.not_not`: double negation elimination.
* `FirstOrder.Language.ConsistencyProperty.mem_ofModel_iff`: the members of `ofModel` are the
  theories modelled by the structure.
* `FirstOrder.Language.ConsistencyProperty.onTheoryω_mem_ofSatisfiable`: a satisfiable theory of
  sentences of the fragment is a member of `ofSatisfiable`.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.1.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
* `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/Henkin/ConsistencyProperty.lean` and
  `InfinitaryLogic/Methods/Henkin/SatisfiableConsistencyProperty.lean`, which formalize
  consistency properties and the true-in-a-model instance. Divergences from that source: the
  clauses are stated over the Henkin expansion `L[[ℕ]]`, with the quantifier clauses
  instantiating Henkin constants through bound substitution and an explicit naming clause for
  closed terms; the chain-closure and decision clauses are dropped; and the true-in-a-model
  instance names elements by Henkin constants rather than by a naming function into closed terms.
-/

public section

universe u v w

namespace FirstOrder

namespace Language

open BoundedFormulaInf

/-- A **consistency property** over `L`: a family of sets of `L_{ω₁ω}` sentences of the Henkin
expansion `L[[ℕ]]` containing neither `⊥` nor a sentence together with its negation, and closed
under the decomposition of each connective and quantifier, with the Henkin constants as witnesses
and as names for closed terms. -/
@[ext]
structure ConsistencyProperty (L : Language.{u, v}) where
  /-- The family of consistent sets of sentences. -/
  sets : Set L[[ℕ]].Theoryω
  /-- No consistent set contains `⊥`. -/
  no_falsum : ∀ s ∈ sets, (⊥ : L[[ℕ]].Sentenceω) ∉ s
  /-- No consistent set contains a sentence together with its negation. -/
  no_contradiction : ∀ s ∈ sets, ∀ φ : L[[ℕ]].Sentenceω, φ ∈ s → φ.not ∉ s
  /-- An implication can be decomposed into the negation of its hypothesis or its conclusion. -/
  imp : ∀ s ∈ sets, ∀ φ ψ : L[[ℕ]].Sentenceω, φ.imp ψ ∈ s →
    insert φ.not s ∈ sets ∨ insert ψ s ∈ sets
  /-- A negated implication can be decomposed into its hypothesis and the negation of its
  conclusion. -/
  not_imp : ∀ s ∈ sets, ∀ φ ψ : L[[ℕ]].Sentenceω, (φ.imp ψ).not ∈ s →
    insert φ s ∈ sets ∧ insert ψ.not s ∈ sets
  /-- A countable conjunction can be decomposed into each of its conjuncts. -/
  iInf : ∀ s ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaInf.iInf φs ∈ s →
    ∀ k, insert (φs k) s ∈ sets
  /-- A negated countable conjunction can be decomposed into the negation of some conjunct. -/
  not_iInf : ∀ s ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω, (BoundedFormulaInf.iInf φs).not ∈ s →
    ∃ k, insert (φs k).not s ∈ sets
  /-- A countable disjunction can be decomposed into some disjunct. -/
  iSup : ∀ s ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaInf.iSup φs ∈ s →
    ∃ k, insert (φs k) s ∈ sets
  /-- A negated countable disjunction can be decomposed into the negation of each disjunct. -/
  not_iSup : ∀ s ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω, (BoundedFormulaInf.iSup φs).not ∈ s →
    ∀ k, insert (φs k).not s ∈ sets
  /-- A universal sentence can be instantiated at every Henkin constant. -/
  all : ∀ s ∈ sets, ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1, φ.all ∈ s →
    ∀ c : ℕ, insert (φ.inst (L.con c).term) s ∈ sets
  /-- A negated universal sentence has a counterexample at some Henkin constant. -/
  not_all : ∀ s ∈ sets, ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1, φ.all.not ∈ s →
    ∃ c : ℕ, insert (φ.inst (L.con c).term).not s ∈ sets
  /-- Every closed term equals itself. -/
  eq_refl : ∀ s ∈ sets, ∀ t : L[[ℕ]].Term (Empty ⊕ Fin 0),
    insert (equal t t : L[[ℕ]].Sentenceω) s ∈ sets
  /-- Equals can be substituted for equals in an atomic formula. -/
  eq_subst : ∀ s ∈ sets, ∀ (t t' : L[[ℕ]].Term (Empty ⊕ Fin 0))
    (φ : L[[ℕ]].BoundedFormulaω Empty 1), φ.IsAtomic → (equal t t' : L[[ℕ]].Sentenceω) ∈ s →
      φ.inst t ∈ s → insert (φ.inst t') s ∈ sets
  /-- Every closed term equals some Henkin constant. -/
  eq_name : ∀ s ∈ sets, ∀ t : L[[ℕ]].Term (Empty ⊕ Fin 0),
    ∃ c : ℕ, insert (equal (L.con c).term t : L[[ℕ]].Sentenceω) s ∈ sets

namespace ConsistencyProperty

variable {L : Language.{u, v}}

/-- **Double negation elimination**: a doubly negated sentence can be replaced by the sentence. -/
theorem not_not (C : ConsistencyProperty L) {s : L[[ℕ]].Theoryω} (hs : s ∈ C.sets)
    {φ : L[[ℕ]].Sentenceω} (h : φ.not.not ∈ s) : insert φ s ∈ C.sets :=
  -- `φ.not.not` is `(φ.imp ⊥).not` by the definitions of `not` and `⊥`.
  (C.not_imp s hs φ ⊥ (by rwa [bot_def])).1

section ofModel

variable (M : Type w) [L[[ℕ]].Structure M]

/-- The **satisfaction instance**: in an `L[[ℕ]]`-structure in which every element is the
interpretation of a Henkin constant, the sets of sentences true in the structure form a
consistency property. For an `L`-structure `M` and a surjection `e : ℕ → M`, the expansion
`constantsOn.structure e` interpreting `L.con c` as `e c` is such a structure. -/
def ofModel (hM : Function.Surjective fun c : ℕ => (L.con c : M)) : ConsistencyProperty L where
  sets := {s | s.Model M}
  no_falsum s hs h := SentenceInf.realize_bot.1 (Theoryω.Model.realize_of_mem hs h)
  no_contradiction s hs φ h h' :=
    SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hs h')
      (Theoryω.Model.realize_of_mem hs h)
  imp s hs φ ψ h := by
    have h := Theoryω.Model.realize_of_mem hs h
    simp only [Set.mem_ofPred_eq, Theoryω.model_insert_iff, SentenceInf.realize_def,
      FormulaInf.realize_def, realize_not, realize_imp] at h ⊢
    by_cases hφ : φ.Realize (Empty.elim : Empty → M) default
    · exact .inr ⟨h hφ, hs⟩
    · exact .inl ⟨hφ, hs⟩
  not_imp s hs φ ψ h := by
    have h := Theoryω.Model.realize_of_mem hs h
    simp only [Set.mem_ofPred_eq, Theoryω.model_insert_iff, SentenceInf.realize_def,
      FormulaInf.realize_def, realize_not, realize_imp, Classical.not_imp] at h ⊢
    exact ⟨⟨h.1, hs⟩, ⟨h.2, hs⟩⟩
  iInf s hs φs h k := Theoryω.model_insert_iff.2
    ⟨SentenceInf.realize_iInf.1 (Theoryω.Model.realize_of_mem hs h) k, hs⟩
  not_iInf s hs φs h := by
    have h := SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hs h)
    obtain ⟨k, hk⟩ := not_forall.1 (h ∘ SentenceInf.realize_iInf.2)
    exact ⟨k, Theoryω.model_insert_iff.2 ⟨SentenceInf.realize_not.2 hk, hs⟩⟩
  iSup s hs φs h := by
    obtain ⟨k, hk⟩ := SentenceInf.realize_iSup.1 (Theoryω.Model.realize_of_mem hs h)
    exact ⟨k, Theoryω.model_insert_iff.2 ⟨hk, hs⟩⟩
  not_iSup s hs φs h k := by
    have h := SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hs h)
    exact Theoryω.model_insert_iff.2
      ⟨SentenceInf.realize_not.2 fun hk => h (SentenceInf.realize_iSup.2 ⟨k, hk⟩), hs⟩
  all s hs φ h c := by
    have h := Theoryω.Model.realize_of_mem hs h
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all] at h
    refine Theoryω.model_insert_iff.2 ⟨?_, hs⟩
    simp only [SentenceInf.realize_def, realize_inst, Term.realize_constants]
    simpa only [Fin.snoc_zero] using h (L.con c)
  not_all s hs φ h := by
    have h := SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hs h)
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all] at h
    obtain ⟨m, hm⟩ := not_forall.1 h
    obtain ⟨c, rfl⟩ := hM m
    refine ⟨c, Theoryω.model_insert_iff.2 ⟨SentenceInf.realize_not.2 ?_, hs⟩⟩
    simp only [SentenceInf.realize_def, realize_inst, Term.realize_constants]
    simpa only [Fin.snoc_zero] using hm
  eq_refl s hs t := Theoryω.model_insert_iff.2
    ⟨by simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal], hs⟩
  eq_subst s hs t t' φ _ ht hφ := by
    have ht := Theoryω.Model.realize_of_mem hs ht
    have hφ := Theoryω.Model.realize_of_mem hs hφ
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal] at ht
    simp only [SentenceInf.realize_def, realize_inst] at hφ
    refine Theoryω.model_insert_iff.2 ⟨?_, hs⟩
    simp only [SentenceInf.realize_def, realize_inst]
    rwa [← ht]
  eq_name s hs t := by
    obtain ⟨c, hc⟩ := hM (t.realize (Sum.elim Empty.elim default))
    refine ⟨c, Theoryω.model_insert_iff.2 ⟨?_, hs⟩⟩
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal,
      Term.realize_constants]
    exact hc

variable {M}

/-- The members of `ofModel M hM` are the theories of which `M` is a model. -/
@[simp]
theorem mem_ofModel_iff {hM : Function.Surjective fun c : ℕ => (L.con c : M)}
    {s : L[[ℕ]].Theoryω} : s ∈ (ofModel M hM).sets ↔ s.Model M :=
  Iff.rfl

end ofModel

section ofSatisfiable

open Fragment

variable {A : Fragment L} {T : L.Theoryω}

/-- The sentences of a theory together with finitely many instances can be written as instances
at tuples of constants drawn from one finite set. -/
private theorem exists_finite_constants {σ : L[[ℕ]].Theoryω} (hσ : σ.Finite)
    (hσA : σ ⊆ A.instances ℕ) :
    ∃ F : Set ℕ, F.Finite ∧ ∀ φ ∈ (L.lhomWithConstants ℕ).onTheoryω T ∪ σ,
      ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (d : Fin n → ℕ),
        χ.instConstants d = φ ∧ ∀ i, d i ∈ F := by
  choose n χ d _ hd using fun φ (hφ : φ ∈ σ) => mem_instances.1 (hσA hφ)
  refine ⟨⋃ (φ) (h : φ ∈ σ), Set.range (d φ h), hσ.biUnion' fun _ _ => Set.finite_range _, ?_⟩
  rintro φ (hφ | hφ)
  · obtain ⟨ψ, -, rfl⟩ := LHom.mem_onTheoryω.1 hφ
    exact ⟨0, ψ, Fin.elim0, instConstants_zero ψ _, fun i => i.elim0⟩
  · exact ⟨n φ hφ, χ φ hφ, d φ hφ, hd φ hφ, fun i => Set.mem_iUnion₂.2 ⟨φ, hφ, i, rfl⟩⟩

/-- The expansion of an `L`-structure interpreting each Henkin constant `c` as `e c` models a
theory whose sentences are instances of formulas holding at the values of their constants. -/
private theorem model_of_forall_realize {M : Type*} [L.Structure M] (e : ℕ → M)
    {s : L[[ℕ]].Theoryω} (h : ∀ φ ∈ s, ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n)
      (d : Fin n → ℕ), χ.instConstants d = φ ∧ χ.Realize Empty.elim (e ∘ d)) :
    letI := constantsOn.structure e; s.Model M := by
  let := constantsOn.structure e
  refine Theoryω.model_iff.2 fun φ hφ => ?_
  obtain ⟨n, χ, d, rfl, h⟩ := h φ hφ
  rwa [SentenceInf.realize_def, realize_instConstants]

/-- In a model of `s` that is the expansion of an `L`-structure interpreting each Henkin
constant `c` as `e c`, an instance in `s` holds at the values of its constants. -/
private theorem realize_of_model {M : Type*} [L.Structure M] {e : ℕ → M}
    {s : L[[ℕ]].Theoryω} (hM : letI := constantsOn.structure e; s.Model M) {n : ℕ}
    {χ : L.BoundedFormulaω Empty n} {d : Fin n → ℕ} (h : χ.instConstants d ∈ s) :
    χ.Realize Empty.elim (e ∘ d) := by
  let := constantsOn.structure e
  have hr := Theoryω.Model.realize_of_mem hM h
  rwa [SentenceInf.realize_def, realize_instConstants] at hr

/-- Changing the interpretation of Henkin constants outside a set `F` preserves a model of a
theory whose sentences are instances at tuples of constants from `F`. -/
private theorem model_of_eqOn {M : Type*} [L.Structure M] {e e' : ℕ → M} {F : Set ℕ}
    {s : L[[ℕ]].Theoryω} (hF : ∀ φ ∈ s, ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n)
      (d : Fin n → ℕ), χ.instConstants d = φ ∧ ∀ i, d i ∈ F)
    (he : Set.EqOn e e' F) (hM : letI := constantsOn.structure e; s.Model M) :
    letI := constantsOn.structure e'; s.Model M := by
  refine model_of_forall_realize e' fun φ hφ => ?_
  obtain ⟨n, χ, d, rfl, hd⟩ := hF φ hφ
  have hed : e' ∘ d = e ∘ d := funext fun i => (he (hd i)).symm
  exact ⟨n, χ, d, rfl, hed ▸ realize_of_model hM hφ⟩

/-- A theory that the expansion of a nonempty `L`-structure by an interpretation of the Henkin
constants models is satisfiable. -/
private theorem isSatisfiable_of_model {M : Type (max u v)} [L.Structure M] [Nonempty M]
    (e : ℕ → M) {s : L[[ℕ]].Theoryω} (hM : letI := constantsOn.structure e; s.Model M) :
    s.IsSatisfiable := by
  let := constantsOn.structure e
  exact Theoryω.isSatisfiable_iff.2 ⟨M, inferInstance, inferInstance, hM⟩

/-- A satisfiable theory made of the sentences of `T` and finitely many instances has a nonempty
model that is the expansion of an `L`-structure by an interpretation `e` of the Henkin
constants, and its sentences are instances at tuples of constants from a finite set. -/
private theorem exists_model_of_mem {s : L[[ℕ]].Theoryω}
    (hs : (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
      s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ s.IsSatisfiable) :
    ∃ (M : Type (max u v)) (_ : L.Structure M) (_ : Nonempty M) (e : ℕ → M) (F : Set ℕ),
      F.Finite ∧ (∀ φ ∈ s, ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (d : Fin n → ℕ),
        χ.instConstants d = φ ∧ ∀ i, d i ∈ F) ∧
      (letI := constantsOn.structure e; s.Model M) := by
  obtain ⟨⟨σ, hσ, hσA, rfl⟩, hsat⟩ := hs
  obtain ⟨M, _, hne, hM⟩ := Theoryω.isSatisfiable_iff.1 hsat
  obtain ⟨F, hFf, hF⟩ := exists_finite_constants (T := T) hσ hσA
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  refine ⟨M, inferInstance, hne, fun c => (L.con c : M), F, hFf, hF,
    model_of_forall_realize _ fun φ hφ => ?_⟩
  obtain ⟨n, χ, d, rfl, -⟩ := hF φ hφ
  have h := Theoryω.Model.realize_of_mem hM hφ
  rw [SentenceInf.realize_def, realize_instConstants] at h
  exact ⟨n, χ, d, rfl, h⟩

/-- Adding a satisfiable instance to a theory made of the sentences of `T` and finitely many
instances gives a theory of the same kind. -/
private theorem insert_mem {s : L[[ℕ]].Theoryω} {X : L[[ℕ]].Sentenceω}
    (hs : (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
      s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ s.IsSatisfiable)
    (hX : X ∈ A.instances ℕ) (hsat : (insert X s).IsSatisfiable) :
    (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
      insert X s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ (insert X s).IsSatisfiable := by
  obtain ⟨⟨σ, hσ, hσA, rfl⟩, -⟩ := hs
  exact ⟨⟨insert X σ, hσ.insert X, Set.insert_subset hX hσA, (Set.union_insert ..).symm⟩, hsat⟩

/-- Adding an instance true in a nonempty model of such a theory gives a theory of the same
kind. -/
private theorem insert_mem_of_model {s : L[[ℕ]].Theoryω} {X : L[[ℕ]].Sentenceω}
    (hs : (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
      s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ s.IsSatisfiable)
    (hX : X ∈ A.instances ℕ) {M : Type (max u v)} [L[[ℕ]].Structure M] [Nonempty M]
    (hM : s.Model M) (hXM : SentenceInf.Realize X M) :
    (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
      insert X s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ (insert X s).IsSatisfiable :=
  insert_mem hs hX (Theoryω.isSatisfiable_iff.2
    ⟨M, inferInstance, inferInstance, Theoryω.model_insert_iff.2 ⟨hXM, hM⟩⟩)

/-- The sentences of a theory of members of `A` together with finitely many instances are
instances. -/
private theorem subset_instances (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    {s : L[[ℕ]].Theoryω} (hs : ∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
      s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) :
    s ⊆ A.instances ℕ := by
  obtain ⟨σ, -, hσA, rfl⟩ := hs
  rintro φ (hφ | hφ)
  · obtain ⟨ψ, hψ, rfl⟩ := LHom.mem_onTheoryω.1 hφ
    exact onBoundedFormulaInf_mem_instances (hT ψ hψ)
  · exact hσA hφ

/-- **The consistency property of satisfiable instances.** For a formation-closed fragment `A`
and a theory `T` of sentences of `A`, the satisfiable theories of `L[[ℕ]]` made of the image of `T`
and a finite set of instances of members of `A` at tuples of Henkin constants form a consistency
property. -/
def ofSatisfiable (T : L.Theoryω) (A : Fragment L) (hA : A.FormationClosed)
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) : ConsistencyProperty L where
  sets := {s | (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
    s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ s.IsSatisfiable}
  no_falsum s hs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact SentenceInf.realize_bot.1 (Theoryω.Model.realize_of_mem hM h)
  no_contradiction s hs φ h h' := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hM h')
      (Theoryω.Model.realize_of_mem hM h)
  imp s hs φ ψ h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := subset_instances hT hs.1 h
    have hr : SentenceInf.Realize φ M → SentenceInf.Realize ψ M := by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_imp] using
        Theoryω.Model.realize_of_mem hM h
    by_cases hφ : SentenceInf.Realize φ M
    · exact .inr (insert_mem_of_model hs (imp_right_mem_instances hi) hM (hr hφ))
    · exact .inl (insert_mem_of_model hs (hA.not_mem_instances_iff.2 (imp_left_mem_instances hi))
        hM (SentenceInf.realize_not.2 hφ))
  not_imp s hs φ ψ h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := imp_left_mem_instances (subset_instances hT hs.1 h)
    have hr : SentenceInf.Realize φ M ∧ ¬SentenceInf.Realize ψ M := by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_not, realize_imp,
        Classical.not_imp] using Theoryω.Model.realize_of_mem hM h
    exact ⟨insert_mem_of_model hs (imp_left_mem_instances hi) hM hr.1,
      insert_mem_of_model hs (hA.not_mem_instances_iff.2 (imp_right_mem_instances hi)) hM
        (SentenceInf.realize_not.2 hr.2)⟩
  iInf s hs φs h k := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact insert_mem_of_model hs (iInf_mem_instances (subset_instances hT hs.1 h) k) hM
      (SentenceInf.realize_iInf.1 (Theoryω.Model.realize_of_mem hM h) k)
  not_iInf s hs φs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := hA.not_mem_instances_iff.1 (subset_instances hT hs.1 h)
    have hr := SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hM h)
    obtain ⟨k, hk⟩ := not_forall.1 (hr ∘ SentenceInf.realize_iInf.2)
    exact ⟨k, insert_mem_of_model hs (hA.not_mem_instances_iff.2 (iInf_mem_instances hi k)) hM
      (SentenceInf.realize_not.2 hk)⟩
  iSup s hs φs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    obtain ⟨k, hk⟩ := SentenceInf.realize_iSup.1 (Theoryω.Model.realize_of_mem hM h)
    exact ⟨k, insert_mem_of_model hs (iSup_mem_instances (subset_instances hT hs.1 h) k) hM hk⟩
  not_iSup s hs φs h k := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := hA.not_mem_instances_iff.1 (subset_instances hT hs.1 h)
    have hr := SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hM h)
    exact insert_mem_of_model hs (hA.not_mem_instances_iff.2 (iSup_mem_instances hi k)) hM
      (SentenceInf.realize_not.2 fun hk => hr (SentenceInf.realize_iSup.2 ⟨k, hk⟩))
  all s hs φ h c := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hr := Theoryω.Model.realize_of_mem hM h
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all] at hr
    refine insert_mem_of_model hs (inst_mem_instances (subset_instances hT hs.1 h) c) hM ?_
    simp only [SentenceInf.realize_def, realize_inst, Term.realize_constants]
    simpa only [Fin.snoc_zero] using hr (L.con c)
  not_all s hs φ h := by
    -- Write `¬∀φ` as the instance of `¬∀χ` at `d`, take a counterexample `m` to `χ` at `d`, and
    -- reinterpret a Henkin constant `c` not occurring in `s` as `m`.
    obtain ⟨M, _, _, e, F, hFf, hF, hM⟩ := exists_model_of_mem hs
    obtain ⟨c, hc⟩ := hFf.exists_notMem
    obtain ⟨n, χ, d, hχ, hd⟩ := hF _ h
    obtain ⟨χ₁, χ₂, rfl, hχ₁, hχ₂⟩ := instConstants_eq_imp_iff.1 hχ
    obtain rfl := instConstants_eq_falsum_iff.1 hχ₂
    obtain ⟨χ, rfl, hinst⟩ := exists_eq_all_of_instConstants_eq_all hχ₁
    obtain ⟨m, hm⟩ : ∃ m, ¬χ.Realize Empty.elim (Fin.snoc (e ∘ d) m) := by
      have hr := realize_of_model hM (hχ ▸ h)
      simp only [realize_imp, realize_all, realize_falsum, imp_false, not_forall] at hr
      exact hr
    obtain ⟨e', he'c, he⟩ : ∃ e' : ℕ → M, e' c = m ∧ Set.EqOn e e' F :=
      ⟨Function.update e c m, Function.update_self .., fun k hk =>
        (Function.update_of_ne (ne_of_mem_of_not_mem hk hc) _ _).symm⟩
    refine ⟨c, insert_mem hs (hA.not_mem_instances_iff.2
      (inst_mem_instances (imp_left_mem_instances (subset_instances hT hs.1 h)) c))
      (isSatisfiable_of_model e' (model_of_forall_realize e' ?_))⟩
    rintro ψ (rfl | hψ)
    · refine ⟨n + 1, χ.not, Fin.snoc d c, by rw [instConstants_not, hinst], ?_⟩
      have hed : e' ∘ d = e ∘ d := funext fun i => (he (hd i)).symm
      rwa [realize_not, Fin.comp_snoc, he'c, hed]
    · obtain ⟨k, ψ, d', rfl, hd'⟩ := hF _ hψ
      have hed : e' ∘ d' = e ∘ d' := funext fun i => (he (hd' i)).symm
      exact ⟨k, ψ, d', rfl, hed ▸ realize_of_model hM hψ⟩
  eq_refl s hs t := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact insert_mem_of_model hs (hA.mem_instances_of_isAtomic (.equal _ _)) hM
      (by simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal])
  eq_subst s hs t t' φ hφ ht htφ := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have ht := Theoryω.Model.realize_of_mem hM ht
    have htφ := Theoryω.Model.realize_of_mem hM htφ
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal] at ht
    simp only [SentenceInf.realize_def, realize_inst] at htφ
    have hi : (φ.inst t').IsAtomic := by rw [inst_def]; exact hφ.substBounds _
    refine insert_mem_of_model hs (hA.mem_instances_of_isAtomic hi) hM ?_
    simp only [SentenceInf.realize_def, realize_inst]
    rwa [← ht]
  eq_name s hs t := by
    -- Write `t` with its constants `d` abstracted, and reinterpret a Henkin constant `c`
    -- occurring neither in `s` nor in `t` as the value of `t`.
    obtain ⟨M, _, _, e, F, hFf, hF, hM⟩ := exists_model_of_mem hs
    obtain ⟨n, r, d, rfl⟩ := t.exists_onTerm_subst_eq
    obtain ⟨c, hc⟩ := (hFf.union (Set.finite_range d)).exists_notMem
    obtain ⟨e', he'c, he⟩ : ∃ e' : ℕ → M,
        e' c = r.realize (Sum.elim Empty.elim (e ∘ d)) ∧ Set.EqOn e e' (F ∪ Set.range d) :=
      ⟨Function.update e c _, Function.update_self .., fun k hk =>
        (Function.update_of_ne (ne_of_mem_of_not_mem hk hc) _ _).symm⟩
    refine ⟨c, insert_mem hs (hA.mem_instances_of_isAtomic (.equal _ _))
      (isSatisfiable_of_model e' ?_)⟩
    have hs' := model_of_eqOn hF (he.mono Set.subset_union_left) hM
    let := constantsOn.structure e'
    have hcon : ∀ k, (L.con k : M) = e' k := fun _ => rfl
    refine Theoryω.model_insert_iff.2 ⟨?_, hs'⟩
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal, Term.realize_constants,
      Term.realize_onTerm_subst_con, hcon, he'c]
    simp only [hcon]
    congr 2
    funext i
    exact he (Or.inr ⟨i, rfl⟩)

/-- The members of `ofSatisfiable T A hA hT` are the satisfiable theories made of the sentences of
`T`, mapped to `L[[ℕ]]`, and finitely many instances of members of `A`. -/
@[simp]
theorem mem_ofSatisfiable_iff {hA : A.FormationClosed} {hT} {s : L[[ℕ]].Theoryω} :
    s ∈ (ofSatisfiable T A hA hT).sets ↔ (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧
      σ ⊆ A.instances ℕ ∧ s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ s.IsSatisfiable :=
  Iff.rfl

/-- A satisfiable theory of sentences of `A`, mapped to `L[[ℕ]]`, is a member of
`ofSatisfiable`. -/
theorem onTheoryω_mem_ofSatisfiable {hA : A.FormationClosed} {hT} (h : T.IsSatisfiable) :
    (L.lhomWithConstants ℕ).onTheoryω T ∈ (ofSatisfiable T A hA hT).sets := by
  refine ⟨⟨∅, Set.finite_empty, Set.empty_subset _, (Set.union_empty _).symm⟩, ?_⟩
  obtain ⟨M, _, hne, hM⟩ := Theoryω.isSatisfiable_iff.1 h
  refine isSatisfiable_of_model (fun _ => Classical.arbitrary M) ?_
  let := constantsOn.structure fun _ : ℕ => Classical.arbitrary M
  exact (LHom.onTheoryω_model _ T).2 hM

end ofSatisfiable

end ConsistencyProperty

end Language

end FirstOrder
