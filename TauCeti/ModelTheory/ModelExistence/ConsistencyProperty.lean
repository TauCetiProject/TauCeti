/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.SubstBounds
public import TauCeti.ModelTheory.Infinitary.Theory

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

## Main definitions

* `FirstOrder.Language.ConsistencyProperty`: consistency properties over `L[[ℕ]]`.
* `FirstOrder.Language.ConsistencyProperty.ofModel`: the sets of sentences true in a structure
  whose elements are all named by Henkin constants.

## Main results

* `FirstOrder.Language.ConsistencyProperty.not_not`: double negation elimination.
* `FirstOrder.Language.ConsistencyProperty.mem_ofModel_iff`: the members of `ofModel` are the
  theories modelled by the structure.

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

end ConsistencyProperty

end Language

end FirstOrder
