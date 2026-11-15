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
* `FirstOrder.Language.ConsistencyProperty.exists_model_of_mem_ofSatisfiable` and
  `FirstOrder.Language.ConsistencyProperty.insert_mem_ofSatisfiable`: a member of `ofSatisfiable`
  has a model expanding an `L`-structure by an interpretation of the Henkin constants, and adding
  an instance keeps a satisfiable theory a member.

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
  no_falsum _ hs := hs.bot_notMem
  no_contradiction _ hs _ h := hs.not_notMem h
  imp s hs φ ψ h := (hs.realize_of_imp_mem h).imp
    (fun hφ => Theoryω.model_insert_iff.2 ⟨hφ, hs⟩) fun hψ => Theoryω.model_insert_iff.2 ⟨hψ, hs⟩
  not_imp s hs φ ψ h := ⟨Theoryω.model_insert_iff.2 ⟨(hs.realize_of_not_imp_mem h).1, hs⟩,
    Theoryω.model_insert_iff.2 ⟨(hs.realize_of_not_imp_mem h).2, hs⟩⟩
  iInf s hs φs h k := Theoryω.model_insert_iff.2
    ⟨SentenceInf.realize_iInf.1 (Theoryω.Model.realize_of_mem hs h) k, hs⟩
  not_iInf s hs φs h := by
    obtain ⟨k, hk⟩ := hs.realize_of_not_iInf_mem h
    exact ⟨k, Theoryω.model_insert_iff.2 ⟨hk, hs⟩⟩
  iSup s hs φs h := by
    obtain ⟨k, hk⟩ := SentenceInf.realize_iSup.1 (Theoryω.Model.realize_of_mem hs h)
    exact ⟨k, Theoryω.model_insert_iff.2 ⟨hk, hs⟩⟩
  not_iSup s hs φs h k := Theoryω.model_insert_iff.2 ⟨hs.realize_of_not_iSup_mem h k, hs⟩
  all s hs φ h c := Theoryω.model_insert_iff.2
    ⟨SentenceInf.realize_inst_of_realize_all (hs.realize_of_mem h) _, hs⟩
  not_all s hs φ h := by
    have h := SentenceInf.realize_not.1 (Theoryω.Model.realize_of_mem hs h)
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all] at h
    obtain ⟨m, hm⟩ := not_forall.1 h
    obtain ⟨c, rfl⟩ := hM m
    refine ⟨c, Theoryω.model_insert_iff.2 ⟨SentenceInf.realize_not.2 ?_, hs⟩⟩
    simp only [SentenceInf.realize_def, realize_inst, Term.realize_constants]
    simpa only [Fin.snoc_zero] using hm
  eq_refl s hs t := Theoryω.model_insert_iff.2 ⟨SentenceInf.realize_equal_self t, hs⟩
  eq_subst s hs t t' φ _ ht hφ :=
    Theoryω.model_insert_iff.2
      ⟨SentenceInf.realize_inst_of_realize_equal (hs.realize_of_mem ht) (hs.realize_of_mem hφ), hs⟩
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

/-- The satisfiable theories made of the sentences of `T`, mapped to `L[[ℕ]]`, and finitely many
instances of members of `A`: the members of `ofSatisfiable`. -/
private def satisfiableSets (T : L.Theoryω) (A : Fragment L) : Set L[[ℕ]].Theoryω :=
  {s | (∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
    s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ) ∧ s.IsSatisfiable}

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

/-- A satisfiable theory made of the sentences of `T` and finitely many instances has a nonempty
model that is the expansion of an `L`-structure by an interpretation `e` of the Henkin
constants, and its sentences are instances at tuples of constants from a finite set. -/
private theorem exists_model_of_mem {s : L[[ℕ]].Theoryω} (hs : s ∈ satisfiableSets T A) :
    ∃ (M : Type (max u v)) (_ : L.Structure M) (_ : Nonempty M) (e : ℕ → M) (F : Set ℕ),
      F.Finite ∧ (∀ φ ∈ s, ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (d : Fin n → ℕ),
        χ.instConstants d = φ ∧ ∀ i, d i ∈ F) ∧
      (letI := constantsOn.structure e; s.Model M) := by
  obtain ⟨⟨σ, hσ, hσA, rfl⟩, hsat⟩ := hs
  obtain ⟨M, _, hne, hM⟩ := Theoryω.isSatisfiable_iff.1 hsat
  obtain ⟨F, hFf, hF⟩ := exists_finite_constants (T := T) hσ hσA
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  refine ⟨M, inferInstance, hne, fun c => (L.con c : M), F, hFf, hF,
    Theoryω.model_of_forall_realize_instConstants _ fun φ hφ => ?_⟩
  obtain ⟨n, χ, d, rfl, -⟩ := hF φ hφ
  have h := Theoryω.Model.realize_of_mem hM hφ
  rw [SentenceInf.realize_def, realize_instConstants] at h
  exact ⟨n, χ, d, rfl, h⟩

/-- **Reinterpreting a fresh constant**: in a model of a theory of instances at constants from
`F`, a Henkin constant `c` outside a set `G ⊇ F` can be reinterpreted as any element `m`, keeping
the interpretation on `G` and the model of the theory. -/
private theorem exists_update_model {M : Type*} [L.Structure M] {e : ℕ → M} {F G : Set ℕ}
    {s : L[[ℕ]].Theoryω} (hF : ∀ φ ∈ s, ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n)
      (d : Fin n → ℕ), χ.instConstants d = φ ∧ ∀ i, d i ∈ F) (hFG : F ⊆ G)
    (hM : letI := constantsOn.structure e; s.Model M) {c : ℕ} (hc : c ∉ G) (m : M) :
    ∃ e' : ℕ → M, e' c = m ∧ Set.EqOn e e' G ∧ (letI := constantsOn.structure e'; s.Model M) := by
  have he : Set.EqOn e (Function.update e c m) G := fun k hk =>
    (Function.update_of_ne (ne_of_mem_of_not_mem hk hc) _ _).symm
  exact ⟨_, Function.update_self .., he, hM.of_eqOn_constantsOn hF (he.mono hFG)⟩

/-- Adding a satisfiable instance to a theory made of the sentences of `T` and finitely many
instances gives a theory of the same kind. -/
private theorem insert_mem {s : L[[ℕ]].Theoryω} {X : L[[ℕ]].Sentenceω}
    (hs : s ∈ satisfiableSets T A) (hX : X ∈ A.instances ℕ) (hsat : (insert X s).IsSatisfiable) :
    insert X s ∈ satisfiableSets T A := by
  obtain ⟨⟨σ, hσ, hσA, rfl⟩, -⟩ := hs
  exact ⟨⟨insert X σ, hσ.insert X, Set.insert_subset hX hσA, (Set.union_insert ..).symm⟩, hsat⟩

/-- Adding an instance true in a nonempty model of such a theory gives a theory of the same
kind. -/
private theorem insert_mem_of_model {s : L[[ℕ]].Theoryω} {X : L[[ℕ]].Sentenceω}
    (hs : s ∈ satisfiableSets T A) (hX : X ∈ A.instances ℕ) {M : Type (max u v)}
    [L[[ℕ]].Structure M] [Nonempty M] (hM : s.Model M) (hXM : SentenceInf.Realize X M) :
    insert X s ∈ satisfiableSets T A :=
  insert_mem hs hX (Theoryω.model_insert_iff.2 ⟨hXM, hM⟩).isSatisfiable

/-- The sentences of a theory of members of `A` together with finitely many instances are
instances. -/
private theorem subset_instances (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    {s : L[[ℕ]].Theoryω} (hs : s ∈ satisfiableSets T A) :
    s ⊆ A.instances ℕ := by
  obtain ⟨⟨σ, -, hσA, rfl⟩, -⟩ := hs
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
  sets := satisfiableSets T A
  no_falsum s hs := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact hM.bot_notMem
  no_contradiction s hs φ h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact hM.not_notMem h
  imp s hs φ ψ h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := subset_instances hT hs h
    exact (hM.realize_of_imp_mem h).imp
      (insert_mem_of_model hs (hA.not_mem_instances_iff.2 (imp_left_mem_instances hi)) hM)
      (insert_mem_of_model hs (imp_right_mem_instances hi) hM)
  not_imp s hs φ ψ h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := imp_left_mem_instances (subset_instances hT hs h)
    exact ⟨insert_mem_of_model hs (imp_left_mem_instances hi) hM (hM.realize_of_not_imp_mem h).1,
      insert_mem_of_model hs (hA.not_mem_instances_iff.2 (imp_right_mem_instances hi)) hM
        (hM.realize_of_not_imp_mem h).2⟩
  iInf s hs φs h k := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact insert_mem_of_model hs (iInf_mem_instances (subset_instances hT hs h) k) hM
      (SentenceInf.realize_iInf.1 (Theoryω.Model.realize_of_mem hM h) k)
  not_iInf s hs φs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := hA.not_mem_instances_iff.1 (subset_instances hT hs h)
    obtain ⟨k, hk⟩ := hM.realize_of_not_iInf_mem h
    exact ⟨k, insert_mem_of_model hs (hA.not_mem_instances_iff.2 (iInf_mem_instances hi k)) hM hk⟩
  iSup s hs φs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    obtain ⟨k, hk⟩ := SentenceInf.realize_iSup.1 (Theoryω.Model.realize_of_mem hM h)
    exact ⟨k, insert_mem_of_model hs (iSup_mem_instances (subset_instances hT hs h) k) hM hk⟩
  not_iSup s hs φs h k := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi := hA.not_mem_instances_iff.1 (subset_instances hT hs h)
    exact insert_mem_of_model hs (hA.not_mem_instances_iff.2 (iSup_mem_instances hi k)) hM
      (hM.realize_of_not_iSup_mem h k)
  all s hs φ h c := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact insert_mem_of_model hs (inst_mem_instances (subset_instances hT hs h) c) hM
      (SentenceInf.realize_inst_of_realize_all (hM.realize_of_mem h) _)
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
      have hr := hM.realize_of_instConstants_mem (hχ ▸ h)
      simp only [realize_imp, realize_all, realize_falsum, imp_false, not_forall] at hr
      exact hr
    obtain ⟨e', he'c, he, hs'⟩ := exists_update_model hF subset_rfl hM hc m
    have hed : e' ∘ d = e ∘ d := funext fun i => (he (hd i)).symm
    let := constantsOn.structure e'
    have hX : SentenceInf.Realize (φ.inst (L.con c).term).not M := by
      rw [hinst c, ← instConstants_not, SentenceInf.realize_def,
        realize_instConstants_constantsOn, realize_not, Fin.comp_snoc, he'c, hed]
      exact hm
    refine ⟨c, insert_mem hs (hA.not_mem_instances_iff.2
      (inst_mem_instances (imp_left_mem_instances (subset_instances hT hs h)) c))
      (Theoryω.model_insert_iff.2 ⟨hX, hs'⟩).isSatisfiable⟩
  eq_refl s hs t := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    exact insert_mem_of_model hs (hA.mem_instances_of_isAtomic (.equal _ _)) hM
      (SentenceInf.realize_equal_self t)
  eq_subst s hs t t' φ hφ ht htφ := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.2
    have hi : (φ.inst t').IsAtomic := by rw [inst_def]; exact hφ.substBounds _
    exact insert_mem_of_model hs (hA.mem_instances_of_isAtomic hi) hM
      (SentenceInf.realize_inst_of_realize_equal (hM.realize_of_mem ht)
        (hM.realize_of_mem htφ))
  eq_name s hs t := by
    -- Write `t` with its constants `d` abstracted, and reinterpret a Henkin constant `c`
    -- occurring neither in `s` nor in `t` as the value of `t`.
    obtain ⟨M, _, _, e, F, hFf, hF, hM⟩ := exists_model_of_mem hs
    obtain ⟨n, r, d, rfl⟩ := t.exists_onTerm_subst_eq
    obtain ⟨c, hc⟩ := (hFf.union (Set.finite_range d)).exists_notMem
    obtain ⟨e', he'c, he, hs'⟩ := exists_update_model hF Set.subset_union_left hM hc
      (r.realize (Sum.elim Empty.elim (e ∘ d)))
    let := constantsOn.structure e'
    have hed : (fun i => (L.con (d i) : M)) = e ∘ d := funext fun i =>
      (coe_con_constantsOn_structure e' (d i)).trans (he (Or.inr ⟨i, rfl⟩)).symm
    refine ⟨c, insert_mem hs (hA.mem_instances_of_isAtomic (.equal _ _))
      (Theoryω.model_insert_iff.2 ⟨?_, hs'⟩).isSatisfiable⟩
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal, Term.realize_constants,
      Term.realize_onTerm_subst_con, coe_con_constantsOn_structure, he'c, hed]

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
  let := constantsOn.structure fun _ : ℕ => Classical.arbitrary M
  exact ((LHom.onTheoryω_model _ T).2 hM).isSatisfiable

/-- **Members of `ofSatisfiable` have expansion models**: a member has a nonempty model that is
the expansion of an `L`-structure by an interpretation `e` of the Henkin constants, and its
sentences are instances at tuples of constants from one finite set `F`. -/
theorem exists_model_of_mem_ofSatisfiable {hA : A.FormationClosed} {hT} {s : L[[ℕ]].Theoryω}
    (hs : s ∈ (ofSatisfiable T A hA hT).sets) :
    ∃ (M : Type (max u v)) (_ : L.Structure M) (_ : Nonempty M) (e : ℕ → M) (F : Set ℕ),
      F.Finite ∧ (∀ φ ∈ s, ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (d : Fin n → ℕ),
        χ.instConstants d = φ ∧ ∀ i, d i ∈ F) ∧
      (letI := constantsOn.structure e; s.Model M) :=
  exists_model_of_mem hs

/-- Adding an instance to a member of `ofSatisfiable` gives a member, provided the enlarged
theory is satisfiable. -/
theorem insert_mem_ofSatisfiable {hA : A.FormationClosed} {hT} {s : L[[ℕ]].Theoryω}
    {X : L[[ℕ]].Sentenceω} (hs : s ∈ (ofSatisfiable T A hA hT).sets) (hX : X ∈ A.instances ℕ)
    (hsat : (insert X s).IsSatisfiable) : insert X s ∈ (ofSatisfiable T A hA hT).sets :=
  insert_mem hs hX hsat

end ofSatisfiable

end ConsistencyProperty

end Language

end FirstOrder
