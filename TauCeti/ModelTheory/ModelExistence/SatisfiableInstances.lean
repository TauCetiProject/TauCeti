/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FormationClosed
public import TauCeti.ModelTheory.Infinitary.Satisfiability
public import TauCeti.ModelTheory.ModelExistence.ConsistencyProperty

/-!
# The consistency property of satisfiable sets of instances

Let `A` be a formation-closed fragment of `L_{ω₁ω}` and `T` a theory all of whose sentences
belong to `A`. A finite set `σ` of **instances** of members of `A` at Henkin constants, sentences
`χ[c]` of `L[[ℕ]]` obtained from a member `⟨n, χ⟩` of `A` by replacing its bound positions with the
constants `L.con (c i)`, may be added to `T`. The sets `T ∪ σ` that are satisfiable form a
consistency property, `ConsistencyProperty.ofSatisfiable T A`.

Each clause is checked semantically in a model of `T ∪ σ`. Formation closure keeps the sentences
added by the propositional and quantifier clauses inside the instances of `A`: the negation of an
instance is an instance, and every atomic sentence of `L[[ℕ]]` is an instance, since its finitely
many constants can be abstracted into bound positions. Finiteness of `σ` leaves fresh Henkin
constants: the witness clause for a negated universal sentence and the naming clause for a closed
term reinterpret a constant that does not occur in `σ` or in the term, which changes the truth of
no sentence of `T ∪ σ`.

This is the consistency property to which model existence is applied in the omitting types
theorem for countable formation-closed fragments: a countable satisfiable theory `T` inside `A` is
a countable member (`onTheoryω_mem_ofSatisfiable`, `countable_of_mem_ofSatisfiable`), and a member
can be extended by any instance that keeps it satisfiable (`insert_mem_ofSatisfiable`).

## Main definitions

* `FirstOrder.Language.Fragment.instances`: the instances of the members of a fragment at tuples
  of constants of `L[[γ]]`.
* `FirstOrder.Language.ConsistencyProperty.ofSatisfiable`: the satisfiable sets `T ∪ σ` with
  `σ` a finite set of instances of a formation-closed fragment containing `T`.

## Main results

* `FirstOrder.Language.Fragment.FormationClosed.mem_instances_of_isAtomic`: every atomic
  sentence of `L[[γ]]` is an instance of a formation-closed fragment.
* `FirstOrder.Language.ConsistencyProperty.onTheoryω_mem_ofSatisfiable`: a satisfiable theory
  inside the fragment is a member.
* `FirstOrder.Language.ConsistencyProperty.insert_mem_ofSatisfiable`: adding an instance to a
  member keeps it a member as long as the result is satisfiable.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.1.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
-/

public section

universe u v w

namespace FirstOrder.Language

open BoundedFormulaInf

variable {L : Language.{u, v}}

namespace Fragment

variable (A : Fragment L) (γ : Type*)

/-- The **instances at constants** of a fragment: the sentences of `L[[γ]]` obtained from a member
`⟨n, χ⟩` of `A` by replacing its `n` bound positions with constants `L.con (c i)`. -/
def instances : Set L[[γ]].Sentenceω :=
  {θ | ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (c : Fin n → γ),
    (⟨n, χ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧ χ.instConstants c = θ}

variable {A γ}

/-- Unfolding lemma for `Fragment.instances`. -/
theorem mem_instances_iff {θ : L[[γ]].Sentenceω} :
    θ ∈ A.instances γ ↔ ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (c : Fin n → γ),
      (⟨n, χ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧ χ.instConstants c = θ :=
  Iff.rfl

/-- The image in `L[[γ]]` of a member sentence is an instance. -/
theorem onBoundedFormulaInf_mem_instances {φ : L.Sentenceω}
    (h : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (L.lhomWithConstants γ).onBoundedFormulaInf φ ∈ A.instances γ :=
  ⟨0, φ, Fin.elim0, h, instConstants_zero _ _⟩

/-- The antecedent of an instance implication is an instance. -/
theorem imp_left_mem_instances {φ ψ : L[[γ]].Sentenceω} (h : φ.imp ψ ∈ A.instances γ) :
    φ ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, h⟩ := h
  obtain ⟨χ₁, χ₂, rfl, h₁, -⟩ := instConstants_eq_imp_iff.1 h
  exact ⟨n, χ₁, c, A.imp_left_mem hχ, h₁⟩

/-- The consequent of an instance implication is an instance. -/
theorem imp_right_mem_instances {φ ψ : L[[γ]].Sentenceω} (h : φ.imp ψ ∈ A.instances γ) :
    ψ ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, h⟩ := h
  obtain ⟨χ₁, χ₂, rfl, -, h₂⟩ := instConstants_eq_imp_iff.1 h
  exact ⟨n, χ₂, c, A.imp_right_mem hχ, h₂⟩

/-- Every conjunct of an instance countable conjunction is an instance. -/
theorem iInf_mem_instances {φs : ℕ → L[[γ]].Sentenceω} (h : iInf φs ∈ A.instances γ) (k : ℕ) :
    φs k ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, h⟩ := h
  obtain ⟨χs, rfl, hs⟩ := instConstants_eq_iInf_iff.1 h
  exact ⟨n, χs k, c, A.iInf_mem hχ k, hs k⟩

/-- Every disjunct of an instance countable disjunction is an instance. -/
theorem iSup_mem_instances {φs : ℕ → L[[γ]].Sentenceω} (h : iSup φs ∈ A.instances γ) (k : ℕ) :
    φs k ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, h⟩ := h
  obtain ⟨χs, rfl, hs⟩ := instConstants_eq_iSup_iff.1 h
  exact ⟨n, χs k, c, A.iSup_mem hχ k, hs k⟩

/-- The body of an instance universal sentence, instantiated at a constant, is an instance. -/
theorem inst_mem_instances {φ : L[[γ]].BoundedFormulaω Empty 1} (h : φ.all ∈ A.instances γ)
    (d : γ) : φ.inst (L.con d).term ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, h⟩ := h
  obtain ⟨χ', rfl, h'⟩ := exists_of_instConstants_eq_all h
  exact ⟨n + 1, χ', Fin.snoc c d, A.all_mem hχ, (h' d).symm⟩

namespace FormationClosed

variable (hA : A.FormationClosed)
include hA

/-- A negation is an instance of a formation-closed fragment exactly when the negated sentence
is. -/
theorem not_mem_instances_iff {φ : L[[γ]].Sentenceω} :
    φ.not ∈ A.instances γ ↔ φ ∈ A.instances γ := by
  refine ⟨imp_left_mem_instances, fun ⟨n, χ, c, hχ, h⟩ => ⟨n, χ.not, c, ?_, ?_⟩⟩
  · exact (hA.not_mem_iff).2 hχ
  · rw [instConstants_not, h]

/-- Every atomic sentence of `L[[γ]]` is an instance of a formation-closed fragment. -/
theorem mem_instances_of_isAtomic {θ : L[[γ]].Sentenceω} (h : θ.IsAtomic) :
    θ ∈ A.instances γ := by
  obtain ⟨k, χ, c, hχ, rfl⟩ := exists_instConstants_eq_of_isAtomic h
  exact ⟨k, χ, c, hA.atomic_mem hχ, rfl⟩

end FormationClosed

end Fragment

namespace ConsistencyProperty

/-! ### Reinterpreting Henkin constants -/

section Constants

variable {M : Type w}

/-- An instance at constants holds in an `L`-structure with the constants interpreted by `e`
when the formula holds at the interpretations of its constants. -/
private theorem realize_instConstants_constantsOn [L.Structure M] (e : ℕ → M) {n : ℕ}
    (χ : L.BoundedFormulaω Empty n) (c : Fin n → ℕ) :
    (letI := constantsOn.structure e; SentenceInf.Realize (χ.instConstants c) M) ↔
      χ.Realize Empty.elim (e ∘ c) := by
  let := constantsOn.structure e
  rw [SentenceInf.realize_def, realize_instConstants]
  rfl

/-- A model of a set of sentences of `L[[ℕ]]` with the constants interpreted by `e` on top of an
`L`-structure. -/
private theorem model_constantsOn_iff [L.Structure M] (e : ℕ → M) {s : L[[ℕ]].Theoryω} :
    (letI := constantsOn.structure e; s.Model M) ↔
      ∀ θ ∈ s, letI := constantsOn.structure e; SentenceInf.Realize θ M := by
  let := constantsOn.structure e
  exact Theoryω.model_iff

/-- A satisfiable set of instances at Henkin constants has a model whose constants are
interpreted on top of an `L`-structure: the `L`-reduct of any model, with its constants. -/
private theorem exists_model_constantsOn {A : Fragment L} {s : L[[ℕ]].Theoryω}
    (hs : ∀ θ ∈ s, θ ∈ A.instances ℕ) (h : s.IsSatisfiable) :
    ∃ (M : Type (max u v)) (_ : L.Structure M) (e : ℕ → M), Nonempty M ∧
      (letI := constantsOn.structure e; s.Model M) := by
  obtain ⟨M, S, hM, h⟩ := Theoryω.isSatisfiable_iff.1 h
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  refine ⟨M, this, fun i => (L.con i : M), hM, (model_constantsOn_iff _).2 fun θ hθ => ?_⟩
  obtain ⟨n, χ, c, -, rfl⟩ := hs θ hθ
  rw [realize_instConstants_constantsOn]
  have h := h.realize_of_mem hθ
  rwa [SentenceInf.realize_def, realize_instConstants] at h

end Constants

/-! ### Instances with bounded constants -/

section Bounded

variable {A : Fragment L}

/-- `θ` is the instance of a member of `A` at a tuple of Henkin constants below `N`. -/
private def InstBelow (A : Fragment L) (N : ℕ) (θ : L[[ℕ]].Sentenceω) : Prop :=
  ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (c : Fin n → ℕ),
    (⟨n, χ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧ (∀ i, c i < N) ∧ χ.instConstants c = θ

/-- Reinterpreting the Henkin constants from `N` on keeps a model of a set of instances with
constants below `N` a model, and adds every sentence true in the new interpretation. -/
private theorem isSatisfiable_insert_of_instBelow {s : L[[ℕ]].Theoryω} {N : ℕ}
    (hN : ∀ θ ∈ s, InstBelow A N θ) {M : Type (max u v)} [L.Structure M] [Nonempty M]
    {e e' : ℕ → M} (hM : letI := constantsOn.structure e; s.Model M)
    (he : ∀ i < N, e' i = e i) {θ : L[[ℕ]].Sentenceω}
    (hθ : letI := constantsOn.structure e'; SentenceInf.Realize θ M) :
    (insert θ s).IsSatisfiable := by
  have hs : ∀ θ ∈ s, ∃ (n : ℕ) (χ : L.BoundedFormulaω Empty n) (c : Fin n → ℕ),
      (∀ i, c i < N) ∧ χ.instConstants c = θ ∧ χ.Realize Empty.elim (e ∘ c) := by
    intro θ hθ
    obtain ⟨n, χ, c, -, hc, rfl⟩ := hN θ hθ
    refine ⟨n, χ, c, hc, rfl, (realize_instConstants_constantsOn e χ c).1 ?_⟩
    let := constantsOn.structure e
    exact hM.realize_of_mem hθ
  let := constantsOn.structure e'
  refine Theoryω.isSatisfiable_iff.2 ⟨M, inferInstance, inferInstance,
    Theoryω.model_insert_iff.2 ⟨hθ, Theoryω.model_iff.2 fun θ hθ => ?_⟩⟩
  obtain ⟨n, χ, c, hc, rfl, h⟩ := hs θ hθ
  rw [realize_instConstants_constantsOn]
  have hc : e' ∘ c = e ∘ c := funext fun i => he _ (hc i)
  rwa [hc]

end Bounded

/-! ### The consistency property -/

section OfSatisfiable

variable {T : L.Theoryω} {A : Fragment L}

/-- The members of `ofSatisfiable T A`: satisfiable sets `T ∪ σ` with `σ` a finite set of
instances of `A`. -/
private def IsMem (T : L.Theoryω) (A : Fragment L) (s : L[[ℕ]].Theoryω) : Prop :=
  s.IsSatisfiable ∧ ∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧ σ ⊆ A.instances ℕ ∧
    s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ

variable (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
include hT

/-- Every sentence of a member is an instance. -/
private theorem IsMem.mem_instances {s : L[[ℕ]].Theoryω} (hs : IsMem T A s)
    {θ : L[[ℕ]].Sentenceω} (hθ : θ ∈ s) : θ ∈ A.instances ℕ := by
  obtain ⟨-, σ, -, hσ, rfl⟩ := hs
  rcases hθ with hθ | hθ
  · obtain ⟨φ, hφ, rfl⟩ := LHom.mem_onTheoryω.1 hθ
    exact Fragment.onBoundedFormulaInf_mem_instances (hT φ hφ)
  · exact hσ hθ

/-- The constants of the instances in a member are bounded. -/
private theorem IsMem.exists_instBelow {s : L[[ℕ]].Theoryω} (hs : IsMem T A s) :
    ∃ N, ∀ θ ∈ s, InstBelow A N θ := by
  obtain ⟨-, σ, hσf, hσ, rfl⟩ := hs
  have hθ (θ : σ) : ∃ N, InstBelow A N θ := by
    obtain ⟨n, χ, c, hχ, h⟩ := hσ θ.2
    obtain ⟨B, hB⟩ := (Set.finite_range c).bddAbove
    exact ⟨B + 1, n, χ, c, hχ, fun i => Nat.lt_succ_of_le (hB ⟨i, rfl⟩), h⟩
  choose f hf using hθ
  have : Finite σ := hσf
  obtain ⟨N, hN⟩ := (Set.finite_range f).bddAbove
  refine ⟨N, ?_⟩
  rintro θ (hθ | hθ)
  · obtain ⟨φ, hφ, rfl⟩ := LHom.mem_onTheoryω.1 hθ
    exact ⟨0, φ, Fin.elim0, hT φ hφ, fun i => i.elim0, instConstants_zero _ _⟩
  · obtain ⟨n, χ, c, hχ, hc, h⟩ := hf ⟨θ, hθ⟩
    exact ⟨n, χ, c, hχ, fun i => (hc i).trans_le (hN ⟨_, rfl⟩), h⟩

omit hT in
/-- Adding a satisfiable instance to a member gives a member. -/
private theorem IsMem.insert_mem {s : L[[ℕ]].Theoryω} (hs : IsMem T A s) {θ : L[[ℕ]].Sentenceω}
    (hθ : θ ∈ A.instances ℕ) (h : (insert θ s).IsSatisfiable) : IsMem T A (insert θ s) := by
  obtain ⟨-, σ, hσf, hσ, rfl⟩ := hs
  exact ⟨h, insert θ σ, hσf.insert θ, Set.insert_subset hθ hσ, (Set.union_insert ..).symm⟩

omit hT in
/-- Adding a sentence true in a model of a member gives a satisfiable set. -/
private theorem isSatisfiable_insert {s : L[[ℕ]].Theoryω} {M : Type (max u v)}
    [L[[ℕ]].Structure M] [Nonempty M] (hM : s.Model M) {θ : L[[ℕ]].Sentenceω}
    (hθ : SentenceInf.Realize θ M) : (insert θ s).IsSatisfiable :=
  Theoryω.isSatisfiable_iff.2 ⟨M, inferInstance, inferInstance,
    Theoryω.model_insert_iff.2 ⟨hθ, hM⟩⟩

variable (hA : A.FormationClosed)
include hA

/-- **The satisfaction instance for fragments.** For a formation-closed fragment `A` and a
theory `T` inside `A`, the satisfiable sets `T ∪ σ`, with `σ` a finite set of instances of members
of `A` at Henkin constants, form a consistency property. -/
def ofSatisfiable : ConsistencyProperty L where
  sets := {s | IsMem T A s}
  no_falsum s hs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    exact SentenceInf.realize_bot.1 (hM.realize_of_mem h)
  no_contradiction s hs φ h h' := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    exact SentenceInf.realize_not.1 (hM.realize_of_mem h') (hM.realize_of_mem h)
  imp s hs φ ψ h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    have hi := hs.mem_instances hT h
    have h' : SentenceInf.Realize φ M → SentenceInf.Realize ψ M := by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_imp] using
        hM.realize_of_mem h
    by_cases hφ : SentenceInf.Realize φ M
    · exact .inr (hs.insert_mem (Fragment.imp_right_mem_instances hi)
        (isSatisfiable_insert hM (h' hφ)))
    · exact .inl (hs.insert_mem ((hA.not_mem_instances_iff).2 (Fragment.imp_left_mem_instances hi))
        (isSatisfiable_insert hM (SentenceInf.realize_not.2 hφ)))
  not_imp s hs φ ψ h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    have hi := (hA.not_mem_instances_iff).1 (hs.mem_instances hT h)
    have h' : SentenceInf.Realize φ M ∧ ¬SentenceInf.Realize ψ M := by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_not, realize_imp,
        Classical.not_imp] using hM.realize_of_mem h
    exact ⟨hs.insert_mem (Fragment.imp_left_mem_instances hi) (isSatisfiable_insert hM h'.1),
      hs.insert_mem ((hA.not_mem_instances_iff).2 (Fragment.imp_right_mem_instances hi))
        (isSatisfiable_insert hM (SentenceInf.realize_not.2 h'.2))⟩
  iInf s hs φs h k := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    exact hs.insert_mem (Fragment.iInf_mem_instances (hs.mem_instances hT h) k)
      (isSatisfiable_insert hM (SentenceInf.realize_iInf.1 (hM.realize_of_mem h) k))
  not_iInf s hs φs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    have hi := (hA.not_mem_instances_iff).1 (hs.mem_instances hT h)
    have h' := SentenceInf.realize_not.1 (hM.realize_of_mem h)
    obtain ⟨k, hk⟩ := not_forall.1 (h' ∘ SentenceInf.realize_iInf.2)
    exact ⟨k, hs.insert_mem ((hA.not_mem_instances_iff).2 (Fragment.iInf_mem_instances hi k))
      (isSatisfiable_insert hM (SentenceInf.realize_not.2 hk))⟩
  iSup s hs φs h := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    obtain ⟨k, hk⟩ := SentenceInf.realize_iSup.1 (hM.realize_of_mem h)
    exact ⟨k, hs.insert_mem (Fragment.iSup_mem_instances (hs.mem_instances hT h) k)
      (isSatisfiable_insert hM hk)⟩
  not_iSup s hs φs h k := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    have hi := (hA.not_mem_instances_iff).1 (hs.mem_instances hT h)
    have h' := SentenceInf.realize_not.1 (hM.realize_of_mem h)
    exact hs.insert_mem ((hA.not_mem_instances_iff).2 (Fragment.iSup_mem_instances hi k))
      (isSatisfiable_insert hM
        (SentenceInf.realize_not.2 fun hk => h' (SentenceInf.realize_iSup.2 ⟨k, hk⟩)))
  all s hs φ h c := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    refine hs.insert_mem (Fragment.inst_mem_instances (hs.mem_instances hT h) c)
      (isSatisfiable_insert hM ?_)
    have h' := hM.realize_of_mem h
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all] at h'
    simp only [SentenceInf.realize_def, realize_inst, Term.realize_constants]
    simpa only [Fin.snoc_zero] using h' (L.con c)
  not_all s hs φ h := by
    obtain ⟨M, _, e, _, hM⟩ := exists_model_constantsOn (fun _ => hs.mem_instances hT) hs.1
    obtain ⟨N, hN⟩ := hs.exists_instBelow hT
    -- `¬∀φ` is an instance `(∀χ')[c]` with constants below `N`, so `N` is a fresh constant
    obtain ⟨n, χ, c, -, hc, hχ⟩ := hN _ h
    obtain ⟨χ₁, χ₂, rfl, h₁, -⟩ := instConstants_eq_imp_iff.1 hχ
    obtain ⟨χ', rfl, hinst⟩ := exists_of_instConstants_eq_all h₁
    have hm : ∃ m, ¬χ'.Realize Empty.elim (Fin.snoc (e ∘ c) m) := by
      let := constantsOn.structure e
      have h' := SentenceInf.realize_not.1 (hM.realize_of_mem h)
      rw [← h₁, SentenceInf.realize_def, realize_instConstants, realize_all] at h'
      exact not_forall.1 h'
    obtain ⟨m, hm⟩ := hm
    refine ⟨N, hs.insert_mem ((hA.not_mem_instances_iff).2
      (Fragment.inst_mem_instances (Fragment.imp_left_mem_instances (hs.mem_instances hT h)) N))
      (isSatisfiable_insert_of_instBelow hN hM (e' := Function.update e N m)
        (fun i hi => Function.update_of_ne hi.ne _ _) ?_)⟩
    -- reinterpret the constant `N` as the counterexample `m`
    let := constantsOn.structure (Function.update e N m)
    rw [SentenceInf.realize_not, hinst N, realize_instConstants_constantsOn]
    convert hm using 2
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp [Function.update_of_ne (hc i).ne]
  eq_refl s hs t := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    refine hs.insert_mem (hA.mem_instances_of_isAtomic (.equal t t)) (isSatisfiable_insert hM ?_)
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal]
  eq_subst s hs t t' φ hφ ht hφt := by
    obtain ⟨M, _, _, hM⟩ := Theoryω.isSatisfiable_iff.1 hs.1
    refine hs.insert_mem (hA.mem_instances_of_isAtomic (by rw [inst_def]; exact hφ.substBounds _))
      (isSatisfiable_insert hM ?_)
    have ht := hM.realize_of_mem ht
    have hφt := hM.realize_of_mem hφt
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal] at ht
    simp only [SentenceInf.realize_def, realize_inst] at hφt ⊢
    rwa [← ht]
  eq_name s hs t := by
    obtain ⟨M, _, e, _, hM⟩ := exists_model_constantsOn (fun _ => hs.mem_instances hT) hs.1
    obtain ⟨N, hN⟩ := hs.exists_instBelow hT
    -- abstract the finitely many constants of `t` into bound positions below a fresh `d`
    obtain ⟨B, hB⟩ := t.finite_setOf_con_mem_functionsIn.bddAbove
    set d := max N (B + 1)
    obtain ⟨t₀, ht₀⟩ := t.exists_instConstants_eq (Fin.val : Fin d → ℕ) fun a ha =>
      ⟨⟨a, (Nat.lt_succ_of_le (hB ha)).trans_le (le_max_right _ _)⟩, rfl⟩
    refine ⟨d, hs.insert_mem (hA.mem_instances_of_isAtomic (.equal _ _))
      (isSatisfiable_insert_of_instBelow hN hM
        (e' := Function.update e d (t₀.realize (Sum.elim Empty.elim (e ∘ Fin.val))))
        (fun i hi => Function.update_of_ne (hi.trans_le (le_max_left _ _)).ne _ _) ?_)⟩
    -- reinterpret the constant `d` as the value of `t`
    let := constantsOn.structure
      (Function.update e d (t₀.realize (Sum.elim Empty.elim (e ∘ Fin.val))))
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal,
      Term.realize_constants]
    rw [← ht₀, Term.realize_instConstants]
    refine (Function.update_self ..).trans ?_
    congr 1
    funext a
    rcases a with a | i
    · exact a.elim
    · exact (Function.update_of_ne i.isLt.ne _ _).symm

/-- The members of `ofSatisfiable T A` are the satisfiable sets `T ∪ σ`, with `σ` a finite set of
instances of `A`. -/
theorem mem_ofSatisfiable_iff {s : L[[ℕ]].Theoryω} :
    s ∈ (ofSatisfiable hT hA).sets ↔ s.IsSatisfiable ∧ ∃ σ : L[[ℕ]].Theoryω, σ.Finite ∧
      σ ⊆ A.instances ℕ ∧ s = (L.lhomWithConstants ℕ).onTheoryω T ∪ σ :=
  Iff.rfl

/-- A satisfiable theory inside a formation-closed fragment, viewed in `L[[ℕ]]`, is a member of
`ofSatisfiable`. -/
theorem onTheoryω_mem_ofSatisfiable (h : T.IsSatisfiable) :
    (L.lhomWithConstants ℕ).onTheoryω T ∈ (ofSatisfiable hT hA).sets := by
  obtain ⟨M, _, hM, h⟩ := Theoryω.isSatisfiable_iff.1 h
  let := constantsOn.structure fun _ : ℕ => Classical.arbitrary M
  exact ⟨Theoryω.isSatisfiable_iff.2 ⟨M, inferInstance, hM, (LHom.onTheoryω_model _ T).2 h⟩, ∅,
    Set.finite_empty, Set.empty_subset _, (Set.union_empty _).symm⟩

/-- Adding an instance to a member of `ofSatisfiable` gives a member as long as the result is
satisfiable. -/
theorem insert_mem_ofSatisfiable {s : L[[ℕ]].Theoryω} (hs : s ∈ (ofSatisfiable hT hA).sets)
    {θ : L[[ℕ]].Sentenceω} (hθ : θ ∈ A.instances ℕ) (h : (insert θ s).IsSatisfiable) :
    insert θ s ∈ (ofSatisfiable hT hA).sets :=
  IsMem.insert_mem hs hθ h

/-- Every sentence of a member of `ofSatisfiable T A` is an instance of `A`. -/
theorem mem_instances_of_mem_ofSatisfiable {s : L[[ℕ]].Theoryω}
    (hs : s ∈ (ofSatisfiable hT hA).sets) {θ : L[[ℕ]].Sentenceω} (hθ : θ ∈ s) :
    θ ∈ A.instances ℕ :=
  IsMem.mem_instances hT hs hθ

/-- The members of `ofSatisfiable T A` are countable when `T` is. -/
theorem countable_of_mem_ofSatisfiable (hTc : T.Countable) {s : L[[ℕ]].Theoryω}
    (hs : s ∈ (ofSatisfiable hT hA).sets) : s.Countable := by
  obtain ⟨-, σ, hσ, -, rfl⟩ := hs
  exact (hTc.onTheoryω _).union hσ.countable

end OfSatisfiable

end ConsistencyProperty

end FirstOrder.Language
