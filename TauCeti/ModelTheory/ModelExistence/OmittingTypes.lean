/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FiniteInstances
public import TauCeti.ModelTheory.ModelExistence.Isolation
public import TauCeti.ModelTheory.ModelExistence.ModelExistence
import TauCeti.ModelTheory.LanguageMap
import TauCeti.ModelTheory.Semantics

/-!
# Omitting types in countable fragments

A satisfiable theory of sentences in a countable formation-closed fragment has a countable
nonempty model omitting any countable family of partial types in the fragment, provided none
is isolated over the theory in that fragment. The model may be constructed in any universe.
Consequently a partial type realized in every countable nonempty model is isolated.
Over a language with countably many symbols, applying the theorem to the first-order image
fragment gives the first-order omitting types theorem, for a first-order theory satisfiable in the
sense of Mathlib's `Theory.IsSatisfiable` and first-order partial types not isolated by a
first-order formula modulo the theory. Consequently, over a countable language, a first-order
partial type realized in every countable nonempty model of a satisfiable theory is isolated modulo
that theory; over a complete theory the converse also holds. By contrast, `Theory.IsSatisfiable`
alone detects only finite satisfiability: a partial type is realized in *some* nonempty model if and
only if every finite subset has a satisfiable conjunction, so isolation and realizability coincide
for finite partial types.

The key refutation lemma applies to the consistency property of satisfiable finite instances.
Projecting those instances onto a prescribed tuple of Henkin constants gives a consistent
formula of the fragment. Non-isolation supplies a model and a tuple satisfying that formula
but refuting a member of the type. The projection theorem then interprets all the constants,
even when the prescribed tuple repeats a constant. The model-existence theorem with omission
requests supplies the final model.

## Main results

* `FirstOrder.Language.Theoryω.exists_countable_model_omitting`: the omitting types theorem for a
  countable formation-closed fragment.
* `FirstOrder.Language.Theoryω.isolatesIn_of_realized_in_every_countable_model`: a partial type
  realized in every countable nonempty model of the theory is isolated.
* `FirstOrder.Language.Theory.exists_countable_model_omitting`: the first-order omitting types
  theorem.
* `FirstOrder.Language.Theory.exists_modelType_realize_iff_forall_finset_isSatisfiable`: a
  first-order partial type is realized in some nonempty model if and only if the conjunction of
  every finite subset is satisfiable with the theory.
* `FirstOrder.Language.Theory.exists_isolating_iff_of_finite`: a finite first-order partial type is
  isolated modulo a theory if and only if it is realized in some nonempty model.
* `FirstOrder.Language.Theory.exists_isolating_of_realized_in_every_countable_model`: over a
  countable language, a first-order partial type realized in every countable nonempty model of a
  satisfiable theory is isolated modulo that theory.
* `FirstOrder.Language.Theory.IsComplete.exists_isolating_iff_realized_in_every_countable_model`:
  over a complete theory in a countable language, a first-order partial type is isolated if and
  only if it is realized in every countable nonempty model.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 4.
* D. Marker, *Model Theory: An Introduction*, Springer, 2002, Section 4.2.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
-/

public section

universe u v w

namespace FirstOrder.Language

open BoundedFormulaInf

variable {L : FirstOrder.Language.{u, v}} {A : Fragment L} {T : L.Theoryω}

/-- A non-isolated type can be refuted at every tuple of Henkin constants in every member of
the consistency property of satisfiable finite instances. No countability is needed for this
refutation step. -/
theorem ConsistencyProperty.exists_insert_not_mem_ofSatisfiable
    (hA : A.FormationClosed)
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    {n : ℕ} {p : Set (L.BoundedFormulaω Empty n)}
    (hp : ∀ ψ ∈ p, (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (hnp : ¬Theoryω.IsolatesIn A T p) {s : L[[ℕ]].Theoryω}
    (hs : s ∈ (ConsistencyProperty.ofSatisfiable T A hA hT).sets) (c : Fin n → ℕ) :
    ∃ ψ ∈ p, insert (ψ.instConstants c).not s ∈
      (ConsistencyProperty.ofSatisfiable T A hA hT).sets := by
  classical
  obtain ⟨⟨σ, hσ, hσA, hseq⟩, -⟩ := ConsistencyProperty.mem_ofSatisfiable_iff.1 hs
  obtain ⟨φ, hφ, hφr⟩ := hA.exists_formula_iff_exists_constants.{u, v, max u v} hσ hσA c
  have hsat : (insert φ.exs T).IsSatisfiable := by
    obtain ⟨M, _, _, e, _, -, -, hM⟩ :=
      ConsistencyProperty.exists_model_of_mem_ofSatisfiable hs
    let := constantsOn.structure e
    have hMT : T.Model M := (LHom.onTheoryω_model _ T).1
      (hM.mono (hseq ▸ Set.subset_union_left))
    have hr := (hφr M (e ∘ c)).2 ⟨e, rfl, hM.mono (hseq ▸ Set.subset_union_right)⟩
    exact (Theoryω.model_insert_iff.2 ⟨by
      simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_exs]
      exact ⟨e ∘ c, hr⟩, hMT⟩).isSatisfiable
  have hex : ∃ ψ ∈ p, ¬T.Entails (φ.imp ψ).alls := by
    by_contra! h
    exact hnp (Theoryω.isolatesIn_iff.2 ⟨φ, hφ, hsat, h⟩)
  obtain ⟨ψ, hψ, hψT⟩ := hex
  simp only [Theoryω.entails_iff, not_forall] at hψT
  obtain ⟨M, _, _, hMT, hfail⟩ := hψT
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_alls,
    realize_imp, not_forall] at hfail
  obtain ⟨a, ha, hψa⟩ := hfail
  obtain ⟨e, hec, heσ⟩ := (hφr M a).1 ha
  let := constantsOn.structure e
  have hMs : s.Model M := by
    rw [hseq, Theoryω.model_union_iff]
    exact ⟨(LHom.onTheoryω_model _ T).2 hMT, heσ⟩
  have hnot : SentenceInf.Realize (ψ.instConstants c).not M := by
    rw [SentenceInf.realize_not, SentenceInf.realize_def,
      realize_instConstants_constantsOn, hec]
    exact hψa
  exact ⟨ψ, hψ, ConsistencyProperty.insert_mem_ofSatisfiable hs
    (hA.not_mem_instances_iff.2 (Fragment.instConstants_mem_instances (hp ψ hψ) c))
    (Theoryω.model_insert_iff.2 ⟨hnot, hMs⟩).isSatisfiable⟩

namespace Theoryω

/-- **The omitting types theorem for a countable formation-closed fragment.** A satisfiable theory
of sentences of the fragment has a countable nonempty model, in any universe, omitting any
countable family of partial types in the fragment, none isolated over the theory in the fragment.
Countability of the language follows from countability and formation closure of the fragment. -/
theorem exists_countable_model_omitting
    (hAc : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) (hA : A.FormationClosed)
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) (hTs : T.IsSatisfiable)
    {ι : Type*} [Countable ι] {n : ι → ℕ} (p : ∀ i, Set (L.BoundedFormulaω Empty (n i)))
    (hp : ∀ i, ∀ ψ ∈ p i, (⟨n i, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (hnp : ∀ i, ¬IsolatesIn A T (p i)) :
    ∃ (M : Type w) (_ : L.Structure M), Countable M ∧ Nonempty M ∧ T.Model M ∧
      ∀ i, OmitsType M (p i) := by
  let := hA.countable_functions hAc
  let := hA.countable_relations hAc
  have hTc : T.Countable := (Fragment.slice_countable hAc 0).mono
    fun φ hφ => Fragment.mem_slice.2 (hT φ hφ)
  have hpc (i : ι) : (p i).Countable := (Fragment.slice_countable hAc (n i)).mono
    fun ψ hψ => Fragment.mem_slice.2 (hp i ψ hψ)
  let g := L.lhomWithConstants ℕ
  let C := ConsistencyProperty.ofSatisfiable T A hA hT
  have hC (i : ι) (s : L[[ℕ]].Theoryω) (hs : s ∈ C.sets) (c : Fin (n i) → ℕ) :
      ∃ ψ ∈ g.onBoundedFormulaInf '' p i,
        insert (substBounds (fun j => (L.con (c j)).term) ψ).not s ∈ C.sets := by
    obtain ⟨ψ, hψ, hsψ⟩ :=
      ConsistencyProperty.exists_insert_not_mem_ofSatisfiable hA hT (hp i) (hnp i) hs c
    rw [instConstants_def] at hsψ
    exact ⟨g.onBoundedFormulaInf ψ, ⟨ψ, hψ, rfl⟩, hsψ⟩
  obtain ⟨M, _, hMc, hMne, hM, -, hMo⟩ := C.model_existence_omitting.{u, v, w}
    (fun i => g.onBoundedFormulaInf '' p i) (fun i => (hpc i).image _) hC
    (ConsistencyProperty.onTheoryω_mem_ofSatisfiable hTs) (hTc.onTheoryω g)
  let : L.Structure M := g.reduct M
  refine ⟨M, inferInstance, hMc, hMne, (LHom.onTheoryω_model g T).1 hM, fun i => ?_⟩
  refine omitsType_iff.2 fun a => ?_
  obtain ⟨_, ⟨ψ, hψ, rfl⟩, hψa⟩ := omitsType_iff.1 (hMo i) a
  exact ⟨ψ, hψ, fun h => hψa ((LHom.realize_onBoundedFormulaInf g ψ Empty.elim a).2 h)⟩

/-- A partial type in a countable formation-closed fragment that is realized in every countable
nonempty model of a satisfiable theory of the fragment is isolated over that theory. It suffices
to test models in any one universe. -/
theorem isolatesIn_of_realized_in_every_countable_model
    (hAc : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) (hA : A.FormationClosed)
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) (hTs : T.IsSatisfiable)
    {n : ℕ} {p : Set (L.BoundedFormulaω Empty n)}
    (hp : ∀ ψ ∈ p, (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (h : ∀ (M : Type w) [L.Structure M] [Countable M] [Nonempty M], T.Model M → ¬OmitsType M p) :
    IsolatesIn A T p := by
  by_contra hnp
  obtain ⟨M, _, _, _, hMT, hMo⟩ := exists_countable_model_omitting.{u, v, w}
    hAc hA hT hTs (fun _ : Unit => p) (fun _ => hp) (fun _ => hnp)
  exact h M hMT (hMo ())

end Theoryω

namespace Theory

/-- **The first-order omitting types theorem.** Over a language with countably many function and
relation symbols, a satisfiable first-order theory `T` has a countable nonempty model, in any
universe, omitting any countable family of first-order partial types none of which is isolated
modulo `T`: for no formula `φ` is `T` together with the existential closure of `φ` satisfiable
while `T` models the universal closure of `φ → ψ` for every `ψ` in the type. -/
theorem exists_countable_model_omitting [Countable (Σ l, L.Functions l)]
    [Countable (Σ l, L.Relations l)] {T : L.Theory} (hT : T.IsSatisfiable)
    {ι : Type*} [Countable ι] {n : ι → ℕ} (p : ∀ i, Set (L.BoundedFormula Empty (n i)))
    (hnp : ∀ i, ¬∃ φ : L.BoundedFormula Empty (n i),
      (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p i, T ⊨ᵇ (φ.imp ψ).alls) :
    ∃ (M : Type w) (_ : L.Structure M), Countable M ∧ Nonempty M ∧ M ⊨ T ∧
      ∀ i (a : Fin (n i) → M), ∃ ψ ∈ p i, ¬ψ.Realize Empty.elim a := by
  obtain ⟨M, _, hMc, hMne, hMT, hMo⟩ := Theoryω.exists_countable_model_omitting.{u, v, w}
    (T := BoundedFormula.toOmega '' T) Fragment.firstOrder_countable
    Fragment.formationClosed_firstOrder
    (fun _ ⟨φ, _, hφ⟩ => hφ ▸ Fragment.toOmega_mem_firstOrder φ)
    (Theoryω.isSatisfiable_image_toOmega_iff.2 hT) (fun i => BoundedFormula.toOmega '' p i)
    (fun _ _ ⟨ψ, _, hψ⟩ => hψ ▸ Fragment.toOmega_mem_firstOrder ψ)
    (fun i => Theoryω.isolatesIn_firstOrder_iff.not.2 (hnp i))
  refine ⟨M, inferInstance, hMc, hMne, Theoryω.model_image_toOmega_iff.1 hMT, fun i a => ?_⟩
  obtain ⟨_, ⟨ψ, hψ, rfl⟩, hψa⟩ := omitsType_iff.1 (hMo i) a
  exact ⟨ψ, hψ, fun h => hψa ((BoundedFormula.realize_toInf ψ Empty.elim a).2 h)⟩

/-- Convert a bounded formula with no free variables into a sentence of `L[[Fin n]]` evaluating
its bound positions at the adjoined constants. -/
private def evalAtConstants {n : ℕ} (ψ : L.BoundedFormula Empty n) : L[[Fin n]].Sentence :=
  Formula.equivSentence (ψ.toFormula.relabel (Sum.elim Empty.elim id))

private theorem realize_evalAtConstants_iff {M : Type w} [L.Structure M] {n : ℕ}
    (a : Fin n → M) (ψ : L.BoundedFormula Empty n) :
    @Sentence.Realize _ M (@withConstantsStructure L M _ (Fin n) (constantsOn.structure a))
      (evalAtConstants ψ) ↔ ψ.Realize Empty.elim a := by
  let : (constantsOn (Fin n)).Structure M := constantsOn.structure a
  rw [evalAtConstants, Formula.realize_equivSentence, Formula.realize_relabel]
  have hfun :
      (fun i : Fin n => (L.con i : M)) ∘ Sum.elim Empty.elim id = Sum.elim Empty.elim a := by
    ext (x | i)
    · exact x.elim
    · rfl
  rw [hfun, BoundedFormula.realize_toFormula]
  rfl

private theorem realize_exs_iff {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) :
    M ⊨ φ.exs ↔ ∃ a : Fin n → M, φ.Realize Empty.elim a := by
  rw [Sentence.Realize, Subsingleton.elim (default : Empty → M) Empty.elim,
    BoundedFormula.realize_exs]

/-- A partial type isolated by a first-order formula `φ` modulo `T` is realized in some nonempty
model of `T`. -/
theorem exists_modelType_realize_of_isolating {T : L.Theory} {n : ℕ}
    {p : Set (L.BoundedFormula Empty n)} {φ : L.BoundedFormula Empty n}
    (hsat : (insert φ.exs T).IsSatisfiable) (himp : ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls) :
    ∃ M : ModelType.{u, v, max u v} T, ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a := by
  obtain ⟨M⟩ := hsat
  have hMT : M ⊨ T := M.is_model.mono (Set.subset_insert _ _)
  obtain ⟨a, ha⟩ := (realize_exs_iff φ).1 (M.is_model.realize_of_mem _ (Set.mem_insert _ _))
  let := hMT
  refine ⟨ModelType.of T M, a, fun ψ hψ => ?_⟩
  have hψa := (Sentence.realize_alls (φ.imp ψ)).1 ((himp ψ hψ).realize_sentence M) a
  exact BoundedFormula.realize_imp.1 hψa ha

/-- **Compactness for first-order partial types.** A partial type `p` is realized in some nonempty
model of `T` if and only if for every finite subset `s` of `p`, `T` together with the existential
closure of the conjunction of `s` is satisfiable in the sense of `Theory.IsSatisfiable`. Compare
with isolation modulo `T`, which asks for a single formula `φ` consistent with `T` that implies
every member of `p`. -/
theorem exists_modelType_realize_iff_forall_finset_isSatisfiable {T : L.Theory} {n : ℕ}
    {p : Set (L.BoundedFormula Empty n)} :
    (∃ M : ModelType.{u, v, max u v} T, ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a) ↔
      ∀ s : Finset (L.BoundedFormula Empty n), (s : Set (L.BoundedFormula Empty n)) ⊆ p →
        (insert (BoundedFormula.iInf fun ψ : s => ψ.1).exs T).IsSatisfiable := by
  constructor
  · rintro ⟨M, a, ha⟩ s hs
    have hM : M ⊨ insert (BoundedFormula.iInf fun ψ : s => ψ.1).exs T := by
      refine model_insert_iff.2 ⟨(realize_exs_iff _).2 ?_, M.is_model⟩
      exact ⟨a, BoundedFormula.realize_iInf.2 fun ψ => ha ψ.1 (hs ψ.2)⟩
    let := hM
    exact Model.isSatisfiable M
  · intro hfin
    let g := L.lhomWithConstants (Fin n)
    let Sub := {s : Finset (L.BoundedFormula Empty n) // (s : Set (L.BoundedFormula Empty n)) ⊆ p}
    have : Nonempty Sub := ⟨⟨∅, by simp⟩⟩
    let S : Sub → L[[Fin n]].Theory := fun s => g.onTheory T ∪ evalAtConstants '' (s.1 : Set _)
    have hdir : Directed (· ⊆ ·) S := by
      classical
      intro s₁ s₂
      refine ⟨⟨s₁.1 ∪ s₂.1, by simp [s₁.2, s₂.2]⟩, ?_, ?_⟩
      · exact Set.union_subset_union_right _ (Set.image_mono (by simp))
      · exact Set.union_subset_union_right _ (Set.image_mono (by simp))
    have hsatS : ∀ s : Sub, (S s).IsSatisfiable := by
      intro s
      obtain ⟨N⟩ := hfin s.1 s.2
      have hNT : N ⊨ T := N.is_model.mono (Set.subset_insert _ _)
      obtain ⟨a, ha⟩ := (realize_exs_iff _).1
        (N.is_model.realize_of_mem _ (Set.mem_insert _ _))
      let : (constantsOn (Fin n)).Structure N := constantsOn.structure a
      let := hNT
      have hNS : N ⊨ S s := by
        refine model_union_iff.2 ⟨(g.onTheory_model T).2 hNT, (model_iff _).2 ?_⟩
        rintro _ ⟨ψ, hψ, rfl⟩
        exact (realize_evalAtConstants_iff a ψ).2 (BoundedFormula.realize_iInf.1 ha ⟨ψ, hψ⟩)
      let := hNS
      exact Model.isSatisfiable N
    have hu : (⋃ s : Sub, S s) = g.onTheory T ∪ evalAtConstants '' p := by
      ext σ
      simp only [S, Set.mem_iUnion, Set.mem_union, Set.mem_image, Finset.mem_coe]
      refine ⟨?_, ?_⟩
      · rintro ⟨s, hT | ⟨ψ, hψ, rfl⟩⟩
        · exact Or.inl hT
        · exact Or.inr ⟨ψ, s.2 hψ, rfl⟩
      · rintro (hT | ⟨ψ, hψ, rfl⟩)
        · exact ⟨⟨∅, by simp⟩, Or.inl hT⟩
        · exact ⟨⟨{ψ}, by simp [hψ]⟩, Or.inr ⟨ψ, Finset.mem_singleton_self ψ, rfl⟩⟩
    obtain ⟨M⟩ := (hu ▸ (isSatisfiable_directed_union_iff hdir).2 hsatS)
    let : L.Structure M := g.reduct M
    have hMT : M ⊨ T := (g.onTheory_model T).1 (M.is_model.mono Set.subset_union_left)
    have hMp : M ⊨ evalAtConstants '' p := M.is_model.mono Set.subset_union_right
    let := hMT
    refine ⟨ModelType.of T M, fun i => (L.con i : M), fun ψ hψ => ?_⟩
    have heq := withConstantsStructure_reduct_eq (L := L) (γ := Fin n) M
    exact (realize_evalAtConstants_iff (fun i => (L.con i : M)) ψ).1
      (heq.symm ▸ hMp.realize_of_mem _ ⟨ψ, hψ, rfl⟩)

/-- A **finite** first-order partial type realized in any nonempty model `M` of `T` (in any
universe `w`) is isolated modulo `T` by the conjunction of its members. -/
theorem exists_isolating_of_finite_of_realize {T : L.Theory} {M : Type w} [L.Structure M]
    [Nonempty M] [M ⊨ T] {n : ℕ} {p : Set (L.BoundedFormula Empty n)} (hp : p.Finite)
    {a : Fin n → M} (ha : ∀ ψ ∈ p, ψ.Realize Empty.elim a) :
    ∃ φ : L.BoundedFormula Empty n,
      (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls := by
  have := hp.fintype
  refine ⟨BoundedFormula.iInf fun ψ : p => ψ.1, ?_, fun ψ hψ => ?_⟩
  · have hM : M ⊨ insert (BoundedFormula.iInf fun ψ : p => ψ.1).exs T := by
      refine model_insert_iff.2 ⟨(realize_exs_iff _).2 ?_, inferInstance⟩
      exact ⟨a, BoundedFormula.realize_iInf.2 fun q => ha q.1 q.2⟩
    let := hM
    exact Model.isSatisfiable M
  · refine models_sentence_iff.2 fun N => (Sentence.realize_alls _).2 fun b => ?_
    exact BoundedFormula.realize_imp.2 fun hb => BoundedFormula.realize_iInf.1 hb ⟨ψ, hψ⟩

/-- A **finite** first-order partial type is isolated modulo `T` if and only if it is realized in
some nonempty model of `T`: the conjunction of its members is itself a single first-order
formula. -/
theorem exists_isolating_iff_of_finite {T : L.Theory} {n : ℕ}
    {p : Set (L.BoundedFormula Empty n)} (hp : p.Finite) :
    (∃ φ : L.BoundedFormula Empty n,
        (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls) ↔
      ∃ M : ModelType.{u, v, max u v} T, ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a :=
  ⟨fun ⟨_, hsat, himp⟩ => exists_modelType_realize_of_isolating hsat himp,
    fun ⟨_, _, ha⟩ => exists_isolating_of_finite_of_realize hp ha⟩

/-- Over a language with countably many function and relation symbols, a first-order partial type
realized in every countable nonempty model of a satisfiable first-order theory `T` (tested in any
one universe `w`) is isolated by a first-order formula modulo `T`. -/
theorem exists_isolating_of_realized_in_every_countable_model [Countable (Σ l, L.Functions l)]
    [Countable (Σ l, L.Relations l)] {T : L.Theory} (hT : T.IsSatisfiable)
    {n : ℕ} {p : Set (L.BoundedFormula Empty n)}
    (h : ∀ (M : Type w) [L.Structure M] [Countable M] [Nonempty M] [M ⊨ T],
      ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a) :
    ∃ φ : L.BoundedFormula Empty n,
      (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls := by
  by_contra hnp
  obtain ⟨M, _, _, _, hMT, hMo⟩ := exists_countable_model_omitting.{u, v, w} hT
    (fun _ : Unit => p) (fun _ => hnp)
  let := hMT
  obtain ⟨a, ha⟩ := h M
  obtain ⟨ψ, hψ, hψa⟩ := hMo () a
  exact hψa (ha ψ hψ)

/-- Over a complete first-order theory `T`, any partial type isolated by a first-order formula `φ`
modulo `T` is realized in every nonempty model of `T`, of any cardinality and in any universe, with
no countability hypothesis on the language. -/
theorem IsComplete.exists_realize_of_isolating {T : L.Theory} (hT : T.IsComplete)
    {n : ℕ} {p : Set (L.BoundedFormula Empty n)} {φ : L.BoundedFormula Empty n}
    (hsat : (insert φ.exs T).IsSatisfiable) (himp : ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls)
    (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T] :
    ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a := by
  have hφT : T ⊨ᵇ φ.exs := (hT.2 φ.exs).resolve_right fun hnot => by
    obtain ⟨N⟩ := hsat
    have hNT : N ⊨ T := N.is_model.mono (Set.subset_insert _ _)
    let := hNT
    exact (Sentence.realize_not N).1 (hnot.realize_sentence N)
      (N.is_model.realize_of_mem _ (Set.mem_insert _ _))
  obtain ⟨a, ha⟩ := (realize_exs_iff φ).1 (hφT.realize_sentence M)
  refine ⟨a, fun ψ hψ => ?_⟩
  have hψM := (Sentence.realize_alls (φ.imp ψ)).1 ((himp ψ hψ).realize_sentence M) a
  exact BoundedFormula.realize_imp.1 hψM ha

/-- Over a complete first-order theory `T` in a language with countably many function and relation
symbols, a partial type is isolated by a first-order formula modulo `T` if and only if it is
realized in every countable nonempty model of `T` in a given universe `w`. -/
theorem IsComplete.exists_isolating_iff_realized_in_every_countable_model
    [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    {T : L.Theory} (hT : T.IsComplete) {n : ℕ} {p : Set (L.BoundedFormula Empty n)} :
    (∃ φ : L.BoundedFormula Empty n,
        (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls) ↔
      ∀ (M : Type w) [L.Structure M] [Countable M] [Nonempty M] [M ⊨ T],
        ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a :=
  ⟨fun ⟨_, hsat, himp⟩ M _ _ _ _ => hT.exists_realize_of_isolating hsat himp M,
    exists_isolating_of_realized_in_every_countable_model hT.1⟩

end Theory

end FirstOrder.Language
