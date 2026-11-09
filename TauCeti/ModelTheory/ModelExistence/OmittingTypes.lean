/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FiniteInstances
public import TauCeti.ModelTheory.ModelExistence.Isolation
public import TauCeti.ModelTheory.ModelExistence.ModelExistence

/-!
# Omitting types in countable fragments

A satisfiable theory of sentences in a countable formation-closed fragment has a countable
nonempty model omitting any countable family of partial types in the fragment, provided none
is isolated over the theory in that fragment. The model may be constructed in any universe.
Consequently a partial type realized in every countable nonempty model is isolated.
Over a language with countably many symbols, applying the theorem to the first-order image
fragment gives the first-order omitting types theorem, for a first-order theory satisfiable in the
sense of Mathlib's `Theory.IsSatisfiable` and first-order partial types not isolated by a
first-order formula modulo the theory.

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

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 4.
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

end Theory

end FirstOrder.Language
