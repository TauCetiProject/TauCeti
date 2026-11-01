/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.Enumeration
public import TauCeti.ModelTheory.ModelExistence.TermModel

/-!
# The model existence theorem for `L_{ω₁ω}`

Let `L` have countably many function and relation symbols. The **model existence theorem**
(`ConsistencyProperty.model_existence`) says that every countable member `s` of a consistency
property `C` over `L` has a countable model, in any universe, in which every element is the
interpretation of a Henkin constant. The model is the term model of the limit of a fair
enumeration of `C` starting from `s`: that limit is Henkin complete
(`ConsistencyProperty.henkinComplete_limit`) and contains neither `⊥` nor a sentence together with
its negation, so the truth lemma applies to it.

The model can moreover be made to omit countably many countable partial types `p i`
(`ConsistencyProperty.model_existence_omitting`), provided `C` lets each of them be refuted at
every tuple of Henkin constants: for every member `t` of `C` and every tuple `c`, some `ψ ∈ p i`
has `t + ¬ψ[c]` in `C`.

These theorems are the engine of the model-producing constructions of infinitary model theory:
the omitting types theorem for countable fragments, and the interpolation and well-ordering
theorems, each of which supplies a consistency property tailored to the model it needs.

## Main results

* `FirstOrder.Language.ConsistencyProperty.henkinComplete_limit`: the limit of a fair enumeration
  of a consistency property is Henkin complete.
* `FirstOrder.Language.ConsistencyProperty.model_existence`: a countable member of a consistency
  property over a countable language has a countable model in which every element is named by a
  Henkin constant.
* `FirstOrder.Language.ConsistencyProperty.model_existence_omitting`: the model can also be made
  to omit countably many countable partial types that the consistency property refutes at every
  tuple.

## Implementation notes

Omission is obtained without changing the enumeration: every member of `C`, and in particular
`s`, is enlarged by the countable disjunctions `⋁_{ψ ∈ p i} ¬ψ[c]`. The enlarged sets again form a
consistency property, since every member can decide each adjoined disjunction by the hypothesis,
and none contains the negation of one: adding the chosen refutation `¬ψ[c]` and then the negated
disjunct `¬¬ψ[c]` would produce a contradiction. A model of the enlarged starting set in which
every element is named refutes some member of `p i` at every tuple.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.1.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
-/

public section

universe u v w

namespace FirstOrder

namespace Language

open BoundedFormulaInf

namespace ConsistencyProperty

variable {L : Language.{u, v}} {C : ConsistencyProperty L} {s : L[[ℕ]].Theoryω}

/-- **The limit of a fair enumeration is Henkin complete.** If `s` is a member of `C`, the
sequence `e` enumerates `s` and the schedule `q` is surjective, then the limit of the enumeration
contains the target of every clause of `C` whose trigger it contains. -/
theorem henkinComplete_limit {e : ℕ → L[[ℕ]].Sentenceω} {q : ℕ → Request L} (hs : s ∈ C.sets)
    (he : s ⊆ Set.range e) (hq : Function.Surjective q) : HenkinComplete (C.limit s e q) where
  imp _ _ := limit_imp hs he hq
  not_imp _ _ := limit_not_imp hs he hq
  iInf _ := limit_iInf hs he hq
  not_iInf _ := limit_not_iInf hs he hq
  iSup _ := limit_iSup hs he hq
  not_iSup _ := limit_not_iSup hs he hq
  all _ := limit_all hs he hq
  not_all _ := limit_not_all hs he hq
  eq_refl := limit_eq_refl hs hq
  eq_subst _ _ _ := limit_eq_subst hs he hq
  eq_name := limit_eq_name hs hq

/-- **The model existence theorem.** Over a language with countably many function and relation
symbols, every countable member `s` of a consistency property has a countable model, in any
universe `w`, in which every element is the interpretation of a Henkin constant. -/
theorem model_existence [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (hs : s ∈ C.sets) (hsc : s.Countable) :
    ∃ (M : Type w) (_ : L[[ℕ]].Structure M), Countable M ∧ s.Model M ∧
      Function.Surjective fun c : ℕ => (L.con c : M) := by
  obtain ⟨e, he⟩ := Set.countable_iff_exists_subset_range.1 hsc
  obtain ⟨q, hq⟩ := exists_surjective_nat (Request L)
  have hS := henkinComplete_limit hs he hq
  -- move the term model of the limit into the universe `w`
  let f : hS.TermModel ≃ ULift.{w} hS.TermModel := Equiv.ulift.symm
  let : L[[ℕ]].Structure (ULift.{w} hS.TermModel) := f.inducedStructure
  have hcon (c : ℕ) : f (L.con c) = L.con c :=
    HomClass.map_constants f.inducedStructureEquiv _
  refine ⟨ULift.{w} hS.TermModel, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← StrongHomClass.theoryω_model_iff f.inducedStructureEquiv]
    exact (hS.model (bot_notMem_limit hs) fun _ => not_notMem_limit hs).mono subset_limit
  · simpa only [Function.comp_def, hcon] using f.surjective.comp hS.con_surjective

/-! ### Omitting types -/

section adjoin

variable {D : L[[ℕ]].Theoryω}

/-- A sentence that is not a countable disjunction lies in `t ∪ D` only if it lies in `t`, when
`D` consists of countable disjunctions. -/
private theorem mem_of_mem_union {P : (ℕ → L[[ℕ]].Sentenceω) → Prop}
    (hD : ∀ φ ∈ D, ∃ φs : ℕ → L[[ℕ]].Sentenceω, φ = BoundedFormulaInf.iSup φs ∧ P φs)
    {t : L[[ℕ]].Theoryω} {φ : L[[ℕ]].Sentenceω} (h : φ ∈ t ∪ D)
    (hφ : ∀ φs, φ ≠ BoundedFormulaInf.iSup φs) :
    φ ∈ t :=
  h.resolve_right fun h => (hD φ h).elim fun φs h' => hφ φs h'.1

/-- The consistency property obtained by adjoining to every member of `C` a set `D` of countable
disjunctions, each of which every member of `C` can extend by one of its disjuncts. -/
private def adjoin (C : ConsistencyProperty L) (D : L[[ℕ]].Theoryω)
    (hD : ∀ φ ∈ D, ∃ φs : ℕ → L[[ℕ]].Sentenceω, φ = BoundedFormulaInf.iSup φs ∧
      ∀ t ∈ C.sets, ∃ k, insert (φs k) t ∈ C.sets) : ConsistencyProperty L where
  sets := (· ∪ D) '' C.sets
  no_falsum := by
    rintro _ ⟨t, ht, rfl⟩ h
    exact C.no_falsum t ht (mem_of_mem_union hD h fun _ => nofun)
  no_contradiction := by
    rintro _ ⟨t, ht, rfl⟩ φ hφ hnφ
    have hnφ := mem_of_mem_union hD hnφ fun _ => nofun
    rcases hφ with hφ | hφ
    · exact C.no_contradiction t ht φ hφ hnφ
    -- a member containing `¬⋁ φs` would accept a disjunct `φs k` and then also `¬φs k`
    · obtain ⟨φs, rfl, hφs⟩ := hD φ hφ
      obtain ⟨k, hk⟩ := hφs t ht
      exact C.no_contradiction _ (C.not_iSup _ hk φs (Set.mem_insert_of_mem _ hnφ) k) (φs k)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert _ _)
  imp := by
    rintro _ ⟨t, ht, rfl⟩ φ ψ h
    exact (C.imp t ht φ ψ (mem_of_mem_union hD h fun _ => nofun)).imp
      (⟨_, ·, Set.insert_union⟩) (⟨_, ·, Set.insert_union⟩)
  not_imp := by
    rintro _ ⟨t, ht, rfl⟩ φ ψ h
    exact (C.not_imp t ht φ ψ (mem_of_mem_union hD h fun _ => nofun)).imp
      (⟨_, ·, Set.insert_union⟩) (⟨_, ·, Set.insert_union⟩)
  iInf := by
    rintro _ ⟨t, ht, rfl⟩ φs h k
    exact ⟨_, C.iInf t ht φs (mem_of_mem_union hD h fun _ => nofun) k, Set.insert_union⟩
  not_iInf := by
    rintro _ ⟨t, ht, rfl⟩ φs h
    exact (C.not_iInf t ht φs (mem_of_mem_union hD h fun _ => nofun)).imp
      fun _ hk => ⟨_, hk, Set.insert_union⟩
  iSup := by
    rintro _ ⟨t, ht, rfl⟩ φs h
    rcases h with h | h
    · exact (C.iSup t ht φs h).imp fun _ hk => ⟨_, hk, Set.insert_union⟩
    · obtain ⟨φs', hφs, hφs'⟩ := hD _ h
      cases hφs
      exact (hφs' t ht).imp fun _ hk => ⟨_, hk, Set.insert_union⟩
  not_iSup := by
    rintro _ ⟨t, ht, rfl⟩ φs h k
    exact ⟨_, C.not_iSup t ht φs (mem_of_mem_union hD h fun _ => nofun) k, Set.insert_union⟩
  all := by
    rintro _ ⟨t, ht, rfl⟩ φ h c
    exact ⟨_, C.all t ht φ (mem_of_mem_union hD h fun _ => nofun) c, Set.insert_union⟩
  not_all := by
    rintro _ ⟨t, ht, rfl⟩ φ h
    exact (C.not_all t ht φ (mem_of_mem_union hD h fun _ => nofun)).imp
      fun _ hc => ⟨_, hc, Set.insert_union⟩
  eq_refl := by
    rintro _ ⟨t, ht, rfl⟩ u
    exact ⟨_, C.eq_refl t ht u, Set.insert_union⟩
  eq_subst := by
    rintro _ ⟨t, ht, rfl⟩ u u' φ hφ hu h
    refine ⟨_, C.eq_subst t ht u u' φ hφ (mem_of_mem_union hD hu fun _ => nofun)
      (mem_of_mem_union hD h fun φs h' => ?_), Set.insert_union⟩
    -- an instance of an atomic formula is atomic, hence not a disjunction
    have hat := hφ.substBounds fun _ => u
    rw [← inst_def, h'] at hat
    nomatch hat
  eq_name := by
    rintro _ ⟨t, ht, rfl⟩ u
    exact (C.eq_name t ht u).imp fun _ hc => ⟨_, hc, Set.insert_union⟩

end adjoin

/-- **The model existence theorem with omitted types.** Over a language with countably many
function and relation symbols, let `p i` be countably many countable partial types such that
every member `t` of the consistency property `C` and every tuple `c` of Henkin constants admit
some `ψ ∈ p i` for which `t` together with the refutation `¬ψ[c]` is again a member. Then every
countable member `s` of `C` has a countable model, in any universe `w`, in which every element
is the interpretation of a Henkin constant and which omits every `p i`. -/
theorem model_existence_omitting [Countable (Σ l, L.Functions l)]
    [Countable (Σ l, L.Relations l)] {ι : Type*} [Countable ι] {n : ι → ℕ}
    (p : ∀ i, Set (L[[ℕ]].BoundedFormulaω Empty (n i))) (hp : ∀ i, (p i).Countable)
    (hC : ∀ i, ∀ t ∈ C.sets, ∀ c : Fin (n i) → ℕ, ∃ ψ ∈ p i,
      insert (substBounds (fun j => (L.con (c j)).term) ψ).not t ∈ C.sets)
    (hs : s ∈ C.sets) (hsc : s.Countable) :
    ∃ (M : Type w) (_ : L[[ℕ]].Structure M), Countable M ∧ s.Model M ∧
      (Function.Surjective fun c : ℕ => (L.con c : M)) ∧ ∀ i, OmitsType M (p i) := by
  -- enumerate each type, which is nonempty since `s` refutes it at some tuple
  have hne (i : ι) : (p i).Nonempty :=
    let ⟨ψ, hψ, _⟩ := hC i s hs fun _ => 0
    ⟨ψ, hψ⟩
  choose f hf using fun i => (hp i).exists_eq_range (hne i)
  -- the disjunction refuting `p i` at the tuple `c` of Henkin constants
  let δ : (Σ i, Fin (n i) → ℕ) → L[[ℕ]].Sentenceω := fun x =>
    BoundedFormulaInf.iSup fun k => (substBounds (fun j => (L.con (x.2 j)).term) (f x.1 k)).not
  have hD : ∀ φ ∈ Set.range δ, ∃ φs : ℕ → L[[ℕ]].Sentenceω, φ = BoundedFormulaInf.iSup φs ∧
      ∀ t ∈ C.sets, ∃ k, insert (φs k) t ∈ C.sets := by
    rintro _ ⟨⟨i, c⟩, rfl⟩
    refine ⟨_, rfl, fun t ht => ?_⟩
    obtain ⟨ψ, hψ, h⟩ := hC i t ht c
    rw [hf i] at hψ
    obtain ⟨k, rfl⟩ := hψ
    exact ⟨k, h⟩
  obtain ⟨M, _, hMc, hM, hsurj⟩ := (C.adjoin (Set.range δ) hD).model_existence.{u, v, w}
    (s := s ∪ Set.range δ) ⟨s, hs, rfl⟩ (hsc.union (Set.countable_range δ))
  refine ⟨M, inferInstance, hMc, hM.mono Set.subset_union_left, hsurj,
    fun i => omitsType_iff.2 fun a => ?_⟩
  -- name the tuple by Henkin constants and read off the refuting disjunction
  choose c hc using fun j => hsurj (a j)
  have h := hM.realize_of_mem (Set.mem_union_right s ⟨⟨i, c⟩, rfl⟩)
  simp only [δ, SentenceInf.realize_def, FormulaInf.realize_def, realize_iSup, realize_not,
    realize_substBounds, Term.realize_constants, hc] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨f i k, hf i ▸ ⟨k, rfl⟩, hk⟩

end ConsistencyProperty

end Language

end FirstOrder
