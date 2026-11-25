/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FirstOrderImage
public import TauCeti.ModelTheory.ModelExistence.CountableModel
public import TauCeti.ModelTheory.ModelExistence.Types
import TauCeti.ModelTheory.Semantics

/-!
# Isolation of partial types over an `L_{ω₁ω}` theory

A partial type `p`, a set of formulas with `n` bound positions and no free variables, is
**isolated over a theory `T` in a fragment `A`** when some member `φ` of `A` with `n` bound
positions is consistent with `T` and implies every formula of `p` modulo `T`: the theory `T`
together with `φ.exs` is satisfiable, and `T` entails `(φ.imp ψ).alls` for every `ψ ∈ p`, where
`exs` and `alls` quantify the `n` bound positions.

Non-isolation is the hypothesis of the omitting types theorem, by which a satisfiable theory in a
countable formation-closed fragment has a countable model omitting countably many partial types
none of which is isolated. An isolated type, on the other hand, is realized in some countable
model of a countable theory, and in every structure whose `L_{ω₁ω}` theory the theory entails.
Conversely, in a structure realizing only countably many complete `n`-types, each realized complete
type is isolated over the theory of the structure.

In the first-order image fragment, isolation reduces to isolation by a first-order formula modulo a
first-order theory (`Theoryω.isolatesIn_firstOrder_iff`). Directly at the first-order level, any
partial type isolated modulo a theory is realized in some nonempty model, and in every nonempty
model when the theory is complete; for finite first-order partial types, isolation modulo a theory
coincides with realization in some nonempty model.

## Main definitions

* `FirstOrder.Language.Theoryω.IsolatesIn`: a partial type is isolated over a theory in a
  fragment.

## Main results

* `FirstOrder.Language.Theoryω.IsolatesIn.mono` and `FirstOrder.Language.Theoryω.IsolatesIn.subset`:
  isolation passes to larger fragments and to smaller partial types.
* `FirstOrder.Language.Theoryω.IsolatesIn.exists_model_not_omitsType` and
  `FirstOrder.Language.Theoryω.IsolatesIn.exists_countable_model_not_omitsType`: an isolated type
  is realized in some nonempty model of the theory, a countable one in any universe when the theory
  is countable.
* `FirstOrder.Language.Theoryω.IsolatesIn.not_omitsType`: a structure realizes every partial type
  isolated over a theory that entails every sentence true in the structure.
* `FirstOrder.Language.Theoryω.isolatesIn_top_infinitaryType`: if a structure realizes only
  countably many complete `n`-types, the complete type of each of its `n`-tuples is isolated over
  its `L_{ω₁ω}` theory.
* `FirstOrder.Language.Theoryω.isolatesIn_firstOrder_iff`: in the first-order image fragment,
  isolation of a first-order partial type over a first-order theory is isolation by a first-order
  formula in the sense of Mathlib's `Theory.IsSatisfiable` and `Theory.ModelsBoundedFormula`.
* `FirstOrder.Language.Theory.realize_of_isolating`,
  `FirstOrder.Language.Theory.exists_modelType_realize_of_isolating`, and
  `FirstOrder.Language.Theory.IsComplete.exists_realize_of_isolating`: any tuple in a nonempty model
  realizing an isolating formula realizes the partial type, so a first-order partial type isolated
  modulo a theory is realized in some nonempty model, and in every nonempty model when the theory is
  complete.
* `FirstOrder.Language.Theory.exists_isolating_of_finite_of_realize` and
  `FirstOrder.Language.Theory.exists_isolating_iff_of_finite`: a finite first-order partial type is
  isolated modulo a theory if and only if it is realized in some nonempty model.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 4
  (isolation over a theory in a fragment and the omitting types theorem).
* D. Marker, *Model Theory: An Introduction*, Springer, 2002, Section 4.2.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
-/

public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

namespace Theoryω

variable {A B : L.Fragment} {T : L.Theoryω} {n : ℕ} {p q : Set (L.BoundedFormulaω Empty n)}

/-- A partial type `p` in `n` bound positions is **isolated over the theory `T` in the fragment
`A`** when some member `φ` of `A` with `n` bound positions is consistent with `T`, in that `T`
together with `φ.exs` is satisfiable, and implies every formula of `p` modulo `T`: `T` entails
`(φ.imp ψ).alls` for every `ψ ∈ p`. Here `exs` and `alls` quantify the `n` bound positions. -/
def IsolatesIn (A : L.Fragment) (T : L.Theoryω) (p : Set (L.BoundedFormulaω Empty n)) : Prop :=
  ∃ φ : L.BoundedFormulaω Empty n, (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
    (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T.Entails (φ.imp ψ).alls

/-- Unfolding lemma for `Theoryω.IsolatesIn`. -/
theorem isolatesIn_iff :
    IsolatesIn A T p ↔ ∃ φ : L.BoundedFormulaω Empty n,
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧ (insert φ.exs T).IsSatisfiable ∧
        ∀ ψ ∈ p, T.Entails (φ.imp ψ).alls :=
  Iff.rfl

/-- Isolation in a fragment is isolation in every larger fragment. -/
theorem IsolatesIn.mono (h : IsolatesIn A T p) (hAB : A ≤ B) : IsolatesIn B T p :=
  let ⟨φ, hφ, hs, hp⟩ := h
  ⟨φ, hAB hφ, hs, hp⟩

/-- A formula isolating a partial type isolates each of its subsets. -/
theorem IsolatesIn.subset (h : IsolatesIn A T p) (hqp : q ⊆ p) : IsolatesIn A T q :=
  let ⟨φ, hφ, hs, hp⟩ := h
  ⟨φ, hφ, hs, fun ψ hψ => hp ψ (hqp hψ)⟩

/-- Only a satisfiable theory isolates a partial type. -/
theorem IsolatesIn.isSatisfiable (h : IsolatesIn A T p) : T.IsSatisfiable :=
  let ⟨_, _, hs, _⟩ := h
  hs.mono (Set.subset_insert _ _)

/-- **Isolated types are realized.** A partial type isolated over `T` is realized in some nonempty
model of `T` in the universe `max u v`. -/
theorem IsolatesIn.exists_model_not_omitsType (h : IsolatesIn A T p) :
    ∃ (M : Type (max u v)) (_ : L.Structure M), Nonempty M ∧ T.Model M ∧ ¬OmitsType M p := by
  obtain ⟨φ, -, hs, hp⟩ := h
  obtain ⟨M, _, hM, hMφ⟩ := isSatisfiable_iff.1 hs
  have := hM
  rw [model_insert_iff] at hMφ
  exact ⟨M, _, hM, hMφ.2,
    not_omitsType_of_realize hMφ.1 fun ψ hψ => (hp ψ hψ).realize_of_small M hMφ.2⟩

/-- **Isolated types are realized in countable models.** A partial type isolated over a countable
theory `T` is realized in some countable nonempty model of `T`, in every universe `w`. -/
theorem IsolatesIn.exists_countable_model_not_omitsType (hT : T.Countable)
    (h : IsolatesIn A T p) :
    ∃ (M : Type w) (_ : L.Structure M), Countable M ∧ Nonempty M ∧ T.Model M ∧
      ¬OmitsType M p := by
  obtain ⟨φ, -, hs, hp⟩ := h
  obtain ⟨M, _, hMc, hM, hMφ⟩ := exists_countable_model.{u, v, w} (hT.insert φ.exs) hs
  rw [model_insert_iff] at hMφ
  exact ⟨M, _, hMc, hM, hMφ.2,
    not_omitsType_of_realize hMφ.1 fun ψ hψ => (hp ψ hψ).realize hT M hMφ.2⟩

/-- **Isolated types are realized in structures whose theory `T` entails.** If `T` entails every
sentence true in `N`, for instance when `T` is the `L_{ω₁ω}` theory of `N`, then `N` realizes every
partial type isolated over `T`. The structure `N` may be empty and of any cardinality, in any
universe. -/
theorem IsolatesIn.not_omitsType {N : Type w} [L.Structure N] (h : IsolatesIn A T p)
    (hN : ∀ σ : L.Sentenceω, SentenceInf.Realize σ N → T.Entails σ) : ¬OmitsType N p := by
  obtain ⟨φ, -, hs, hp⟩ := h
  obtain ⟨M, _, hM, hMφ⟩ := isSatisfiable_iff.1 hs
  have := hM
  rw [model_insert_iff] at hMφ
  -- every sentence true in the model `M` of `T` is true in `N`
  have hMN (σ : L.Sentenceω) (hσ : SentenceInf.Realize σ M) : SentenceInf.Realize σ N := by
    by_contra hσN
    exact SentenceInf.realize_not.1
      ((hN σ.not (SentenceInf.realize_not.2 hσN)).realize_of_small M hMφ.2) hσ
  exact not_omitsType_of_realize (hMN _ hMφ.1) fun ψ hψ =>
    hMN _ ((hp ψ hψ).realize_of_small M hMφ.2)

/-- **Realized types are isolated over the theory of the structure.** If a nonempty structure `M`,
small in the universe `max u v`, realizes only countably many complete `n`-types, then the complete
type of each `n`-tuple of `M` is isolated over the `L_{ω₁ω}` theory of `M` in the fragment of all
formulas. -/
theorem isolatesIn_top_infinitaryType {M : Type w} [L.Structure M] [Nonempty M]
    [Small.{max u v} M] (h : (realizedTypes (L := L) M n).Countable) (a : Fin n → M) :
    IsolatesIn ⊤ {σ : L.Sentenceω | SentenceInf.Realize σ M} (infinitaryType M a) := by
  obtain ⟨χ, hχ⟩ := exists_isolatingFormula h a
  refine ⟨χ, Fragment.mem_top _, Model.isSatisfiable (M := M) ?_, fun ψ hψ => entails_of_mem ?_⟩
  · refine model_insert_iff.2 ⟨?_, model_iff.2 fun _ hσ => hσ⟩
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_exs]
    exact ⟨a, (hχ a).2 rfl⟩
  · simp only [Set.mem_ofPred_eq, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_imp]
    intro b hb
    rw [← mem_infinitaryType, (hχ b).1 hb]
    exact hψ

/-- **Isolation in the first-order image.** A first-order partial type is isolated over a
first-order theory in the first-order image fragment exactly when some first-order formula `φ`
isolates it modulo the theory in Mathlib's sense: the theory together with the existential closure
of `φ` is satisfiable, and the theory models the universal closure of `φ → ψ` for every `ψ` in the
type. -/
theorem isolatesIn_firstOrder_iff {T : L.Theory} {p : Set (L.BoundedFormula Empty n)} :
    IsolatesIn (Fragment.firstOrder L) (BoundedFormula.toOmega '' T)
        (BoundedFormula.toOmega '' p) ↔
      ∃ φ : L.BoundedFormula Empty n,
        (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls := by
  simp only [isolatesIn_iff, Set.forall_mem_image]
  constructor
  · rintro ⟨_, hφ, hsat, hent⟩
    obtain ⟨φ, rfl⟩ := Fragment.mem_firstOrder_iff.1 hφ
    refine ⟨φ, ?_, fun ψ hψ => ?_⟩
    · rw [← isSatisfiable_image_toOmega_iff, Set.image_insert_eq]
      simpa only [BoundedFormula.toInf_exs] using hsat
    · rw [← entails_image_toOmega_iff]
      simpa only [BoundedFormula.toInf_alls, BoundedFormula.toInf_imp] using hent hψ
  · rintro ⟨φ, hsat, hent⟩
    refine ⟨φ.toOmega, Fragment.toOmega_mem_firstOrder φ, ?_, fun ψ hψ => ?_⟩
    · rw [← isSatisfiable_image_toOmega_iff, Set.image_insert_eq] at hsat
      simpa only [BoundedFormula.toInf_exs] using hsat
    · have h := entails_image_toOmega_iff.2 (hent ψ hψ)
      simpa only [BoundedFormula.toInf_alls, BoundedFormula.toInf_imp] using h

end Theoryω

namespace Theory

/-- If `T` entails `(φ.imp ψ).alls` for every `ψ ∈ p`, then any tuple in a nonempty model of `T`
realizing `φ` realizes every formula of `p`. -/
theorem realize_of_isolating {T : L.Theory} {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]
    {n : ℕ} {p : Set (L.BoundedFormula Empty n)} {φ : L.BoundedFormula Empty n} {a : Fin n → M}
    (ha : φ.Realize Empty.elim a) (himp : ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls) :
    ∀ ψ ∈ p, ψ.Realize Empty.elim a := fun ψ hψ =>
  BoundedFormula.realize_imp.1
    ((Sentence.realize_alls (φ.imp ψ)).1 ((himp ψ hψ).realize_sentence M) a) ha

/-- A partial type isolated by a first-order formula `φ` modulo `T` is realized in some nonempty
model of `T`. -/
theorem exists_modelType_realize_of_isolating {T : L.Theory} {n : ℕ}
    {p : Set (L.BoundedFormula Empty n)} {φ : L.BoundedFormula Empty n}
    (hsat : (insert φ.exs T).IsSatisfiable) (himp : ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls) :
    ∃ M : ModelType.{u, v, max u v} T, ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a := by
  obtain ⟨M⟩ := hsat
  have hMT : M ⊨ T := M.is_model.mono (Set.subset_insert _ _)
  obtain ⟨a, ha⟩ := (Sentence.realize_exs φ).1 (M.is_model.realize_of_mem _ (Set.mem_insert _ _))
  let := hMT
  exact ⟨ModelType.of T M, a, realize_of_isolating ha himp⟩

/-- A **finite** first-order partial type realized in any nonempty model `M` of `T` (in any
universe `w`) is isolated by a first-order formula modulo `T`. -/
theorem exists_isolating_of_finite_of_realize {T : L.Theory} {M : Type w} [L.Structure M]
    [Nonempty M] [M ⊨ T] {n : ℕ} {p : Set (L.BoundedFormula Empty n)} (hp : p.Finite)
    {a : Fin n → M} (ha : ∀ ψ ∈ p, ψ.Realize Empty.elim a) :
    ∃ φ : L.BoundedFormula Empty n,
      (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls := by
  have := hp.fintype
  refine ⟨BoundedFormula.iInf fun ψ : p => ψ.val, ?_, fun ψ hψ => ?_⟩
  · have hM : M ⊨ insert (BoundedFormula.iInf fun ψ : p => ψ.val).exs T :=
      model_insert_iff.2 ⟨(Sentence.realize_exs _).2
        ⟨a, BoundedFormula.realize_iInf.2 fun q => ha q.val q.property⟩, inferInstance⟩
    let := hM
    exact Model.isSatisfiable M
  · refine models_sentence_iff.2 fun N => (Sentence.realize_alls _).2 fun b => ?_
    exact BoundedFormula.realize_imp.2 fun hb => BoundedFormula.realize_iInf.1 hb ⟨ψ, hψ⟩

/-- A **finite** first-order partial type is isolated by a first-order formula modulo `T` if and
only if it is realized in some nonempty model of `T`. -/
theorem exists_isolating_iff_of_finite {T : L.Theory} {n : ℕ}
    {p : Set (L.BoundedFormula Empty n)} (hp : p.Finite) :
    (∃ φ : L.BoundedFormula Empty n,
        (insert φ.exs T).IsSatisfiable ∧ ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls) ↔
      ∃ M : ModelType.{u, v, max u v} T, ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a :=
  ⟨fun ⟨_, hsat, himp⟩ => exists_modelType_realize_of_isolating hsat himp,
    fun ⟨_, _, ha⟩ => exists_isolating_of_finite_of_realize hp ha⟩

/-- Over a complete first-order theory `T`, any partial type isolated by a first-order formula `φ`
modulo `T` is realized in every nonempty model of `T`, of any cardinality and in any universe, with
no countability hypothesis on the language. -/
theorem IsComplete.exists_realize_of_isolating {T : L.Theory} (hT : T.IsComplete)
    {n : ℕ} {p : Set (L.BoundedFormula Empty n)} {φ : L.BoundedFormula Empty n}
    (hsat : (insert φ.exs T).IsSatisfiable) (himp : ∀ ψ ∈ p, T ⊨ᵇ (φ.imp ψ).alls)
    (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T] :
    ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a := by
  obtain ⟨N⟩ := hsat
  have : N ⊨ T := N.is_model.mono (Set.subset_insert _ _)
  have hφT : T ⊨ᵇ φ.exs :=
    (hT.realize_sentence_iff φ.exs N).1 (N.is_model.realize_of_mem _ (Set.mem_insert _ _))
  obtain ⟨a, ha⟩ := (Sentence.realize_exs φ).1 (hφT.realize_sentence M)
  exact ⟨a, realize_of_isolating ha himp⟩

end Theory

end Language

end FirstOrder
