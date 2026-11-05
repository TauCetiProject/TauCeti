/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.CountableModel
public import TauCeti.ModelTheory.ModelExistence.Types

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

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 4
  (isolation over a theory in a fragment and the omitting types theorem).
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

end Theoryω

end Language

end FirstOrder
