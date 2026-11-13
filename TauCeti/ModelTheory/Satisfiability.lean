/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Satisfiability
import TauCeti.ModelTheory.LanguageMap

/-!
# Semantic entailment and completeness of first-order theories along language maps

Additions to Mathlib's `Mathlib.ModelTheory.Satisfiability` describing how semantic entailment
(`T ⊨ᵇ φ`), satisfiability, and completeness (`Theory.IsComplete`) of first-order theories behave
under language homomorphisms and language equivalences, across arbitrary language universes.

Every language homomorphism `g : L →ᴸ L'` preserves semantic entailment of sentences, because a
model of `g.onTheory T ∪ {(g.onSentence φ).not}` reduces along `g` to a model of `T ∪ {φ.not}`.
When `g` is injective, Mathlib's `Theory.isSatisfiable_onTheory_iff` upgrades this to an
equivalence (`FirstOrder.Language.LHom.Injective.onTheory_models_onSentence_iff`). For a language
equivalence `e : L ≃ᴸ L'`, `e.toLHom` is injective and `e.onSentence` is bijective, so
`e.toLHom.onTheory T` is satisfiable, entails `e.onSentence φ`, or is complete if and only if `T`
is (`FirstOrder.Language.LEquiv.isSatisfiable_onTheory_iff`,
`FirstOrder.Language.LEquiv.onTheory_models_onSentence_iff`,
`FirstOrder.Language.LEquiv.isComplete_onTheory_iff`).

## Main results

* `FirstOrder.Language.LHom.onSentence_not` and `FirstOrder.Language.LEquiv.onSentence_not`:
  language maps and equivalences commute with negation of sentences.
* `FirstOrder.Language.LHom.onTheory_models_onSentence`: language homomorphisms preserve semantic
  entailment of first-order sentences.
* `FirstOrder.Language.LHom.Injective.onTheory_models_onSentence_iff`: injective language
  homomorphisms preserve and reflect semantic entailment of first-order sentences.
* `FirstOrder.Language.LEquiv.isSatisfiable_onTheory_iff`,
  `FirstOrder.Language.LEquiv.toLHom_onTheory_models_onSentence_iff`,
  `FirstOrder.Language.LEquiv.onTheory_models_onSentence_iff`, and
  `FirstOrder.Language.LEquiv.isComplete_onTheory_iff`: satisfiability, entailment, and
  completeness of first-order theories are invariant under language equivalences.
-/

public section

universe u v u' v'

namespace FirstOrder.Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

namespace LHom

/-- A language homomorphism commutes with negation of sentences. -/
@[simp]
theorem onSentence_not (g : L →ᴸ L') (φ : L.Sentence) :
    g.onSentence φ.not = (g.onSentence φ).not :=
  (rfl)

/-- **Language homomorphisms preserve semantic entailment of sentences.** No injectivity of `g` is
needed. -/
theorem onTheory_models_onSentence (g : L →ᴸ L') {T : L.Theory} {φ : L.Sentence} (h : T ⊨ᵇ φ) :
    g.onTheory T ⊨ᵇ g.onSentence φ := by
  rw [Theory.models_iff_not_satisfiable] at h ⊢
  refine fun hsat => h (Theory.isSatisfiable_of_isSatisfiable_onTheory g ?_)
  simpa only [onTheory, Set.image_union, Set.image_singleton, onSentence_not] using hsat

/-- **Injective language homomorphisms preserve and reflect semantic entailment of sentences.**
This is the entailment companion to Mathlib's `Theory.isSatisfiable_onTheory_iff`. -/
theorem Injective.onTheory_models_onSentence_iff {g : L →ᴸ L'} (hg : g.Injective) {T : L.Theory}
    {φ : L.Sentence} : g.onTheory T ⊨ᵇ g.onSentence φ ↔ T ⊨ᵇ φ := by
  simp only [Theory.models_iff_not_satisfiable, ← Theory.isSatisfiable_onTheory_iff hg,
    onTheory, Set.image_union, Set.image_singleton, onSentence_not]

end LHom

namespace LEquiv

variable (e : L ≃ᴸ L')

/-- A language equivalence commutes with negation of sentences. -/
theorem onSentence_not (φ : L.Sentence) :
    e.onSentence φ.not = (e.onSentence φ).not :=
  (rfl)

/-- Transporting a first-order theory along a language equivalence preserves and reflects
satisfiability. -/
@[simp]
theorem isSatisfiable_onTheory_iff {T : L.Theory} :
    (e.toLHom.onTheory T).IsSatisfiable ↔ T.IsSatisfiable :=
  Theory.isSatisfiable_onTheory_iff e.toLHom_injective

/-- Transporting a theory and a sentence along `e.toLHom` preserves and reflects semantic
entailment. -/
@[simp]
theorem toLHom_onTheory_models_onSentence_iff {T : L.Theory} {φ : L.Sentence} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onSentence φ ↔ T ⊨ᵇ φ :=
  e.toLHom_injective.onTheory_models_onSentence_iff

/-- Transporting a theory and a sentence along a language equivalence preserves and reflects
semantic entailment. -/
theorem onTheory_models_onSentence_iff {T : L.Theory} {φ : L.Sentence} :
    e.toLHom.onTheory T ⊨ᵇ e.onSentence φ ↔ T ⊨ᵇ φ :=
  e.toLHom_injective.onTheory_models_onSentence_iff

/-- **Completeness along a language equivalence.** The image of a first-order theory under a
language equivalence is complete if and only if the original theory is complete. -/
@[simp]
theorem isComplete_onTheory_iff {T : L.Theory} :
    (e.toLHom.onTheory T).IsComplete ↔ T.IsComplete := by
  refine and_congr e.isSatisfiable_onTheory_iff ?_
  refine e.onSentence.surjective.forall.trans (forall_congr' fun φ => ?_)
  rw [← e.onSentence_not, e.onTheory_models_onSentence_iff, e.onTheory_models_onSentence_iff]

end LEquiv

end FirstOrder.Language
