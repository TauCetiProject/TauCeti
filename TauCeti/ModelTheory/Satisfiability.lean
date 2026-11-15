/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Satisfiability
import TauCeti.ModelTheory.LanguageMap
import TauCeti.ModelTheory.Syntax

/-!
# Semantic entailment and completeness of first-order theories along language maps

Additions to Mathlib's `Mathlib.ModelTheory.Satisfiability` describing how semantic entailment
(`T ⊨ᵇ φ`), satisfiability, and completeness (`Theory.IsComplete`) of first-order theories behave
under language homomorphisms and language equivalences, across arbitrary language and variable
universes.

Every language homomorphism `g : L →ᴸ L'` preserves semantic entailment of bounded formulas,
because any model `M` of `g.onTheory T` reduces along `g` to a model of `T` in which
`LHom.realize_onBoundedFormula` transfers realization. When `g` is injective, expanding any model
`M` of `T` along `g` via `LHom.defaultExpansion` upgrades this to an equivalence
(`FirstOrder.Language.LHom.Injective.onTheory_models_onBoundedFormula_iff`). For a language
equivalence `e : L ≃ᴸ L'`, `e.toLHom` is injective and `e.onSentence` is bijective, so
`e.toLHom.onTheory T` is satisfiable, entails translated bounded formulas, formulas, or sentences,
or is complete if and only if `T` is (`FirstOrder.Language.LEquiv.isSatisfiable_onTheory_iff`,
`FirstOrder.Language.LEquiv.toLHom_onTheory_models_onBoundedFormula_iff`,
`FirstOrder.Language.LEquiv.onTheory_models_onSentence_iff`,
`FirstOrder.Language.LEquiv.isComplete_onTheory_iff`).

## Main results

* `FirstOrder.Language.LHom.onTheory_models_onBoundedFormula`,
  `FirstOrder.Language.LHom.onTheory_models_onFormula`, and
  `FirstOrder.Language.LHom.onTheory_models_onSentence`: language homomorphisms preserve semantic
  entailment of bounded formulas, formulas, and sentences.
* `FirstOrder.Language.LHom.Injective.onTheory_models_onBoundedFormula_iff`,
  `FirstOrder.Language.LHom.Injective.onTheory_models_onFormula_iff`, and
  `FirstOrder.Language.LHom.Injective.onTheory_models_onSentence_iff`: injective language
  homomorphisms preserve and reflect semantic entailment.
* `FirstOrder.Language.LEquiv.isSatisfiable_onTheory_iff`,
  `FirstOrder.Language.LEquiv.toLHom_onTheory_models_onBoundedFormula_iff`,
  `FirstOrder.Language.LEquiv.toLHom_onTheory_models_onFormula_iff`,
  `FirstOrder.Language.LEquiv.toLHom_onTheory_models_onSentence_iff`,
  `FirstOrder.Language.LEquiv.onTheory_models_onBoundedFormula_iff`,
  `FirstOrder.Language.LEquiv.onTheory_models_onFormula_iff`,
  `FirstOrder.Language.LEquiv.onTheory_models_onSentence_iff`, and
  `FirstOrder.Language.LEquiv.isComplete_onTheory_iff`: satisfiability, entailment, and
  completeness of first-order theories are invariant under language equivalences.
-/

public section

universe u v u' v' w

namespace FirstOrder.Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {α : Type w} {n : ℕ}

namespace LHom

/-- **Language homomorphisms preserve semantic entailment of bounded formulas.** No injectivity of
`g` is needed. -/
theorem onTheory_models_onBoundedFormula (g : L →ᴸ L') {T : L.Theory}
    {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) :
    g.onTheory T ⊨ᵇ g.onBoundedFormula φ := fun M _ _ => by
  let := g.reduct M
  have : M ⊨ T := (g.onTheory_model T).1 M.is_model
  exact (g.realize_onBoundedFormula φ).2 (h.realize_boundedFormula M)

/-- Language homomorphisms preserve semantic entailment of formulas. -/
theorem onTheory_models_onFormula (g : L →ᴸ L') {T : L.Theory} {φ : L.Formula α} (h : T ⊨ᵇ φ) :
    g.onTheory T ⊨ᵇ g.onFormula φ :=
  g.onTheory_models_onBoundedFormula h

/-- **Language homomorphisms preserve semantic entailment of sentences.** No injectivity of `g` is
needed. -/
theorem onTheory_models_onSentence (g : L →ᴸ L') {T : L.Theory} {φ : L.Sentence} (h : T ⊨ᵇ φ) :
    g.onTheory T ⊨ᵇ g.onSentence φ :=
  g.onTheory_models_onBoundedFormula h

/-- **Injective language homomorphisms preserve and reflect semantic entailment of bounded
formulas.** This is the entailment companion to Mathlib's `Theory.isSatisfiable_onTheory_iff`. -/
theorem Injective.onTheory_models_onBoundedFormula_iff {g : L →ᴸ L'} (hg : g.Injective)
    {T : L.Theory} {φ : L.BoundedFormula α n} :
    g.onTheory T ⊨ᵇ g.onBoundedFormula φ ↔ T ⊨ᵇ φ := by
  refine ⟨fun h M _ _ => ?_, g.onTheory_models_onBoundedFormula⟩
  classical
  have : Inhabited M := Classical.inhabited_of_nonempty'
  let := g.defaultExpansion M
  have := hg.isExpansionOn_default M
  have : M ⊨ g.onTheory T := (g.onTheory_model T).2 M.is_model
  exact (g.realize_onBoundedFormula φ).1 (h.realize_boundedFormula M)

/-- Injective language homomorphisms preserve and reflect semantic entailment of formulas. -/
theorem Injective.onTheory_models_onFormula_iff {g : L →ᴸ L'} (hg : g.Injective) {T : L.Theory}
    {φ : L.Formula α} : g.onTheory T ⊨ᵇ g.onFormula φ ↔ T ⊨ᵇ φ :=
  hg.onTheory_models_onBoundedFormula_iff

/-- **Injective language homomorphisms preserve and reflect semantic entailment of sentences.**
This is the entailment companion to Mathlib's `Theory.isSatisfiable_onTheory_iff`. -/
theorem Injective.onTheory_models_onSentence_iff {g : L →ᴸ L'} (hg : g.Injective) {T : L.Theory}
    {φ : L.Sentence} : g.onTheory T ⊨ᵇ g.onSentence φ ↔ T ⊨ᵇ φ :=
  hg.onTheory_models_onBoundedFormula_iff

end LHom

namespace LEquiv

variable (e : L ≃ᴸ L')

/-- Transporting a first-order theory along a language equivalence preserves and reflects
satisfiability. -/
@[simp]
theorem isSatisfiable_onTheory_iff {T : L.Theory} :
    (e.toLHom.onTheory T).IsSatisfiable ↔ T.IsSatisfiable :=
  Theory.isSatisfiable_onTheory_iff e.toLHom_injective

/-- Transporting a theory and a bounded formula along `e.toLHom` preserves and reflects semantic
entailment. -/
@[simp]
theorem toLHom_onTheory_models_onBoundedFormula_iff {T : L.Theory} {φ : L.BoundedFormula α n} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onBoundedFormula φ ↔ T ⊨ᵇ φ :=
  e.toLHom_injective.onTheory_models_onBoundedFormula_iff

/-- Transporting a theory and a formula along `e.toLHom` preserves and reflects semantic
entailment. -/
@[simp]
theorem toLHom_onTheory_models_onFormula_iff {T : L.Theory} {φ : L.Formula α} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onFormula φ ↔ T ⊨ᵇ φ :=
  e.toLHom_injective.onTheory_models_onFormula_iff

/-- Transporting a theory and a sentence along `e.toLHom` preserves and reflects semantic
entailment. -/
@[simp]
theorem toLHom_onTheory_models_onSentence_iff {T : L.Theory} {φ : L.Sentence} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onSentence φ ↔ T ⊨ᵇ φ :=
  e.toLHom_injective.onTheory_models_onSentence_iff

/-- Transporting a theory and a bounded formula along a language equivalence preserves and reflects
semantic entailment. -/
theorem onTheory_models_onBoundedFormula_iff {T : L.Theory} {φ : L.BoundedFormula α n} :
    e.toLHom.onTheory T ⊨ᵇ e.onBoundedFormula φ ↔ T ⊨ᵇ φ :=
  e.toLHom_injective.onTheory_models_onBoundedFormula_iff

/-- Transporting a theory and a formula along a language equivalence preserves and reflects
semantic entailment. -/
theorem onTheory_models_onFormula_iff {T : L.Theory} {φ : L.Formula α} :
    e.toLHom.onTheory T ⊨ᵇ e.onFormula φ ↔ T ⊨ᵇ φ :=
  e.toLHom_injective.onTheory_models_onFormula_iff

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
