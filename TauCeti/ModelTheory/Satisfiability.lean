/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Satisfiability
public import TauCeti.ModelTheory.LanguageMap
import TauCeti.ModelTheory.Syntax

/-!
# Entailment and completeness of first-order theories along language maps

Additions to Mathlib's `Mathlib.ModelTheory.Satisfiability` describing how semantic entailment
(`Theory.ModelsBoundedFormula`, written `T ⊨ᵇ φ`) and theory completeness (`Theory.IsComplete`)
behave under language homomorphisms and language equivalences across arbitrary universes.

Any language homomorphism `g : L →ᴸ L'` pushes semantic entailment forward
(`FirstOrder.Language.Theory.ModelsBoundedFormula.onTheory`): any model of `g.onTheory T` restricts
along `g.reduct` to a model of `T`. When `g` is injective, `g.defaultExpansion` expands every
nonempty model of `T` to a model of `g.onTheory T`, so `g` also reflects entailment
(`FirstOrder.Language.Theory.modelsBoundedFormula_onTheory_iff`,
`FirstOrder.Language.Theory.models_onSentence_onTheory_iff`) and reflects completeness
(`FirstOrder.Language.Theory.IsComplete.of_onTheory`). Along a language equivalence `e : L ≃ᴸ L'`,
`e.onSentence` is surjective on sentences as well, so satisfiability, entailment and completeness
are preserved and reflected (`FirstOrder.Language.LEquiv.isSatisfiable_onTheory_iff`,
`FirstOrder.Language.LEquiv.modelsBoundedFormula_onTheory_iff`,
`FirstOrder.Language.LEquiv.isComplete_onTheory_iff`).

## Main results

* `FirstOrder.Language.Theory.ModelsBoundedFormula.onTheory` and
  `FirstOrder.Language.Theory.modelsBoundedFormula_onTheory_iff`: entailment is preserved by every
  language map and reflected by injective ones, across arbitrary universes.
* `FirstOrder.Language.Theory.IsComplete.of_onTheory` and
  `FirstOrder.Language.LEquiv.isComplete_onTheory_iff`: completeness is reflected by injective
  language maps and invariant under language equivalences.
-/

public section

universe u v u' v' w

namespace FirstOrder.Language

namespace Theory

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {T : L.Theory} {α : Type w} {n : ℕ}

/-- **Language maps preserve semantic entailment.** If `T ⊨ᵇ φ`, then `g.onTheory T` models
`g.onBoundedFormula φ` for every language map `g : L →ᴸ L'`, across arbitrary universes. -/
theorem ModelsBoundedFormula.onTheory {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) (g : L →ᴸ L') :
    g.onTheory T ⊨ᵇ g.onBoundedFormula φ := by
  intro M v xs
  let : L.Structure M := g.reduct M
  have : M ⊨ T := (g.onTheory_model T).1 M.is_model
  exact (g.realize_onBoundedFormula φ).2 (h.realize_boundedFormula M)

/-- **Language maps preserve sentence entailment.** If `T ⊨ᵇ φ` for a sentence `φ`, then
`g.onTheory T ⊨ᵇ g.onSentence φ`. -/
theorem ModelsBoundedFormula.onSentence {φ : L.Sentence} (h : T ⊨ᵇ φ) (g : L →ᴸ L') :
    g.onTheory T ⊨ᵇ g.onSentence φ :=
  h.onTheory g

/-- **Injective language maps preserve and reflect semantic entailment.** For an injective language
map `g : L →ᴸ L'`, `g.onTheory T` models `g.onBoundedFormula φ` if and only if `T` models `φ`. -/
theorem modelsBoundedFormula_onTheory_iff {g : L →ᴸ L'} (hg : g.Injective)
    {φ : L.BoundedFormula α n} :
    g.onTheory T ⊨ᵇ g.onBoundedFormula φ ↔ T ⊨ᵇ φ := by
  classical
  refine ⟨fun h M v xs => ?_, fun h => h.onTheory g⟩
  have : Inhabited M := Classical.inhabited_of_nonempty'
  let : L'.Structure M := g.defaultExpansion M
  have : g.IsExpansionOn M := hg.isExpansionOn_default M
  have : M ⊨ g.onTheory T := (g.onTheory_model T).2 M.is_model
  exact (g.realize_onBoundedFormula φ).1 (h.realize_boundedFormula M)

/-- **Injective language maps preserve and reflect sentence entailment.** -/
theorem models_onSentence_onTheory_iff {g : L →ᴸ L'} (hg : g.Injective) {φ : L.Sentence} :
    g.onTheory T ⊨ᵇ g.onSentence φ ↔ T ⊨ᵇ φ :=
  modelsBoundedFormula_onTheory_iff hg

/-- **Injective language maps reflect completeness.** If `g : L →ᴸ L'` is injective and
`g.onTheory T` is complete, then `T` is complete. -/
theorem IsComplete.of_onTheory {g : L →ᴸ L'} (hg : g.Injective) (h : (g.onTheory T).IsComplete) :
    T.IsComplete := by
  refine ⟨isSatisfiable_of_isSatisfiable_onTheory g h.1, fun φ => ?_⟩
  rcases h.2 (g.onSentence φ) with hφ | hφ
  · exact .inl ((models_onSentence_onTheory_iff hg).1 hφ)
  · rw [← LHom.onSentence_not] at hφ
    exact .inr ((models_onSentence_onTheory_iff hg).1 hφ)

end Theory

namespace LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}} (e : L ≃ᴸ L')
  {T : L.Theory} {α : Type w} {n : ℕ}

/-- A language equivalence preserves and reflects satisfiability of first-order theories. -/
@[simp]
theorem isSatisfiable_onTheory_iff : (e.toLHom.onTheory T).IsSatisfiable ↔ T.IsSatisfiable :=
  Theory.isSatisfiable_onTheory_iff e.toLHom_injective

/-- A language equivalence preserves and reflects semantic entailment of bounded formulas. -/
@[simp]
theorem modelsBoundedFormula_onTheory_iff {φ : L.BoundedFormula α n} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onBoundedFormula φ ↔ T ⊨ᵇ φ :=
  Theory.modelsBoundedFormula_onTheory_iff e.toLHom_injective

/-- A language equivalence preserves and reflects semantic entailment of sentences. -/
@[simp]
theorem models_onSentence_onTheory_iff {φ : L.Sentence} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onSentence φ ↔ T ⊨ᵇ φ :=
  Theory.models_onSentence_onTheory_iff e.toLHom_injective

/-- **Completeness along a language equivalence.** The image of a first-order theory along a
language equivalence is complete if and only if the theory is complete. -/
@[simp]
theorem isComplete_onTheory_iff : (e.toLHom.onTheory T).IsComplete ↔ T.IsComplete := by
  refine ⟨fun h => h.of_onTheory e.toLHom_injective, fun ⟨hsat, hdec⟩ => ?_⟩
  refine ⟨e.isSatisfiable_onTheory_iff.2 hsat, fun ψ => ?_⟩
  obtain ⟨φ, rfl⟩ := e.onSentence.surjective ψ
  exact (hdec φ).imp e.models_onSentence_onTheory_iff.2 e.models_onSentence_onTheory_iff.2

end LEquiv

end FirstOrder.Language
