/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Satisfiability
public import TauCeti.ModelTheory.Syntax

/-!
# Entailment and completeness along a language equivalence

Additions to Mathlib's `Mathlib.ModelTheory.Satisfiability`. Translating a first-order theory
along a language equivalence `e : L ≃ᴸ L'` preserves and reflects what it entails and whether it
is complete. The languages may live in different universes, so the models of the two theories
need not live in the same universe; the comparison goes through satisfiability, which Mathlib
transports along injective language maps in any universes (`isSatisfiable_onTheory_iff`).

## Main results

* `FirstOrder.Language.LEquiv.toLHom_injective`: the forward map of a language equivalence is
  injective.
* `FirstOrder.Language.LEquiv.onTheory_models_onSentence_iff`: a theory entails a sentence exactly
  when their translations along `e` do.
* `FirstOrder.Language.LEquiv.isComplete_onTheory_iff`: a theory is complete exactly when its
  translation along `e` is.
-/

public section

universe u v u' v'

namespace FirstOrder.Language.LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}} (e : L ≃ᴸ L')

/-- The forward map of a language equivalence is injective on symbols. -/
theorem toLHom_injective : e.toLHom.Injective where
  onFunction {n} := Function.LeftInverse.injective (g := fun f => e.invLHom.onFunction f)
    fun f => by simpa using congrArg (fun φ : L →ᴸ L => φ.onFunction f) e.left_inv
  onRelation {n} := Function.LeftInverse.injective (g := fun R => e.invLHom.onRelation R)
    fun R => by simpa using congrArg (fun φ : L →ᴸ L => φ.onRelation R) e.left_inv

variable {e} {T : L.Theory}

/-- **Entailment along a language equivalence.** A theory entails a sentence exactly when the
translation of the theory along `e` entails the translation of the sentence. -/
theorem onTheory_models_onSentence_iff {φ : L.Sentence} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onSentence φ ↔ T ⊨ᵇ φ := by
  rw [Theory.models_iff_not_satisfiable, Theory.models_iff_not_satisfiable,
    ← Theory.isSatisfiable_onTheory_iff e.toLHom_injective (T := T ∪ {φ.not}), LHom.onTheory,
    LHom.onTheory, Set.image_union, Set.image_singleton, LHom.onSentence_not]

/-- **Completeness along a language equivalence.** A theory is complete exactly when its
translation along `e` is complete. -/
theorem isComplete_onTheory_iff : (e.toLHom.onTheory T).IsComplete ↔ T.IsComplete := by
  refine and_congr (Theory.isSatisfiable_onTheory_iff e.toLHom_injective)
    ⟨fun h φ => ?_, fun h ψ => ?_⟩
  · refine (h (e.toLHom.onSentence φ)).imp onTheory_models_onSentence_iff.1 fun hφ => ?_
    rw [← LHom.onSentence_not] at hφ
    exact onTheory_models_onSentence_iff.1 hφ
  · -- `e.onSentence` is the equivalence of sentences whose forward map is `e.toLHom.onSentence`.
    obtain ⟨φ, rfl⟩ : ∃ φ, e.toLHom.onSentence φ = ψ := e.onSentence.surjective ψ
    refine (h φ).imp onTheory_models_onSentence_iff.2 fun hφ => ?_
    rw [← LHom.onSentence_not]
    exact onTheory_models_onSentence_iff.2 hφ

end FirstOrder.Language.LEquiv
