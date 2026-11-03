/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Theory
public import Mathlib.ModelTheory.Satisfiability

/-!
# Satisfiability and entailment of `L_{ω₁ω}` theories

An `L_{ω₁ω}` theory is *satisfiable* when it has a nonempty model, and it *entails* a sentence
when every nonempty model of the theory satisfies the sentence. As in Mathlib's first-order
`Theory.IsSatisfiable` and `Theory.ModelsBoundedFormula`, both notions quantify over models in
the fixed universe `max u v` of a language `L : Language.{u, v}`. Any nonempty model that is
small in that universe, in particular any countable model, witnesses satisfiability and
satisfies every entailed sentence.

Entailment is reflexive, monotone and transitive, admits cut, and is refutation of the negated
conclusion. A countable theory entails exactly what the conjunction of its sentences entails, so
the entailments of a countable theory are entailments between two sentences. For first-order
theories and sentences, embedded into `L_{ω₁ω}` by `BoundedFormula.toOmega`, satisfiability and
entailment agree with Mathlib's first-order notions.

## Main definitions

* `FirstOrder.Language.Theoryω.IsSatisfiable`: a theory has a nonempty model.
* `FirstOrder.Language.Theoryω.Entails`: every nonempty model of a theory satisfies a sentence.
* `FirstOrder.Language.Sentenceω.Entails`: entailment between two sentences.

## Main results

* `FirstOrder.Language.Theoryω.Model.isSatisfiable`: a nonempty small model witnesses
  satisfiability.
* `FirstOrder.Language.Theoryω.Entails.realize_of_small`: an entailed sentence holds in every
  nonempty small model.
* `FirstOrder.Language.Theoryω.entails_iff_not_isSatisfiable`: a theory entails a sentence exactly
  when the theory together with the negation of the sentence is unsatisfiable.
* `FirstOrder.Language.Theoryω.Entails.trans`, `FirstOrder.Language.Theoryω.Entails.cut`: the
  transitivity and cut rules.
* `FirstOrder.Language.Theoryω.entails_iff_conjunction_entails`: a countable theory entails what
  its conjunction entails.
* `FirstOrder.Language.Theoryω.isSatisfiable_image_toOmega_iff`,
  `FirstOrder.Language.Theoryω.entails_image_toOmega_iff` and
  `FirstOrder.Language.Sentenceω.entails_toOmega_iff`: agreement with Mathlib's
  `Theory.IsSatisfiable` and `Theory.ModelsBoundedFormula` on first-order theories.

## References

* The definitions and the refutation characterisation follow Mathlib's first-order
  `Theory.IsSatisfiable`, `Theory.ModelsBoundedFormula` and `Theory.models_iff_not_satisfiable` in
  `Mathlib/ModelTheory/Satisfiability.lean` (Aaron Anderson).
* Divergences from Mathlib: a model of an `L_{ω₁ω}` theory is an unbundled structure together
  with a proof of `Theoryω.Model`, so no bundled model type is introduced; a model in another
  universe is moved into the universe `max u v` through `Small`, whereas Mathlib's first-order
  `Theory.Model.isSatisfiable` uses downward Löwenheim–Skolem, which for `L_{ω₁ω}` holds only
  relative to countable fragments.
-/

public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

namespace Theoryω

variable {T T' : L.Theoryω} {φ ψ : L.Sentenceω}

/-- A theory is **satisfiable** when it has a nonempty model in the universe `max u v`, the model
universe of Mathlib's first-order `Theory.IsSatisfiable`. -/
def IsSatisfiable (T : L.Theoryω) : Prop :=
  ∃ (M : Type (max u v)) (_ : L.Structure M), Nonempty M ∧ T.Model M

/-- A theory **entails** a sentence when every nonempty model of the theory in the universe
`max u v` satisfies the sentence, as in Mathlib's first-order `Theory.ModelsBoundedFormula`. -/
def Entails (T : L.Theoryω) (φ : L.Sentenceω) : Prop :=
  ∀ (M : Type (max u v)) [L.Structure M] [Nonempty M], T.Model M → SentenceInf.Realize φ M

/-- Unfolding lemma for `Theoryω.IsSatisfiable`. -/
theorem isSatisfiable_iff :
    T.IsSatisfiable ↔ ∃ (M : Type (max u v)) (_ : L.Structure M), Nonempty M ∧ T.Model M :=
  Iff.rfl

/-- Unfolding lemma for `Theoryω.Entails`. -/
theorem entails_iff :
    T.Entails φ ↔ ∀ (M : Type (max u v)) [L.Structure M] [Nonempty M], T.Model M →
      SentenceInf.Realize φ M :=
  Iff.rfl

/-! ### Satisfiability -/

/-- A nonempty model of a theory that is small in the universe `max u v`, for instance a countable
model in any universe, witnesses the satisfiability of the theory. -/
theorem Model.isSatisfiable {M : Type w} [L.Structure M] [Nonempty M] [Small.{max u v} M]
    (h : T.Model M) : T.IsSatisfiable := by
  let e := equivShrink M
  let : L.Structure (Shrink M) := e.inducedStructure
  exact ⟨Shrink M, e.inducedStructure, e.symm.nonempty,
    (StrongHomClass.theoryω_model_iff (Equiv.inducedStructureEquiv e) T).1 h⟩

/-- A subtheory of a satisfiable theory is satisfiable. -/
theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hT : T ⊆ T') : T.IsSatisfiable := by
  obtain ⟨M, _, hM, hT'⟩ := h
  exact ⟨M, _, hM, hT'.mono hT⟩

/-- The empty theory is satisfiable. -/
@[simp]
theorem isSatisfiable_empty : (∅ : L.Theoryω).IsSatisfiable :=
  letI : L.Structure PUnit := Inhabited.trivialStructure L
  ⟨PUnit, inferInstance, inferInstance, model_empty⟩

/-! ### Entailment -/

/-- A theory entails each of its sentences. -/
theorem entails_of_mem (h : φ ∈ T) : T.Entails φ := by
  intro M _ _ hM
  exact hM.realize_of_mem h

/-- Entailment is monotone in the theory. -/
theorem Entails.mono (h : T.Entails φ) (hT : T ⊆ T') : T'.Entails φ := by
  intro M _ _ hM
  exact h M (hM.mono hT)

/-- A nonempty model of `T` in the universe `max u v` is a model of every theory whose sentences
`T` entails. -/
theorem Model.of_entails {M : Type (max u v)} [L.Structure M] [Nonempty M] (hM : T.Model M)
    (hT : ∀ ψ ∈ T', T.Entails ψ) : T'.Model M :=
  model_iff.2 fun ψ hψ => hT ψ hψ M hM

/-- **Transitivity of entailment.** If `T` entails every sentence of `T'`, then `T` entails every
sentence that `T'` entails. -/
theorem Entails.trans (h : T'.Entails φ) (hT : ∀ ψ ∈ T', T.Entails ψ) : T.Entails φ := by
  intro M _ _ hM
  exact h M (hM.of_entails hT)

/-- **Cut.** A sentence entailed by a theory may be used as an additional hypothesis. -/
theorem Entails.cut (hψ : T.Entails ψ) (h : (insert ψ T).Entails φ) : T.Entails φ :=
  h.trans fun _ hχ => hχ.elim (fun hχ => hχ ▸ hψ) entails_of_mem

/-- **Entailment is refutation.** A theory entails a sentence exactly when the theory together
with the negation of the sentence is unsatisfiable. This is the `L_{ω₁ω}` form of Mathlib's
`Theory.models_iff_not_satisfiable`. -/
theorem entails_iff_not_isSatisfiable : T.Entails φ ↔ ¬(insert φ.not T).IsSatisfiable := by
  simp only [entails_iff, isSatisfiable_iff, model_insert_iff, not_exists, not_and,
    SentenceInf.realize_not]
  refine ⟨fun h M _ _ hφ hT => hφ (h M hT), fun h M _ _ hT => ?_⟩
  by_contra hφ
  exact h M _ ‹_› hφ hT

/-- A sentence entailed by a theory holds in every nonempty model of the theory that is small in
the universe `max u v`, for instance in every countable model in any universe. -/
theorem Entails.realize_of_small (h : T.Entails φ) (M : Type w) [L.Structure M] [Nonempty M]
    [Small.{max u v} M] (hM : T.Model M) : SentenceInf.Realize φ M := by
  by_contra hφ
  refine entails_iff_not_isSatisfiable.1 h (Model.isSatisfiable (M := M) ?_)
  rw [model_insert_iff]
  exact ⟨SentenceInf.realize_not.2 hφ, hM⟩

/-- A theory is satisfiable exactly when it does not entail the false sentence. -/
theorem isSatisfiable_iff_not_entails_bot : T.IsSatisfiable ↔ ¬T.Entails ⊥ := by
  simp only [entails_iff, isSatisfiable_iff, SentenceInf.realize_bot]
  refine ⟨fun ⟨M, _, _, hM⟩ h => h M hM, fun h => by_contra fun hT => h fun M _ _ hM => ?_⟩
  exact hT ⟨M, _, ‹_›, hM⟩

/-- A theory entails the conjunction of a countable theory exactly when it entails each of its
sentences. -/
@[simp]
theorem entails_conjunction_iff (hT' : T'.Countable) :
    T.Entails (T'.conjunction hT') ↔ ∀ ψ ∈ T', T.Entails ψ := by
  simp only [entails_iff, realize_conjunction_iff, model_iff]
  exact ⟨fun h ψ hψ M _ _ hM => h M hM ψ hψ, fun h M _ _ hM ψ hψ => h ψ hψ M hM⟩

end Theoryω

/-! ### Entailment between sentences -/

namespace Sentenceω

variable {φ ψ χ : L.Sentenceω}

/-- A sentence **entails** another when the theory consisting of the first sentence entails the
second: every nonempty model of `φ` in the universe `max u v` satisfies `ψ`. -/
def Entails (φ ψ : L.Sentenceω) : Prop :=
  Theoryω.Entails {φ} ψ

/-- Entailment between sentences is entailment by the singleton theory. -/
theorem entails_def : φ.Entails ψ ↔ Theoryω.Entails {φ} ψ :=
  Iff.rfl

/-- A sentence entails another when every nonempty model of the first in the universe `max u v`
satisfies the second. -/
theorem entails_iff :
    φ.Entails ψ ↔ ∀ (M : Type (max u v)) [L.Structure M] [Nonempty M], SentenceInf.Realize φ M →
      SentenceInf.Realize ψ M := by
  simp only [entails_def, Theoryω.entails_iff, Theoryω.model_singleton_iff]

/-- Every sentence entails itself. -/
@[refl]
theorem Entails.refl (φ : L.Sentenceω) : φ.Entails φ :=
  Theoryω.entails_of_mem rfl

/-- Entailment between sentences is transitive. -/
@[trans]
theorem Entails.trans (h₁ : φ.Entails ψ) (h₂ : ψ.Entails χ) : φ.Entails χ :=
  Theoryω.Entails.trans h₂ fun _ hθ => (Set.mem_singleton_iff.1 hθ) ▸ h₁

end Sentenceω

namespace Theoryω

variable {T : L.Theoryω} {φ : L.Sentenceω}

/-- **A countable theory entails what its conjunction entails.** This reduces the entailments of a
countable theory to entailments between two sentences. -/
theorem entails_iff_conjunction_entails (hT : T.Countable) :
    T.Entails φ ↔ (T.conjunction hT).Entails φ := by
  simp only [Sentenceω.entails_def, entails_iff, model_singleton_iff, realize_conjunction_iff]

/-! ### Agreement with first-order satisfiability and entailment -/

/-- The image of a first-order theory in `L_{ω₁ω}` is satisfiable exactly when the first-order
theory is satisfiable in the sense of Mathlib's `Theory.IsSatisfiable`. -/
@[simp]
theorem isSatisfiable_image_toOmega_iff {T : L.Theory} :
    IsSatisfiable (BoundedFormula.toOmega '' T) ↔ T.IsSatisfiable := by
  refine ⟨fun ⟨M, _, _, hM⟩ => ?_, fun h => ⟨h.some, inferInstance, inferInstance,
    model_image_toOmega_iff.2 h.some.is_model⟩⟩
  have : M ⊨ T := model_image_toOmega_iff.1 hM
  exact Theory.Model.isSatisfiable M

/-- The image of a first-order theory in `L_{ω₁ω}` entails the image of a first-order sentence
exactly when the first-order theory models the sentence in the sense of Mathlib's
`Theory.ModelsBoundedFormula`. -/
@[simp]
theorem entails_image_toOmega_iff {T : L.Theory} {φ : L.Sentence} :
    Entails (BoundedFormula.toOmega '' T) φ.toOmega ↔ T ⊨ᵇ φ := by
  rw [entails_iff, Theory.models_sentence_iff]
  refine ⟨fun h M => ?_, fun h M _ _ hM => ?_⟩
  · exact (Sentence.realize_toInf φ M).1 (h M (model_image_toOmega_iff.2 M.is_model))
  · have : M ⊨ T := model_image_toOmega_iff.1 hM
    exact (Sentence.realize_toInf φ M).2 (h (Theory.ModelType.of T M))

end Theoryω

/-- Entailment between the images of two first-order sentences in `L_{ω₁ω}` is first-order
entailment in the sense of Mathlib's `Theory.ModelsBoundedFormula`. -/
@[simp]
theorem Sentenceω.entails_toOmega_iff {φ ψ : L.Sentence} :
    Sentenceω.Entails φ.toOmega ψ.toOmega ↔ {φ} ⊨ᵇ ψ := by
  rw [Sentenceω.entails_def, ← Set.image_singleton, Theoryω.entails_image_toOmega_iff]

end Language

end FirstOrder
