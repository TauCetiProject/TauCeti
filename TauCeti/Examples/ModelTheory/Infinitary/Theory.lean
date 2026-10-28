/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.Theory

/-!
# Regression examples: the conjunction of a countable theory

These examples exercise countable `L_{ω₁ω}` theories from a downstream module, through public
statements only:

* the conjunction of the empty theory holds in every structure, including the empty one, since
  every index of the carrier codes no sentence and carries `⊤`;
* the conjunction of a single sentence is equivalent to that sentence;
* the conjunction of `{φ, ⊥}` holds in no structure;
* adding constants preserves modelhood: a structure is a model of an `L`-theory exactly when its
  `L[[ℕ]]`-expansion, under any interpretation of the constants, is a model of the image theory.
-/

universe u v w

open FirstOrder FirstOrder.Language

-- The conjunction of the empty theory holds in every structure, the empty one included.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] :
    SentenceInf.Realize ((∅ : L.Theoryω).conjunction Set.countable_empty) M := by
  simp

-- The conjunction of a single sentence is equivalent to the sentence.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] (φ : L.Sentenceω) :
    SentenceInf.Realize (({φ} : L.Theoryω).conjunction (Set.countable_singleton φ)) M ↔
      SentenceInf.Realize φ M := by
  simp

-- A theory containing `⊥` has an unsatisfiable conjunction.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] (φ : L.Sentenceω) :
    ¬ SentenceInf.Realize (({φ, ⊥} : L.Theoryω).conjunction
      ((Set.countable_singleton _).insert φ)) M := by
  rw [Theoryω.realize_conjunction_iff, Theoryω.model_insert_iff, Theoryω.model_singleton_iff]
  simp [SentenceInf.realize_def, FormulaInf.realize_def]

-- Adding constants preserves modelhood, however the constants are interpreted.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] (c : ℕ → M) (T : L.Theoryω) :
    letI : (constantsOn ℕ).Structure M := constantsOn.structure c
    ((L.lhomWithConstants ℕ).onTheoryω T).Model M ↔ T.Model M := by
  let : (constantsOn ℕ).Structure M := constantsOn.structure c
  exact LHom.onTheoryω_model _ T
