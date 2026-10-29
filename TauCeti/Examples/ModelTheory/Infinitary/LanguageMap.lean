/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.LanguageMap

/-!
# Regression examples: language maps on infinitary formulas

These examples exercise the action of language maps on infinitary formulas from a downstream
module, through public statements only:

* adding constants preserves truth: an `L_{ω₁ω}` sentence of `L` holds in an `L`-structure exactly
  when its image holds in an `L[[ℕ]]`-expansion of it, however the constants are interpreted;
* consequently, the truth of the image does not depend on the interpretation of the constants;
* a relation symbol mapped by a language map is read in the target structure, with no expansion
  hypothesis.
-/

universe u v w

open FirstOrder FirstOrder.Language

-- Adding constants preserves truth: the image of an `L`-sentence in `L[[ℕ]]` holds in the
-- expansion of `M` that interprets the constants by `c` exactly when the sentence holds in `M`.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] (c : ℕ → M) (φ : L.Sentenceω) :
    letI : (constantsOn ℕ).Structure M := constantsOn.structure c
    SentenceInf.Realize ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ : L[[ℕ]].Sentenceω) M ↔
      SentenceInf.Realize φ M := by
  let : (constantsOn ℕ).Structure M := constantsOn.structure c
  simp only [SentenceInf.realize_def, FormulaInf.realize_def]
  exact LHom.realize_onBoundedFormulaInf _ _ _ _

-- The image of an `L`-sentence has the same truth value under any two interpretations of the
-- added constants.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] (c c' : ℕ → M) (φ : L.Sentenceω) :
    (letI : (constantsOn ℕ).Structure M := constantsOn.structure c;
      SentenceInf.Realize ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ : L[[ℕ]].Sentenceω) M) ↔
    (letI : (constantsOn ℕ).Structure M := constantsOn.structure c';
      SentenceInf.Realize ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ : L[[ℕ]].Sentenceω)
        M) := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def]
  let : (constantsOn ℕ).Structure M := constantsOn.structure c
  rw [LHom.realize_onBoundedFormulaInf]
  let : (constantsOn ℕ).Structure M := constantsOn.structure c'
  rw [LHom.realize_onBoundedFormulaInf]

-- A unary relation symbol `P` of `L` mapped by `g` to `g.onRelation P`: the image of `∀ x, P x`
-- is read with the target symbol in the target structure, with no expansion hypothesis.
example {L : Language.{u, v}} {L' : Language.{u, v}} (g : L →ᴸ L') {M : Type w}
    [L'.Structure M] (P : L.Relations 1) :
    SentenceInf.Realize (g.onBoundedFormulaInf
        (BoundedFormulaInf.rel P fun _ => Term.var (Sum.inr 0)).all : L'.Sentenceω) M ↔
      ∀ x : M, Structure.RelMap (g.onRelation P) fun _ => x := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, LHom.onBoundedFormulaInf_all,
    LHom.onBoundedFormulaInf_rel, BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_rel,
    LHom.onTerm, Term.realize_var]
  -- the quantified variable fills the only slot, so the valuation is constant at it
  exact Iff.rfl
