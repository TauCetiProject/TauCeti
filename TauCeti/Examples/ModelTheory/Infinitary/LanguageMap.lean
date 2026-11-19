/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.ConstantAbstraction
import TauCeti.ModelTheory.Infinitary.LanguageMap
import TauCeti.ModelTheory.Infinitary.SubstBounds
import TauCeti.ModelTheory.Infinitary.ToFormula

/-!
# Regression examples: language maps on infinitary formulas

These examples exercise the action of language maps on infinitary formulas from a downstream
module, through public statements only:

* adding constants preserves truth: an `L_{ω₁ω}` sentence of `L` holds in an `L`-structure exactly
  when its image holds in an `L[[ℕ]]`-expansion of it, however the constants are interpreted;
* consequently, the truth of the image does not depend on the interpretation of the constants;
* a relation symbol mapped by a language map is read in the target structure, with no expansion
  hypothesis;
* a language map commutes with embedding a finitary formula, weakening it and transporting it to
  another carrier, all at once;
* a language map commutes with free-variable substitution, free-variable relabelling, opening
  bound positions (`toFormula`), universal/existential closures and bound-position instantiation,
  and preserves `freeVarSupport` without decidable equality on free variables;
* lifting a language map or language equivalence by `addConstants` commutes with
  `constantsVarsEquiv` and `abstractConst` and preserves `constantSupport` across distinct
  language universes.
-/

universe u v u' v' w

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

-- Translating commutes with embedding a finitary formula, weakening it and recoding its carrier.
example {L L' : Language.{u, v}} (g : L →ᴸ L') {ι κ : Type*} {α : Type*} {m n : ℕ}
    (φ : L.BoundedFormula α m) (h : m ≤ n) (c : TauCeti.IndexCoding ι κ) :
    g.onBoundedFormulaInf (((φ.toInf : L.BoundedFormulaInf ι α m).castLE h).reindex c) =
      (((g.onBoundedFormula φ).toInf : L'.BoundedFormulaInf ι α m).castLE h).reindex c := by
  simp

-- Translating across distinct language universes commutes with free-variable substitution,
-- free-variable relabelling into bound slots, universal closure and opening bound positions.
example {L : Language.{u, v}} {L' : Language.{u', v'}} (g : L →ᴸ L')
    {ι α β γ : Type*} {m n : ℕ} (φ : L.BoundedFormulaInf ι α n) (σ : α → L.Term β)
    (ρ : β → γ ⊕ Fin m) :
    g.onBoundedFormulaInf ((TauCeti.BoundedFormulaInf.relabel ρ
      (TauCeti.BoundedFormulaInf.subst φ σ)).toFormula) =
      (TauCeti.BoundedFormulaInf.relabel ρ
        (TauCeti.BoundedFormulaInf.subst (g.onBoundedFormulaInf φ)
          fun a => g.onTerm (σ a))).toFormula := by
  simp

-- Translating commutes with single-slot instantiation and preserves free-variable support with
-- no `DecidableEq` assumption on the free-variable index type.
example {L : Language.{u, v}} {L' : Language.{u', v'}} (g : L →ᴸ L')
    {ι α : Type*} (φ : L.BoundedFormulaInf ι α 1) (t : L.Term (α ⊕ Fin 0)) :
    (g.onBoundedFormulaInf φ).freeVarSupport = φ.freeVarSupport ∧
      g.onBoundedFormulaInf (φ.inst t) = (g.onBoundedFormulaInf φ).inst (g.onTerm t) := by
  simp

-- Lifting a language equivalence by `LEquiv.addConstants` commutes with single-constant
-- abstraction followed by existential quantification, and preserves the constant support.
example {L : Language.{u, v}} {L' : Language.{u', v'}} (e : L ≃ᴸ L')
    {ι α γ : Type*} [DecidableEq γ] (c : γ) (φ : L[[γ]].FormulaInf ι α) :
    (e.addConstants γ).onBoundedFormulaInf (BoundedFormulaInf.abstractConst c φ).ex =
        (BoundedFormulaInf.abstractConst c ((e.addConstants γ).onBoundedFormulaInf φ)).ex ∧
      ((e.addConstants γ).onBoundedFormulaInf
        (BoundedFormulaInf.abstractConst c φ)).constantSupport =
        φ.constantSupport \ {c} := by
  simp
