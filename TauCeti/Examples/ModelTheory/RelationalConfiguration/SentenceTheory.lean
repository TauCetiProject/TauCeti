/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.SentenceTheory

/-!
# Regression example: every Boolean sequence is a truth sequence

Over a language with countably many nullary relation symbols `R₀, R₁, …` and no other symbols,
the truth sequence of the list of sentences `R₀, R₁, …` takes every value in Cantor space: for
each `z : ℕ → Bool`, the structure on `ℕ` in which `Rₖ` holds exactly when `z k = true` has truth
sequence `z`.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

/-- A language with countably many nullary relation symbols and no other symbols: the relation
symbols of arity `n` are the natural numbers when `n = 0`, and there are none otherwise. -/
abbrev nullaryLanguage : Language.{0, 0} where
  Functions _ := Empty
  Relations n := {_k : ℕ // n = 0}

/-- The language of countably many nullary relation symbols is relational. -/
instance : nullaryLanguage.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

-- Every Boolean sequence is the truth sequence of the list of nullary sentences `R₀, R₁, …`.
example :
    Function.Surjective (sentenceTheory (V := ℕ) fun k => (BoundedFormulaInf.rel (l := 0)
      (⟨k, rfl⟩ : nullaryLanguage.Relations 0) Fin.elim0 : nullaryLanguage.SentenceInf ℕ)) := by
  intro z
  -- the structure on `ℕ` in which the `k`-th nullary symbol holds exactly when `z k` does
  let S : nullaryLanguage.Structure ℕ := ⟨fun f => isEmptyElim f, fun R _ => z R.1 = true⟩
  refine ⟨@ofStructure nullaryLanguage ℕ S, funext fun n => Bool.eq_iff_iff.2 ?_⟩
  simp only [sentenceTheory_eq_true_iff, mem_modelsOf, SentenceInf.realize_def,
    FormulaInf.realize_def, BoundedFormulaInf.realize_rel, toStructure_relMap, eval_ofStructure,
    decide_eq_true_eq]
  exact Iff.rfl
