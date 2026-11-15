/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.SentenceTheory

/-!
# Regression example: every Boolean sequence is a truth sequence

Over a language with countably many nullary relation symbols `R₀, R₁, …` and no other symbols,
the truth sequence of the list of sentences `R₀, R₁, …` takes every value in Cantor space: for
each `z : ℕ → Bool`, the structure on `ℕ` in which `Rₖ` holds exactly when `z k = true` has truth
sequence `z`.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- Over a language with countably many nullary relation symbols `R₀, R₁, …` and no other symbols,
-- every Boolean sequence is the truth sequence of the list of sentences `R₀, R₁, …`. The relation
-- symbols of arity `n` are the natural numbers when `n = 0`, and there are none otherwise.
example :
    letI L : Language.{0, 0} := ⟨fun _ => Empty, fun n => {_k : ℕ // n = 0}⟩
    letI : L.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)
    Function.Surjective (sentenceTheory (V := ℕ) fun k => (BoundedFormulaInf.rel (l := 0)
      (⟨k, rfl⟩ : L.Relations 0) Fin.elim0 : L.SentenceInf ℕ)) := by
  intro z
  let L : Language.{0, 0} := ⟨fun _ => Empty, fun n => {_k : ℕ // n = 0}⟩
  -- the structure on `ℕ` in which the `k`-th nullary symbol holds exactly when `z k` does
  let S : L.Structure ℕ := ⟨fun f => isEmptyElim f, fun R _ => z R.1 = true⟩
  refine ⟨@ofStructure L ℕ S, funext fun n => Bool.eq_iff_iff.2 ?_⟩
  simp only [sentenceTheory_eq_true_iff, mem_modelsOf, SentenceInf.realize_def,
    FormulaInf.realize_def, BoundedFormulaInf.realize_rel, toStructure_relMap]
  classical
  exact (congrArg (· = true) (eval_ofStructure (L := L) (V := ℕ) _ _)).to_iff.trans
    decide_eq_true_iff
