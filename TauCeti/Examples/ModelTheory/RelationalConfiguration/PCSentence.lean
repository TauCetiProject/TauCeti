/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.PCSentence

/-!
# Examples of the PC sentence of a tree

The PC sentence of the empty tree has no model, since soundness would produce a branch of it, so
its projective class is empty. For the full tree on `Bool × ℕ`, every code on `ℕ`, expanded by the
standard witness structure of any branch, is a model, so the projective class of its PC sentence
contains every code.
-/

open FirstOrder FirstOrder.Language Descriptive Descriptive.Tree TauCeti RelationalConfiguration

-- The PC sentence of the empty tree has no model.
example {L : Language} [∀ n, Countable (L.Relations n)] (M : Type) [L.Structure M]
    [pcWitnessLanguage.Structure M] :
    ¬ SentenceInf.Realize (pcSentence (L := L) (⊥ : tree (Bool × ℕ))) M := fun h => by
  obtain ⟨e, g, -, -, -, hg⟩ := exists_mem_body_of_realize_pcSentence h
  rw [body_bot] at hg
  exact hg

-- For the full tree, every code with the standard witness of the zero branch is a model.
example {L : Language} [L.IsRelational] [∀ n, Countable (L.Relations n)]
    (c : RelationalConfiguration L ℕ) :
    @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ (pcSentence (⊤ : tree (Bool × ℕ))) ℕ
      (@Language.sumStructure L pcWitnessLanguage ℕ c.toStructure (standardWitness fun _ => 0)) :=
  realize_pcSentence_standardWitness (mem_body.2 fun _ => trivial)

-- No structure lies in the projective class of the PC sentence of the empty tree.
example {L : Language} [∀ n, Countable (L.Relations n)] (M : Type) [L.Structure M] :
    ¬ (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentence (⊥ : tree (Bool × ℕ))) M :=
  fun h => by
    obtain ⟨e, g, hg⟩ := pcMem_pcSentence_iff.1 h
    rw [body_bot] at hg
    exact hg
