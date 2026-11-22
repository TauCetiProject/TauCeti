/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.Morleyization

/-!
# Regression examples: expansion codes and their reducts

For a relational language `L` on the carrier `ℕ`:

* for the empty family the expansion code and the reduct are mutually inverse, in both orders:
  with no new symbols, every expanded code is the expansion of its reduct;
* for the family `{⊤}` of one unary formula, the new bit of every canonical expansion is true at
  every vertex;
* flipping that bit at vertex `0` gives an expanded code that differs from the canonical expansion
  but has the same reduct, so the reduct is inverse to the expansion code only on canonical
  expansions.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

variable {L : Language} [L.IsRelational]

-- Empty family: expansion and reduct are mutually inverse, in both orders.
example (c : RelationalConfiguration L ℕ) (e : RelationalConfiguration (morleyize L ∅) ℕ) :
    (lhomMorleyize ∅).reductConfiguration (morleyCode ∅ c) = c ∧
      morleyCode ∅ ((lhomMorleyize ∅).reductConfiguration e) = e :=
  ⟨reductConfiguration_morleyCode c,
    (eq_morleyCode_reductConfiguration_iff.2 fun _ _ hφ _ => absurd hφ (Set.notMem_empty _)).symm⟩

-- The family `{⊤}` of one unary formula: the new bit of every canonical expansion is true at
-- every vertex.
example (c : RelationalConfiguration L ℕ) (x : ℕ) :
    (morleyCode {⟨1, ⊤⟩} c).eval
      (atom (morleyRel (⊤ : L.BoundedFormulaω Empty 1) (Set.mem_singleton _)) ![x]) = true := by
  let := c.toStructure
  exact (eval_morleyCode_morleyRel_eq_true_iff c _ ![x]).2 (BoundedFormulaInf.realize_top.2 trivial)

-- Flipping the new bit at vertex `0` gives an expanded code that is not a canonical expansion but
-- has the same reduct: the reduct is inverse to the expansion only on canonical expansions.
example (c : RelationalConfiguration L ℕ) :
    let S : (morleyize L {⟨1, ⊤⟩}).Structure ℕ := ⟨fun f => isEmptyElim f, fun {_} R xs =>
      match R with
      | .inl R => c.eval (atom R xs) = true
      | .inr _ => ∀ i, xs i ≠ 0⟩
    @ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S ≠ morleyCode {⟨1, ⊤⟩} c ∧
      (lhomMorleyize {⟨1, ⊤⟩}).reductConfiguration (@ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S) =
        (lhomMorleyize {⟨1, ⊤⟩}).reductConfiguration (morleyCode {⟨1, ⊤⟩} c) := by
  intro S
  classical
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := congrArg (fun e : RelationalConfiguration (morleyize L {⟨1, ⊤⟩}) ℕ =>
      e.eval (atom (morleyRel (⊤ : L.BoundedFormulaω Empty 1) (Set.mem_singleton _)) ![0])) h
    simp only [@eval_ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S] at h1
    let := c.toStructure
    have h2 : (morleyCode {⟨1, ⊤⟩} c).eval
        (atom (morleyRel (⊤ : L.BoundedFormulaω Empty 1) (Set.mem_singleton _)) ![0]) = true :=
      (eval_morleyCode_morleyRel_eq_true_iff c _ ![0]).2 (BoundedFormulaInf.realize_top.2 trivial)
    rw [← h1] at h2
    have h3 := decide_eq_true_iff.1 h2
    exact (h3 : ∀ i : Fin 1, ![(0 : ℕ)] i ≠ 0) 0 rfl
  · rw [reductConfiguration_morleyCode]
    refine ext fun a => ?_
    induction a using Atom.induction_atom with
    | h R x =>
      simp only [LHom.eval_reductConfiguration, LHom.onAtom_atom, lhomMorleyize_onRelation,
        @eval_ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S]
      exact Bool.eq_iff_iff.2 (decide_eq_true_iff.trans Iff.rfl)
