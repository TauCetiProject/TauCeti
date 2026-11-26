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
-- every vertex. Flipping it at vertex `0` gives an expanded code that is not a canonical expansion
-- but has the same reduct: the reduct is inverse to the expansion only on canonical expansions.
example (c : RelationalConfiguration L ℕ) :
    let S : (morleyize L {⟨1, ⊤⟩}).Structure ℕ := ⟨fun f => isEmptyElim f, fun {_} R xs =>
      match R with
      | .inl R => c.eval (atom R xs) = true
      | .inr _ => ∀ i, xs i ≠ 0⟩
    (∀ x : ℕ, (morleyCode {⟨1, ⊤⟩} c).eval
        (atom (morleyRel (⊤ : L.BoundedFormulaω Empty 1) (Set.mem_singleton _)) ![x]) = true) ∧
      @ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S ≠ morleyCode {⟨1, ⊤⟩} c ∧
      (lhomMorleyize {⟨1, ⊤⟩}).reductConfiguration (@ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S) =
        (lhomMorleyize {⟨1, ⊤⟩}).reductConfiguration (morleyCode {⟨1, ⊤⟩} c) := by
  intro S
  classical
  -- the new bit of the canonical expansion holds at every vertex, since `⊤` does
  have hall (x : ℕ) : (morleyCode {⟨1, ⊤⟩} c).eval
      (atom (morleyRel (⊤ : L.BoundedFormulaω Empty 1) (Set.mem_singleton _)) ![x]) = true := by
    let := c.toStructure
    exact (eval_morleyCode_morleyRel_eq_true_iff c _ ![x]).2
      (BoundedFormulaInf.realize_top.2 trivial)
  refine ⟨hall, fun h => ?_, ?_⟩
  · -- in the flipped code the new bit is false at vertex `0`, where `hall` makes it true
    have hflip : (@ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S).eval
        (atom (morleyRel (⊤ : L.BoundedFormulaω Empty 1) (Set.mem_singleton _)) ![0]) = false := by
      rw [@eval_ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S, decide_eq_false_iff_not]
      simp [S, Structure.RelMap]
    rw [h, hall 0] at hflip
    exact Bool.noConfusion hflip
  · -- both reducts read the atoms of `c`
    rw [reductConfiguration_morleyCode]
    refine ext fun a => ?_
    induction a using Atom.induction_atom with
    | h R x =>
      simp [LHom.eval_reductConfiguration, LHom.onAtom_atom, lhomMorleyize_onRelation,
        @eval_ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S, S, Structure.RelMap]
