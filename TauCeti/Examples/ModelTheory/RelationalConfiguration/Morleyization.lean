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
    have h1 := congrArg (fun e : RelationalConfiguration (morleyize L {⟨1, ⊤⟩}) ℕ =>
      e.eval (atom (morleyRel (⊤ : L.BoundedFormulaω Empty 1) (Set.mem_singleton _)) ![0])) h
    simp only [@eval_ofStructure (morleyize L {⟨1, ⊤⟩}) ℕ S] at h1
    have h2 := hall 0
    rw [← h1] at h2
    have h3 := decide_eq_true_iff.1 h2
    exact (h3 : ∀ i : Fin 1, ![(0 : ℕ)] i ≠ 0) 0 rfl
  · -- both reducts decode to the structure of `c`
    rw [reductConfiguration_morleyCode]
    apply equivStructure.injective
    rw [equivStructure_apply, equivStructure_apply, LHom.toStructure_reductConfiguration,
      toStructure_ofStructure]
    apply Structure.ext
    · funext n f
      exact isEmptyElim f
    · funext n R xs
      apply propext
      -- the reduct reads `R` as the symbol `Sum.inl R` of `S`, which copies the atoms of `c`
      change @Structure.RelMap _ _ S _ ((lhomMorleyize {⟨1, ⊤⟩}).onRelation R) xs ↔ _
      rw [lhomMorleyize_onRelation, toStructure_relMap]
      rfl
