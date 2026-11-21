/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Hierarchy.NormalForm.Boolean

/-!
# Displayed arithmetical normal-form codes and Boolean code transformations

These examples exercise only the public API of `QuantifierPrefix` and `NormalFormCode` without
unfolding module-private bodies: prefix order and contraction, concrete valid oracle-dependent
codes, primitive recursive Boolean transformations (`neg`, `and`, `or`), soundness and
completeness for arithmetical pointclasses, and Π⁰₂-completeness / undecidability of validity.
-/

open Encodable TauCeti.Oracle.Single TauCeti.ArithmeticalHierarchy NormalFormCode

-- Prefix order: `zero` lies below every positive prefix, while Σ⁰₁ and Π⁰₁ are incomparable.
example : QuantifierPrefix.zero < .sigma 0 ∧
    ¬(QuantifierPrefix.sigma 0 ≤ .pi 0) ∧ ¬(QuantifierPrefix.pi 0 ≤ .sigma 0) := by
  refine ⟨by simp [QuantifierPrefix.lt_iff], ?_, ?_⟩ <;> simp [QuantifierPrefix.le_iff]

-- Prefix contraction versus alternation under `addExists` and `addForall`.
example : (QuantifierPrefix.sigma 1).addExists = .sigma 1 ∧
    (QuantifierPrefix.sigma 1).addForall = .pi 2 ∧
    (QuantifierPrefix.pi 0).dual = .sigma 0 := by
  simp

-- Semantic characterization of quantifier addition (including same-polarity contraction).
example (p : QuantifierPrefix) (R : List ℕ → Prop) (xs : List ℕ)
    (Z : Set ℕ) (S : ℕ × ℕ → Prop) (hS : p.IsClass Z S) :
    (p.addExists.Eval (fun l => R (p.expandExists l)) xs ↔ ∃ y, p.Eval R (y :: xs)) ∧
    (p.addForall.Eval (fun l => R (p.expandForall l)) xs ↔ ∀ y, p.Eval R (y :: xs)) ∧
    p.addExists.IsClass Z (fun x => ∃ y, S (x, y)) ∧
    p.addForall.IsClass Z (fun x => ∀ y, S (x, y)) :=
  ⟨by simp, by simp, hS.exists_nat, hS.forall_nat⟩

-- A concrete valid oracle-dependent Δ⁰₀ code querying whether `encode [x] ∈ Z`.
example (Z : Set ℕ) :
    let nf : NormalFormCode := ⟨.zero, 1, Code.oracle⟩
    nf.IsValid Z ∧ ∀ x : ℕ, nf.EvalList Z [x] ↔ encode [x] ∈ Z := by
  intro nf
  refine ⟨isValid_iff.2 fun l _ => ?_, fun x => ?_⟩
  · by_cases h : encode l ∈ Z
    · exact ⟨true, by simp [nf, h]⟩
    · exact ⟨false, by simp [nf, h]⟩
  · rw [evalList_iff, QuantifierPrefix.eval_zero, matrixHolds_iff]
    simp [nf, Set.indicator]

-- Valid codes combine effectively under `neg`, `and`, and `or`, satisfying exact semantics.
example (Z : Set ℕ) {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    (xs : List ℕ) (hxs : xs.length = nf₁.arity) :
    ((nf₁.and nf₂).neg.IsValid Z) ∧
    ((nf₁.and nf₂).neg.EvalList Z xs ↔ ¬(nf₁.EvalList Z xs ∧ nf₂.EvalList Z xs)) ∧
    ((nf₁.or nf₂).EvalList Z xs ↔ nf₁.EvalList Z xs ∨ nf₂.EvalList Z xs) := by
  have hand := h₁.and h₂ hq ha
  refine ⟨hand.neg, ?_, evalList_or h₁ h₂ hq ha hxs⟩
  rw [evalList_neg hand (by simpa using hxs), evalList_and h₁ h₂ hq ha hxs]

-- Double negation of `falseCode` is valid and remains identically false on tuples.
example (Z : Set ℕ) (p : QuantifierPrefix) (k : ℕ)
    (x : Fin (falseCode p k).neg.neg.arity → ℕ) :
    (falseCode p k).neg.neg.IsValid Z ∧ ¬(falseCode p k).neg.neg.Holds Z x := by
  have hf := isValid_falseCode Z p k
  refine ⟨hf.neg.neg, ?_⟩
  rw [holds_neg hf.neg, holds_neg hf]
  simp

-- Composite Boolean code transformations remain primitive recursive on encoded codes.
example : Primrec fun p : NormalFormCode × NormalFormCode => encode ((p.1.and p.2).neg) :=
  Primrec.encode.comp (primrec_neg.comp (primrec₂_and.comp Primrec.fst Primrec.snd))

-- Soundness: any valid normal-form code defines a predicate in its displayed pointclass.
example (Z : Set ℕ) {nf : NormalFormCode} (h : nf.IsValid Z) :
    nf.quantifiers.IsClass Z (nf.Holds Z) :=
  h.isClass_holds

-- Completeness: every Σ⁰₂ predicate on pairs is realized by a valid normal-form code.
example (Z : Set ℕ) (P : (Fin 2 → ℕ) → Prop) (hP : IsSigma Z 2 P) :
    ∃ nf : NormalFormCode, nf.quantifiers = .sigma 1 ∧ nf.arity = 2 ∧ nf.IsValid Z ∧
      ∀ x, nf.EvalList Z (List.ofFn x) ↔ P x := by
  simpa using isSigma_iff_exists_normalFormCode.1 hP

-- Exact Π⁰₂-completeness and undecidability of `NormalFormCode.IsValid Z`.
example (Z : Set ℕ) :
    IsPi Z 2 (NormalFormCode.IsValid Z) ∧
    OneOneReducible (· ∈ totality Z) (NormalFormCode.IsValid Z) ∧
    ¬IsSigma Z 2 (NormalFormCode.IsValid Z) ∧
    ¬ComputablePred (NormalFormCode.IsValid Z) :=
  ⟨isPi_two_isValid, oneOneReducible_totality_isValid,
    not_isSigma_two_isValid, not_computablePred_isValid⟩

-- Matrix-level characterizations and `QuantifierPrefix.eval_and_unpair_iff` / `eval_or_unpair_iff`.
example (Z : Set ℕ) {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity)
    (p : QuantifierPrefix) (R₁ R₂ : List ℕ → Prop) (xs₁ xs₂ xs : List ℕ) :
    (falseCode p nf₁.arity).matrix = Code.zero ∧
    nf₁.neg.matrix = Code.boolNot nf₁.matrix ∧
    (nf₁.neg.MatrixHolds Z l ↔ ¬nf₁.MatrixHolds Z l) ∧
    ((nf₁.and nf₂).MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∧
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth)) ∧
    ((nf₁.or nf₂).MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∨
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth)) ∧
    (p.Eval (fun m =>
        R₁ ((m.take p.depth).map (fun y => y.unpair.1) ++ xs₁) ∧
        R₂ ((m.take p.depth).map (fun y => y.unpair.2) ++ xs₂)) xs ↔
      p.Eval R₁ xs₁ ∧ p.Eval R₂ xs₂) ∧
    (p.Eval (fun m =>
        R₁ ((m.take p.depth).map (fun y => y.unpair.1) ++ xs₁) ∨
        R₂ ((m.take p.depth).map (fun y => y.unpair.2) ++ xs₂)) xs ↔
      p.Eval R₁ xs₁ ∨ p.Eval R₂ xs₂) :=
  ⟨matrix_falseCode p nf₁.arity, matrix_neg nf₁, h₁.matrixHolds_neg hl,
    matrixHolds_and h₁ h₂ hq ha hl, matrixHolds_or h₁ h₂ hq ha hl,
    QuantifierPrefix.eval_and_unpair_iff p R₁ R₂ xs₁ xs₂ xs,
    QuantifierPrefix.eval_or_unpair_iff p R₁ R₂ xs₁ xs₂ xs⟩
