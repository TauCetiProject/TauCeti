/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.CodedConnectives
import Mathlib.ModelTheory.Graph
import Mathlib.Tactic.FinCases

/-!
# Regression examples: infinitary syntax and realization

These examples exercise the infinitary syntax and its realization from a downstream module,
through public statements only:

* a finitary formula keeps its meaning under the embedding `toInf`, at every carrier;
* an `ℕ`-indexed conjunction is realized exactly when every conjunct is;
* over the empty carrier, a conjunction is true and a disjunction is false;
* a nullary relation on the empty structure takes the value the structure assigns it;
* in nested quantifiers, each quantifier binds the last bound-variable slot;
* coded conjunctions and disjunctions realize as the conjunction and disjunction of their branches,
  for an empty source carrier, with unused target indices, and with a decoder that sends several
  target indices to the same branch;
* `simp` uses a formula- or sentence-level hypothesis, or a default-priority formula-level rewrite
  rule, before descending to bounded realization.
-/

universe u v u' uι w

open FirstOrder FirstOrder.Language BoundedFormulaInf

/-! ### The finitary embedding -/

-- A finitary formula keeps its meaning in the infinitary syntax.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M) :
    φ.toOmega.Realize v xs ↔ φ.Realize v xs :=
  BoundedFormula.realize_toInf φ v xs

-- The embedding is carrier-generic: here at a carrier in a higher universe.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M) :
    (φ.toInf (ι := Type)).Realize v xs ↔ φ.Realize v xs :=
  BoundedFormula.realize_toInf φ v xs

/-! ### Infinitary connectives -/

-- An `ℕ`-indexed conjunction is realized exactly when every conjunct is.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φs : ℕ → L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    (iInf φs).Realize v xs ↔ ∀ k, (φs k).Realize v xs := by
  simp only [realize_iInf]

-- Over the empty carrier, the conjunction is true and the disjunction is false.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (v : α → M) (xs : Fin n → M) :
    (iInf Empty.elim : L.BoundedFormulaInf Empty α n).Realize v xs := by
  simp

example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (v : α → M) (xs : Fin n → M) :
    ¬(iSup Empty.elim : L.BoundedFormulaInf Empty α n).Realize v xs := by
  simp

/-! ### A nullary relation on the empty structure -/

-- The atom of a nullary relation symbol is evaluated on the empty structure by the structure's
-- interpretation of the symbol, not vacuously. A universal sentence holds vacuously there.
example (b : Prop) :
    letI L₀ : Language := ⟨fun _ => Empty, fun n => if n = 0 then Unit else Empty⟩
    letI : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => b⟩
    SentenceInf.Realize
        (rel (L := L₀) (l := 0) (cast (by simp [L₀]) ()) Fin.elim0 : L₀.SentenceInf ℕ) Empty ↔
      b := by
  simp

example {L : Language.{u, v}} [L.Structure Empty] :
    SentenceInf.Realize (all ⊥ : L.SentenceInf ℕ) Empty := by
  simp

/-! ### Nested quantifiers -/

-- Each quantifier binds the last slot: in `∀ ∃ adj(&0, &1)` the outer quantifier binds `&0` and
-- the inner one binds `&1`.
example {M : Type w} [Language.graph.Structure M] :
    SentenceInf.Realize
        (all (rel Language.adj ![Term.var (Sum.inr 0), Term.var (Sum.inr 1)]).ex :
          Language.graph.SentenceInf ℕ) M ↔
      ∀ x : M, ∃ y : M, Structure.RelMap Language.adj ![x, y] := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all, realize_ex, realize_rel]
  refine forall_congr' fun x => exists_congr fun y => Iff.of_eq (congrArg _ (funext fun i => ?_))
  fin_cases i <;> simp [Fin.snoc]

/-! ### Coded connectives -/

-- Over an empty source carrier, the coded conjunction is true and the coded disjunction is false,
-- although the target carrier `ℕ` is not empty.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (v : α → M) (xs : Fin n → M) :
    (iInfAlong (TauCeti.IndexCoding.ofEncodable Empty) Empty.elim :
      L.BoundedFormulaInf ℕ α n).Realize v xs := by
  simp

example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (v : α → M) (xs : Fin n → M) :
    ¬(iSupAlong (TauCeti.IndexCoding.ofEncodable Empty) Empty.elim :
      L.BoundedFormulaInf ℕ α n).Realize v xs := by
  simp

-- The target indices `Sum.inr k` decode to nothing; their padding branches do not change the
-- realization of a single coded branch.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormulaInf (Unit ⊕ ℕ) α n) (v : α → M) (xs : Fin n → M) :
    (iInfAlong (TauCeti.IndexCoding.sumInl Unit ℕ) fun _ => φ).Realize v xs ↔ φ.Realize v xs := by
  simp

example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormulaInf (Unit ⊕ ℕ) α n) (v : α → M) (xs : Fin n → M) :
    (iSupAlong (TauCeti.IndexCoding.sumInl Unit ℕ) fun _ => φ).Realize v xs ↔ φ.Realize v xs := by
  simp

-- A decoder may send several target indices to the same branch: here every even index decodes to
-- `false` and every odd index to `true`. The coded connectives still realize as the conjunction and
-- disjunction over `Bool`.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φs : Bool → L.BoundedFormulaInf ℕ α n) (v : α → M) (xs : Fin n → M) :
    letI c : TauCeti.IndexCoding Bool ℕ :=
      ⟨fun b => if b then 1 else 0, fun k => some (k % 2 == 1), by decide⟩
    ((iInfAlong c φs).Realize v xs ↔ (φs false).Realize v xs ∧ (φs true).Realize v xs) ∧
      ((iSupAlong c φs).Realize v xs ↔ (φs false).Realize v xs ∨ (φs true).Realize v xs) := by
  simp [Bool.forall_bool, Bool.exists_bool]

/-! ### Formula- and sentence-level facts in `simp` -/

-- The bridges to bounded realization are low-priority simp lemmas, so a hypothesis stated at the
-- formula or sentence level is used as stated rather than pre-empted.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M]
    (φ : L.FormulaInf ι α) (v : α → M) (h : φ.Realize v) : φ.Realize v ∧ True := by
  simp [h]

example {L : Language.{u, v}} {ι : Type uι} {M : Type w} [L.Structure M]
    (φ : L.SentenceInf ι) (h : φ.Realize M) : φ.Realize M ∧ True := by
  simp [h]

-- A formula-level rewrite rule at default priority fires before the fallback, so a downstream
-- library can state such rules without raising their priority.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M]
    (φ ψ : L.FormulaInf ι α) (v : α → M) (h : φ.Realize v) :
    (φ ⊓ ψ).Realize v ↔ ψ.Realize v := by
  have key : ∀ φ ψ : L.FormulaInf ι α, (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v :=
    fun _ _ => by simp only [FormulaInf.realize_def, realize_inf]
  simp [key, h]

-- With no formula-level fact in play, `simp` still reaches bounded realization through the
-- fallback.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M]
    (φ : L.FormulaInf ι α) (v : α → M) : (φ ⊓ ⊤).Realize v ↔ φ.Realize v := by
  simp
