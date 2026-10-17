/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.FreeVariables
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
* a countable conjunction can have infinite free-variable support;
* changing a valuation outside support preserves truth, also under a quantifier.
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

/-! ### Free-variable support -/

namespace TauCeti

open TauCeti.BoundedFormulaInf

attribute [local instance] Language.emptyStructure

-- Comparing every free coordinate to a bound variable gives infinite support,
-- even after quantifying that bound variable.
example : freeVarSupport
    (all (iInf fun i : ℕ => equal (.var (.inl i)) (.var (.inr 0))) :
      Language.empty.BoundedFormulaω ℕ 0) = Set.univ := by
  ext i
  simp [Term.varFinsetLeft]

-- The conjunction is true of the zero valuation at zero.
example : (iInf fun i : ℕ => equal (.var (.inl i)) (.var (.inr 0)) :
    Language.empty.BoundedFormulaω ℕ 1).Realize (M := ℕ) (fun _ => 0) (fun _ => 0) := by
  simp

-- It is false of the identity valuation at zero.
example : ¬ (iInf fun i : ℕ => equal (.var (.inl i)) (.var (.inr 0)) :
    Language.empty.BoundedFormulaω ℕ 1).Realize (M := ℕ) id (fun _ => 0) := by
  simp only [realize_iInf, realize_equal, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, id_eq]
  exact fun h => Nat.one_ne_zero (h 1)

-- An empty branching carrier contributes no free variables.
example {L : Language.{u, v}} {α : Type u'} {n : ℕ} :
    freeVarSupport (iInf Empty.elim : L.BoundedFormulaInf Empty α n) = ∅ := by
  simp

-- Finitary support stays finite even when the unused branching carrier is large.
example {L : Language.{u, v}} {α : Type u'} {n : ℕ} (φ : L.BoundedFormula α n) :
    (freeVarSupport (φ.toInf (ι := Type))).Finite :=
  finite_freeVarSupport_toInf φ

-- The quantified equation uses only free variable zero. All other coordinates may change.
example {v₁ v₂ : ℕ → ℕ} (h : v₁ 0 = v₂ 0) :
    (all (equal (.var (.inl 0)) (.var (.inr 0))) :
      Language.empty.BoundedFormulaω ℕ 0).Realize v₁ Fin.elim0 ↔
    (all (equal (.var (.inl 0)) (.var (.inr 0))) :
      Language.empty.BoundedFormulaω ℕ 0).Realize v₂ Fin.elim0 := by
  apply realize_congr_freeVarSupport
  simpa [Term.varFinsetLeft] using h

end TauCeti
