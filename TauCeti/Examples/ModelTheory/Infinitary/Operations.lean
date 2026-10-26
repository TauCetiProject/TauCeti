/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.Operations
import Mathlib.ModelTheory.Semantics

/-!
# Regression examples: bound-variable relabelling and weakening

These examples exercise bound-variable relabelling and weakening from a downstream module, through
public statements only:

* weakening strictly under a quantifier keeps the quantified variable bound by its quantifier, at
  the new last slot;
* the same holds for nested quantifiers;
* relabelling along a non-injective slot map identifies bound variables;
* weakening a finitary formula has the meaning of Mathlib's `BoundedFormula.liftAt` inserting the
  new slots after the existing ones.
-/

universe u v u' uι w

open FirstOrder FirstOrder.Language BoundedFormulaInf

-- Weakening `∀ x₁, x₀ = x₁` from one to three slots: the quantifier still binds the variable it
-- quantifies, which now sits at the last slot, not at slot `1` of the valuation.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M]
    (v : α → M) (xs : Fin 3 → M) :
    (castLE (by omega : 1 ≤ 3)
      (all (equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))) : L.BoundedFormulaInf ι α 1)
      ).Realize v xs ↔ ∀ y : M, xs 0 = y := by
  rw [realize_castLE]
  simp [Fin.snoc]

-- Nested quantifiers: weakening `∀ x₁, ∃ x₂, x₁ = x₂` from one to four slots.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M]
    (v : α → M) (xs : Fin 4 → M) :
    (castLE (by omega : 1 ≤ 4)
      (all (equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).ex :
        L.BoundedFormulaInf ι α 1)).Realize v xs ↔ ∀ y : M, ∃ z : M, y = z := by
  rw [realize_castLE]
  simp [Fin.snoc]

-- Relabelling along a non-injective slot map identifies bound variables: `x₀ = x₁` becomes
-- `x₀ = x₀`, which always holds.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M]
    (v : α → M) (xs : Fin 1 → M) :
    (mapBound (fun _ : Fin 2 => (0 : Fin 1))
      (equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) : L.BoundedFormulaInf ι α 2)
      ).Realize v xs := by
  simp

-- Weakening a finitary formula by `k` slots has the meaning of Mathlib's `liftAt` inserting the
-- `k` new slots after the existing `n`.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M] {n k : ℕ}
    (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin (n + k) → M) :
    (castLE (Nat.le_add_right n k) (φ.toInf (ι := ι))).Realize v xs ↔
      (φ.liftAt k n).Realize v xs := by
  rw [realize_castLE, BoundedFormula.realize_toInf, BoundedFormula.realize_liftAt le_rfl]
  congr! 1
  funext i
  simp only [Function.comp_apply, i.isLt, ↓reduceIte]
  rfl
