/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Complexity

/-!
# Complexity and realization of first-order formulas

Mathlib's `FirstOrder.Language.BoundedFormula.iSup` and `FirstOrder.Language.BoundedFormula.iInf`
form the disjunction and conjunction of a finite family of formulas. This file shows that both are
quantifier-free when every member of the family is.

In an algebraic language, every atomic formula holds in a subsingleton structure: atomic
formulas can only assert equality of terms.
-/

public section

namespace FirstOrder.Language.BoundedFormula.IsQF

variable {L : Language} {α β : Type*} {n : ℕ}

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
theorem iSup [Finite β] {f : β → L.BoundedFormula α n} (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iSup f).IsQF := by
  -- Mirror the Fintype.ofFinite instance chosen by BoundedFormula.iSup;
  -- its finite-connective goal then reduces to the corresponding list fold.
  let _ := Fintype.ofFinite β
  suffices ∀ l : List β, (l.map f).foldr (· ⊔ ·) ⊥ |>.IsQF from this _
  intro l
  induction l with
  | nil => exact isQF_bot
  | cons b l ih => exact (hf b).sup ih

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
theorem iInf [Finite β] {f : β → L.BoundedFormula α n} (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iInf f).IsQF := by
  -- Mirror the Fintype.ofFinite instance chosen by BoundedFormula.iInf;
  -- its finite-connective goal then reduces to the corresponding list fold.
  let _ := Fintype.ofFinite β
  suffices ∀ l : List β, (l.map f).foldr (· ⊓ ·) ⊤ |>.IsQF from this _
  intro l
  induction l with
  | nil => exact top
  | cons b l ih => exact (hf b).inf ih

end FirstOrder.Language.BoundedFormula.IsQF

namespace FirstOrder.Language.BoundedFormula

open FirstOrder

/-- Every atomic formula over an algebraic language holds in a subsingleton structure. -/
theorem realize_of_isAtomic_subsingleton {L : Language} [L.IsAlgebraic]
    {G α : Type*} [Subsingleton G] [L.Structure G]
    {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic)
    (v : α → G) (xs : Fin n → G) : φ.Realize v xs := by
  cases hφ with
  | equal _ _ => exact Subsingleton.elim _ _
  | rel r _ => exact isEmptyElim r

end FirstOrder.Language.BoundedFormula
