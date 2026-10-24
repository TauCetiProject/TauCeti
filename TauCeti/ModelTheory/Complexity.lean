/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Complexity

/-!
# Finite connectives of quantifier-free formulas

Mathlib's `FirstOrder.Language.BoundedFormula.iSup` and `FirstOrder.Language.BoundedFormula.iInf`
form the disjunction and conjunction of a finite family of formulas. This file shows that both are
quantifier-free when every member of the family is.
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
