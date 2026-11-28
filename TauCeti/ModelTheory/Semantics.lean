/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# Realization of first-order terms and closed formulas

`FirstOrder.Language.Term.realize_congr_varFinsetLeft` says that a term over `α ⊕ β` has the same
realization under two valuations of `α` that agree on the variables `Term.varFinsetLeft` it
mentions. It is derived from Mathlib's `Term.realize_restrictVarLeft'`, since Mathlib has no
direct congruence lemma of this form. In the same way,
`FirstOrder.Language.BoundedFormula.realize_congr_freeVarFinset` says that a bounded formula has
the same realization under two valuations that agree on its free variables
`BoundedFormula.freeVarFinset`; it is derived from Mathlib's
`BoundedFormula.realize_restrictFreeVar'`. In particular, changing a valuation at a variable that
is not free does not change the realization
(`FirstOrder.Language.BoundedFormula.realize_update_of_notMem_freeVarFinset`).

`FirstOrder.Language.Formula.realize_all` characterizes realization of a formula `∀'φ`, with `φ`
in one bound variable, as realization of `φ` at every value of the bound variable.

`FirstOrder.Language.Sentence.realize_alls` characterizes satisfaction of the universal closure
of a bounded formula with no free variables as realization at every tuple of bound variables, and
`FirstOrder.Language.Sentence.realize_exs` characterizes satisfaction of its existential closure
as realization at some tuple.

`FirstOrder.Language.Sentence.realize_ex_bdEqual_self_iff` says that a sentence `∃ x, t = t`,
such as `∃ x, x = x`, holds exactly in the nonempty structures.
-/

public section

namespace FirstOrder

namespace Language

namespace Term

variable {L : Language} {α β M : Type*} [L.Structure M]

/-- A term over `α ⊕ β` has the same realization under two valuations of `α` that agree on the
variables `Term.varFinsetLeft` of `α` it mentions. -/
theorem realize_congr_varFinsetLeft [DecidableEq α] {t : L.Term (α ⊕ β)} {v v' : α → M}
    (h : Set.EqOn v v' t.varFinsetLeft) (xs : β → M) :
    t.realize (Sum.elim v xs) = t.realize (Sum.elim v' xs) := by
  rw [← realize_restrictVarLeft' subset_rfl (v := v),
    ← realize_restrictVarLeft' subset_rfl (v := v'), ← Set.domRestrict_eq, ← Set.domRestrict_eq,
    Set.domRestrict_eq_domRestrict_iff.2 h]

end Term

namespace BoundedFormula

variable {L : Language} {α M : Type*} [L.Structure M]

/-- A bounded formula has the same realization under two valuations that agree on its free
variables `BoundedFormula.freeVarFinset`. -/
theorem realize_congr_freeVarFinset [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n}
    {v v' : α → M} (h : Set.EqOn v v' φ.freeVarFinset) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize v' xs := by
  rw [← realize_restrictFreeVar' subset_rfl (v := v),
    ← realize_restrictFreeVar' subset_rfl (v := v')]
  rw [show v ∘ Subtype.val = v' ∘ Subtype.val from funext fun x => h x.property]

/-- Changing a valuation at a variable that does not occur free in a bounded formula does not
change its realization. -/
theorem realize_update_of_notMem_freeVarFinset [DecidableEq α] {n : ℕ}
    {φ : L.BoundedFormula α n} {a : α} (ha : a ∉ φ.freeVarFinset) (v : α → M) (m : M)
    (xs : Fin n → M) : φ.Realize (Function.update v a m) xs ↔ φ.Realize v xs :=
  realize_congr_freeVarFinset (fun x hx => Function.update_of_ne
    (fun hxa : x = a => ha (hxa ▸ hx)) m v) xs

end BoundedFormula

/-- A formula `∀'φ`, with `φ` in one bound variable, holds exactly when `φ` holds at every value
of the bound variable. -/
@[simp]
theorem Formula.realize_all {L : Language} {α M : Type*} [L.Structure M]
    {φ : L.BoundedFormula α 1} {v : α → M} : Formula.Realize φ.all v ↔ ∀ a, φ.Realize v ![a] := by
  rw [Formula.Realize, BoundedFormula.realize_all, Subsingleton.elim default ![] ]
  simp

/-- A universally closed sentence holds iff its body holds at every tuple. -/
@[simp]
theorem Sentence.realize_alls {L : Language} {M : Type*} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) :
    M ⊨ φ.alls ↔ ∀ a : Fin n → M, φ.Realize Empty.elim a := by
  rw [Sentence.Realize, Subsingleton.elim (default : Empty → M) Empty.elim,
    BoundedFormula.realize_alls]

/-- An existentially closed sentence holds iff its body holds at some tuple. -/
@[simp]
theorem Sentence.realize_exs {L : Language} {M : Type*} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) :
    M ⊨ φ.exs ↔ ∃ a : Fin n → M, φ.Realize Empty.elim a := by
  rw [Sentence.Realize, Subsingleton.elim (default : Empty → M) Empty.elim,
    BoundedFormula.realize_exs]

/-- For every term `t` in one bound variable, the sentence `∃ x, t(x) = t(x)` holds exactly in
the nonempty structures. The case `t = x` is the sentence `∃ x, x = x`. -/
@[simp]
theorem Sentence.realize_ex_bdEqual_self_iff {L : Language} {M : Type*} [L.Structure M]
    (t : L.Term (Empty ⊕ Fin 1)) : M ⊨ (∃' (t =' t) : L.Sentence) ↔ Nonempty M := by
  simp [Sentence.Realize, Formula.Realize]

end Language

end FirstOrder
