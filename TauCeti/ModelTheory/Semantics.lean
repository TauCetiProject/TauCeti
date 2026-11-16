/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# Realization of first-order terms and universally closed formulas

`FirstOrder.Language.Term.realize_congr_varFinsetLeft` says that a term over `α ⊕ β` has the same
realization under two valuations of `α` that agree on the variables `Term.varFinsetLeft` it
mentions. It is derived from Mathlib's `Term.realize_restrictVarLeft'`, since Mathlib has no
direct congruence lemma of this form.

`FirstOrder.Language.Sentence.realize_alls` characterizes satisfaction of the universal closure
of a bounded formula with no free variables as realization at every tuple of bound variables.

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

/-- A universally closed sentence holds iff its body holds at every tuple. -/
@[simp]
theorem Sentence.realize_alls {L : Language} {M : Type*} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) :
    M ⊨ φ.alls ↔ ∀ a : Fin n → M, φ.Realize Empty.elim a := by
  rw [Sentence.Realize, Subsingleton.elim (default : Empty → M) Empty.elim,
    BoundedFormula.realize_alls]

/-- For every term `t` in one bound variable, the sentence `∃ x, t(x) = t(x)` holds exactly in
the nonempty structures. The case `t = x` is the sentence `∃ x, x = x`. -/
@[simp]
theorem Sentence.realize_ex_bdEqual_self_iff {L : Language} {M : Type*} [L.Structure M]
    (t : L.Term (Empty ⊕ Fin 1)) : M ⊨ (∃' (t =' t) : L.Sentence) ↔ Nonempty M := by
  simp [Sentence.Realize, Formula.Realize]

end Language

end FirstOrder
