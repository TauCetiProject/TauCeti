/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
import TauCeti.ModelTheory.Syntax

/-!
# Realization of first-order terms and closed bounded formulas

`FirstOrder.Language.Term.realize_congr_varFinsetLeft` says that a term over `α ⊕ β` has the same
realization under two valuations of `α` that agree on the variables `Term.varFinsetLeft` it
mentions. It is derived from Mathlib's `Term.realize_restrictVarLeft'`, since Mathlib has no
direct congruence lemma of this form.

`FirstOrder.Language.Sentence.realize_alls` and `FirstOrder.Language.Sentence.realize_exs`
characterize satisfaction of the universal and existential closures of a bounded formula with no
free variables as realization at every tuple or some tuple of bound variables, and
`FirstOrder.Language.BoundedFormula.evalAtConstants` and
`FirstOrder.Language.BoundedFormula.realize_evalAtConstants` evaluate those bound positions at the
adjoined constants of `L[[Fin n]]`.

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

namespace BoundedFormula

variable {L : Language} {n : ℕ}

/-- Convert a bounded formula with no free variables into a sentence of `L[[Fin n]]` evaluating
its bound positions at the adjoined constants. -/
def evalAtConstants (φ : L.BoundedFormula Empty n) : L[[Fin n]].Sentence :=
  Formula.equivSentence (φ.toFormula.relabel (Sum.elim Empty.elim id))

/-- Unfolding lemma for `BoundedFormula.evalAtConstants`. -/
theorem evalAtConstants_def (φ : L.BoundedFormula Empty n) :
    φ.evalAtConstants = Formula.equivSentence (φ.toFormula.relabel (Sum.elim Empty.elim id)) :=
  (rfl)

@[simp]
theorem evalAtConstants_falsum : (falsum : L.BoundedFormula Empty n).evalAtConstants = falsum := by
  simp only [evalAtConstants_def, toFormula, Formula.relabel_falsum, Formula.equivSentence_falsum]

@[simp]
theorem evalAtConstants_bot : (⊥ : L.BoundedFormula Empty n).evalAtConstants = ⊥ :=
  evalAtConstants_falsum

@[simp]
theorem evalAtConstants_imp (φ ψ : L.BoundedFormula Empty n) :
    (φ.imp ψ).evalAtConstants = φ.evalAtConstants.imp ψ.evalAtConstants := by
  simp only [evalAtConstants_def, toFormula, Formula.relabel_imp, Formula.equivSentence_imp]

@[simp]
theorem evalAtConstants_not (φ : L.BoundedFormula Empty n) :
    φ.not.evalAtConstants = φ.evalAtConstants.not := by
  rw [BoundedFormula.not, evalAtConstants_imp, evalAtConstants_bot, Formula.not, BoundedFormula.not]

@[simp]
theorem evalAtConstants_top : (⊤ : L.BoundedFormula Empty n).evalAtConstants = ⊤ :=
  evalAtConstants_not ⊥

@[simp]
theorem evalAtConstants_inf (φ ψ : L.BoundedFormula Empty n) :
    (φ ⊓ ψ).evalAtConstants = φ.evalAtConstants ⊓ ψ.evalAtConstants := by
  simp only [Min.min, evalAtConstants_not, evalAtConstants_imp]

@[simp]
theorem evalAtConstants_sup (φ ψ : L.BoundedFormula Empty n) :
    (φ ⊔ ψ).evalAtConstants = φ.evalAtConstants ⊔ ψ.evalAtConstants := by
  simp only [Max.max, evalAtConstants_not, evalAtConstants_imp]

@[simp]
theorem evalAtConstants_iff (φ ψ : L.BoundedFormula Empty n) :
    (φ.iff ψ).evalAtConstants = φ.evalAtConstants.iff ψ.evalAtConstants := by
  rw [BoundedFormula.iff, evalAtConstants_inf, evalAtConstants_imp, evalAtConstants_imp,
    Formula.iff, BoundedFormula.iff]

/-- A closed bounded formula evaluated at the adjoined constants of `L[[Fin n]]` holds in an
expansion iff the formula holds at the interpretations of those constants. -/
@[simp]
theorem realize_evalAtConstants {M : Type*} [L.Structure M] [L[[Fin n]].Structure M]
    [(L.lhomWithConstants (Fin n)).IsExpansionOn M] (φ : L.BoundedFormula Empty n) :
    M ⊨ φ.evalAtConstants ↔ φ.Realize Empty.elim fun i => (L.con i : M) := by
  rw [evalAtConstants_def, Formula.realize_equivSentence, Formula.realize_relabel,
    BoundedFormula.realize_toFormula, Function.comp_assoc, Sum.elim_comp_inl,
    Function.comp_assoc, Sum.elim_comp_inr, Function.comp_id,
    Subsingleton.elim ((fun i : Fin n => (L.con i : M)) ∘ Empty.elim) Empty.elim]

end BoundedFormula

end Language

end FirstOrder
