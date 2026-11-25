/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.SequentCalculus.Instance
import Mathlib.Tactic.FinCases

/-!
# Regression examples: instances and depth of formulas

These examples exercise the instances and the depth of first-order formulas from a downstream
module, through public statements only:

* `⊥` and atoms have depth `0`, an implication of atoms has depth `1`, and the defined connectives
  cost depth: `¬¬p` and `p ⊔ q`, which is `(p → ⊥) → q`, have depth `2`;
* instantiating the bound position of `R(x₀, #0)` at `f(x₁)` gives `R(x₀, f(x₁))`, leaving the free
  variable `x₀` alone;
* a term at a bound position that does not occur in the formula contributes no free variable: the
  instance of `P(x₀)`, with one vacuous bound position, at `x₁` has `x₀` as its only free variable.
-/

open FirstOrder FirstOrder.Language BoundedFormula

variable {L : Language} {n : ℕ}

/-! ### Depth -/

example : (⊥ : L.BoundedFormula ℕ n).depth = 0 := depth_bot

example {p q : L.BoundedFormula ℕ n} (hp : p.IsAtomic) (hq : q.IsAtomic) :
    (p.imp q).depth = 1 := by
  simp [hp.depth_eq_zero, hq.depth_eq_zero]

example {p : L.BoundedFormula ℕ n} (hp : p.IsAtomic) : p.not.not.depth = 2 := by
  simp [hp.depth_eq_zero]

example {p q : L.BoundedFormula ℕ n} (hp : p.IsAtomic) (hq : q.IsAtomic) :
    (p ⊔ q).depth = 2 ∧ ((p.imp ⊥).imp q).depth = 2 := by
  simp [hp.depth_eq_zero, hq.depth_eq_zero]

/-! ### Instances -/

-- The bound position of `R(x₀, #0)` is replaced by `f(x₁)`; the free variable `x₀` is kept.
example (R : L.Relations 2) (f : L.Functions 1) :
    (R.boundedFormula₂ (Term.var (Sum.inl 0)) (&0)).inst ![f.apply₁ (Term.var 1)] =
      R.formula₂ (Term.var 0) (f.apply₁ (Term.var 1)) := by
  simp only [Relations.boundedFormula₂, Relations.formula₂, inst_boundedFormula]
  congr 1
  funext i
  fin_cases i <;> rfl

-- An instance is realized with the values of the terms at the bound positions.
example {M : Type*} [L.Structure M] (R : L.Relations 2) (f : L.Functions 1) (v : ℕ → M) :
    ((R.boundedFormula₂ (Term.var (Sum.inl 0)) (&0)).inst ![f.apply₁ (Term.var 1)]).Realize v ↔
      Structure.RelMap R ![v 0, Structure.funMap f ![v 1] ] := by
  simp only [realize_inst, Relations.boundedFormula₂, realize_rel]
  congr! 1
  funext i
  fin_cases i
  · rfl
  · simp only [Functions.apply₁, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp only [Term.realize_func, Function.comp_apply, Term.realize_var, Sum.elim_inr]
    congr 1
    funext j
    fin_cases j
    rfl

-- The bound position of `P(x₀)` is vacuous, so the term `x₁` put there is not a free variable of
-- the instance.
example (P : L.Relations 1) :
    ((P.boundedFormula₁ (Term.var (Sum.inl 0)) : L.BoundedFormula ℕ 1).inst
      ![Term.var 1]).freeVarFinset = {0} := by
  ext x
  rw [mem_freeVarFinset_inst]
  simp [Relations.boundedFormula₁, Relations.boundedFormula, Relations.formula]
