/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card

/-!
# Propositional formulas and negation normal form

This file introduces propositional formulas over an arbitrary type `V` of variables, built from
variables, the two constants and the connectives `neg`, `and` and `or`, together with their
semantics under an assignment `τ : V → Bool`, their variables and subformulas, and the counts
(size, number of subformulas, occurrences of atoms and of binary connectives) that measure the
cost of translating a formula into conjunctive normal form.

The **negation normal form** pushes negations inwards by the De Morgan laws, removes double
negations and replaces a negated constant by the other constant. It is computed by a map
`PropForm.toNNF b` with a polarity `b : Bool`: `φ.toNNF true` is equivalent to `φ` and
`φ.toNNF false` to its negation, and the negation normal form of `φ` is `φ.toNNF true`.

Mathlib and Lean core have no type of propositional formulas over a type of variables. The
nearest types serve tactics and solvers: `Mathlib.Tactic.ITauto.IProp` has variables indexed by
`ℕ` and the connectives of intuitionistic logic, `Sat.Fmla` (for the `lrat_proof` command) is a
list of clauses, `Std.Tactic.BVDecide.BVLogicalExpr` has bit-vector predicates as atoms and `xor`,
`beq` and `ite` gates, and `Std.Sat.AIG` is an and-inverter graph. Tau Ceti's
`FirstOrder.Language.BoundedFormula.PropRealize` reads first-order formulas propositionally.

## Main definitions

* `TauCeti.Propositional.PropForm V`: propositional formulas over the variables `V`.
* `TauCeti.Propositional.PropForm.eval τ φ`: the truth value of `φ` under the assignment `τ`.
* `TauCeti.Propositional.PropForm.size φ`: the number of occurrences of constants and connectives.
* `TauCeti.Propositional.PropForm.vars φ`, `TauCeti.Propositional.PropForm.subformulas φ`: the
  variables and the subformulas of `φ`, as finite sets.
* `TauCeti.Propositional.PropForm.Satisfiable`, `TauCeti.Propositional.PropForm.Equivalent`,
  `TauCeti.Propositional.PropForm.Equisatisfiable`: satisfiability of a formula, and equivalence
  and equisatisfiability of two formulas.
* `TauCeti.Propositional.PropForm.toNNF b φ`, `TauCeti.Propositional.PropForm.nnf φ`: the
  negation normal form of `φ` (for `b = true`) or of its negation (for `b = false`).
* `TauCeti.Propositional.PropForm.IsNNF φ`: `neg` occurs in `φ` only in front of variables.
* `TauCeti.Propositional.PropForm.numAtoms φ`,
  `TauCeti.Propositional.PropForm.numBinaryConnectives φ`: the number of occurrences of
  variables and constants, and of `and` and `or`.

## Main results

* `TauCeti.Propositional.PropForm.eval_congr`: the truth value of a formula depends only on the
  values of the assignment at its variables.
* `TauCeti.Propositional.PropForm.card_subformulas_le`: a formula has at most `size φ + m`
  subformulas, where `m` is the number of its distinct variables.
* `TauCeti.Propositional.PropForm.subformulas_subset_of_mem`: a subformula of a subformula is a
  subformula; `TauCeti.Propositional.PropForm.mem_subformulas_of_neg_mem` and the four lemmas
  `TauCeti.Propositional.PropForm.mem_subformulas_of_and_mem_left` (and `_right`, and the `or`
  versions) say that the set of subformulas is closed under taking immediate subformulas.
* `TauCeti.Propositional.PropForm.eval_toNNF`: `φ.toNNF b` evaluates to `true` exactly when `φ`
  evaluates to `b`.
* `TauCeti.Propositional.PropForm.equivalent_nnf`,
  `TauCeti.Propositional.PropForm.isNNF_nnf`: the negation normal form of `φ` is equivalent to
  `φ` and is in negation normal form.
* `TauCeti.Propositional.PropForm.numBinaryConnectives_nnf`,
  `TauCeti.Propositional.PropForm.numAtoms_nnf`: the negation normal form has as many
  occurrences of `and` and `or`, and as many occurrences of variables and constants, as `φ`.
* `TauCeti.Propositional.PropForm.numAtoms_eq_numBinaryConnectives_add_one`: a formula has one
  more occurrence of atoms than of binary connectives.
-/

public section

namespace TauCeti.Propositional

/-- **Propositional formulas** over the variables `V`, built from variables and the constants
`tru` and `fls` by negation, conjunction and disjunction. -/
inductive PropForm (V : Type*) : Type _
  /-- The variable `v`. -/
  | var (v : V)
  /-- The constant true. -/
  | tru
  /-- The constant false. -/
  | fls
  /-- The negation of a formula. -/
  | neg (φ : PropForm V)
  /-- The conjunction of two formulas. -/
  | and (φ ψ : PropForm V)
  /-- The disjunction of two formulas. -/
  | or (φ ψ : PropForm V)
  deriving DecidableEq

namespace PropForm

variable {V : Type*}

/-! ### Semantics and size -/

/-- The **truth value** of a formula under the assignment `τ : V → Bool`. -/
def eval (τ : V → Bool) : PropForm V → Bool
  | var v => τ v
  | tru => true
  | fls => false
  | neg φ => !eval τ φ
  | and φ ψ => eval τ φ && eval τ ψ
  | or φ ψ => eval τ φ || eval τ ψ

/-- The **size** of a formula: the number of occurrences of constants and connectives. A variable
has size `0`. -/
def size : PropForm V → ℕ
  | var _ => 0
  | tru => 1
  | fls => 1
  | neg φ => size φ + 1
  | and φ ψ => size φ + size ψ + 1
  | or φ ψ => size φ + size ψ + 1

variable (τ : V → Bool) (v : V) (φ ψ : PropForm V)

/-- A variable evaluates to its value. -/
@[simp]
theorem eval_var : (var v).eval τ = τ v := (rfl)

/-- The constant `tru` evaluates to `true`. -/
@[simp]
theorem eval_tru : (tru : PropForm V).eval τ = true := (rfl)

/-- The constant `fls` evaluates to `false`. -/
@[simp]
theorem eval_fls : (fls : PropForm V).eval τ = false := (rfl)

/-- A negation evaluates to the negated value. -/
@[simp]
theorem eval_neg : (neg φ).eval τ = !φ.eval τ := (rfl)

/-- A conjunction evaluates to the conjunction of the values. -/
@[simp]
theorem eval_and : (and φ ψ).eval τ = (φ.eval τ && ψ.eval τ) := (rfl)

/-- A disjunction evaluates to the disjunction of the values. -/
@[simp]
theorem eval_or : (or φ ψ).eval τ = (φ.eval τ || ψ.eval τ) := (rfl)

/-- A variable has size `0`. -/
@[simp]
theorem size_var : (var v).size = 0 := (rfl)

/-- The constant `tru` has size `1`. -/
@[simp]
theorem size_tru : (tru : PropForm V).size = 1 := (rfl)

/-- The constant `fls` has size `1`. -/
@[simp]
theorem size_fls : (fls : PropForm V).size = 1 := (rfl)

/-- A negation adds `1` to the size. -/
@[simp]
theorem size_neg : (neg φ).size = φ.size + 1 := (rfl)

/-- A conjunction adds `1` to the sum of the sizes. -/
@[simp]
theorem size_and : (and φ ψ).size = φ.size + ψ.size + 1 := (rfl)

/-- A disjunction adds `1` to the sum of the sizes. -/
@[simp]
theorem size_or : (or φ ψ).size = φ.size + ψ.size + 1 := (rfl)

/-! ### Satisfiability, equivalence and equisatisfiability -/

/-- A formula is **satisfiable** when it evaluates to `true` under some assignment. -/
def Satisfiable (φ : PropForm V) : Prop := ∃ τ, φ.eval τ = true

/-- Two formulas are **equivalent** when they evaluate equally under every assignment. -/
def Equivalent (φ ψ : PropForm V) : Prop := ∀ τ, φ.eval τ = ψ.eval τ

/-- Two formulas are **equisatisfiable** when one is satisfiable exactly when the other is. -/
def Equisatisfiable (φ ψ : PropForm V) : Prop := φ.Satisfiable ↔ ψ.Satisfiable

variable {φ ψ} {χ : PropForm V}

/-- A formula is satisfiable when it evaluates to `true` under some assignment. -/
theorem satisfiable_iff : φ.Satisfiable ↔ ∃ τ, φ.eval τ = true := Iff.rfl

/-- Two formulas are equivalent when they evaluate equally under every assignment. -/
theorem equivalent_iff : φ.Equivalent ψ ↔ ∀ τ, φ.eval τ = ψ.eval τ := Iff.rfl

/-- Two formulas are equisatisfiable when one is satisfiable exactly when the other is. -/
theorem equisatisfiable_iff : φ.Equisatisfiable ψ ↔ (φ.Satisfiable ↔ ψ.Satisfiable) := Iff.rfl

/-- Every formula is equivalent to itself. -/
@[refl]
theorem Equivalent.refl (φ : PropForm V) : φ.Equivalent φ := fun _ ↦ rfl

/-- Equivalence of formulas is symmetric. -/
@[symm]
theorem Equivalent.symm (h : φ.Equivalent ψ) : ψ.Equivalent φ := fun τ ↦ (h τ).symm

/-- Equivalence of formulas is transitive. -/
@[trans]
theorem Equivalent.trans (h : φ.Equivalent ψ) (h' : ψ.Equivalent χ) : φ.Equivalent χ :=
  fun τ ↦ (h τ).trans (h' τ)

/-- Equivalent formulas are equisatisfiable. -/
theorem Equivalent.equisatisfiable (h : φ.Equivalent ψ) : φ.Equisatisfiable ψ := by
  simp only [equisatisfiable_iff, satisfiable_iff, h _]

/-! ### Variables and subformulas -/

section DecidableEq

variable [DecidableEq V]

/-- The finite set of **variables** that occur in a formula. -/
def vars : PropForm V → Finset V
  | var v => {v}
  | tru => ∅
  | fls => ∅
  | neg φ => vars φ
  | and φ ψ => vars φ ∪ vars ψ
  | or φ ψ => vars φ ∪ vars ψ

/-- The finite set of **subformulas** of a formula, the formula itself included. -/
def subformulas : PropForm V → Finset (PropForm V)
  | var v => {var v}
  | tru => {tru}
  | fls => {fls}
  | neg φ => insert (neg φ) (subformulas φ)
  | and φ ψ => insert (and φ ψ) (subformulas φ ∪ subformulas ψ)
  | or φ ψ => insert (or φ ψ) (subformulas φ ∪ subformulas ψ)

variable (φ ψ)

/-- The only variable of `var v` is `v`. -/
@[simp]
theorem vars_var : (var v).vars = {v} := (rfl)

/-- The constant `tru` has no variables. -/
@[simp]
theorem vars_tru : (tru : PropForm V).vars = ∅ := (rfl)

/-- The constant `fls` has no variables. -/
@[simp]
theorem vars_fls : (fls : PropForm V).vars = ∅ := (rfl)

/-- A negation has the variables of the negated formula. -/
@[simp]
theorem vars_neg : (neg φ).vars = φ.vars := (rfl)

/-- A conjunction has the variables of both formulas. -/
@[simp]
theorem vars_and : (and φ ψ).vars = φ.vars ∪ ψ.vars := (rfl)

/-- A disjunction has the variables of both formulas. -/
@[simp]
theorem vars_or : (or φ ψ).vars = φ.vars ∪ ψ.vars := (rfl)

/-- The only subformula of a variable is the variable itself. -/
@[simp]
theorem subformulas_var : (var v).subformulas = {var v} := (rfl)

/-- The only subformula of `tru` is `tru`. -/
@[simp]
theorem subformulas_tru : (tru : PropForm V).subformulas = {tru} := (rfl)

/-- The only subformula of `fls` is `fls`. -/
@[simp]
theorem subformulas_fls : (fls : PropForm V).subformulas = {fls} := (rfl)

/-- The subformulas of a negation are the negation and the subformulas of the negated
formula. -/
@[simp]
theorem subformulas_neg : (neg φ).subformulas = insert (neg φ) φ.subformulas := (rfl)

/-- The subformulas of a conjunction are the conjunction and the subformulas of both
formulas. -/
@[simp]
theorem subformulas_and :
    (and φ ψ).subformulas = insert (and φ ψ) (φ.subformulas ∪ ψ.subformulas) := (rfl)

/-- The subformulas of a disjunction are the disjunction and the subformulas of both
formulas. -/
@[simp]
theorem subformulas_or :
    (or φ ψ).subformulas = insert (or φ ψ) (φ.subformulas ∪ ψ.subformulas) := (rfl)

variable {φ ψ}

/-- The truth value of a formula depends only on the values of the assignment at the variables
of the formula. -/
theorem eval_congr {τ τ' : V → Bool} (h : ∀ v ∈ φ.vars, τ v = τ' v) :
    φ.eval τ = φ.eval τ' := by
  induction φ with
  | var v => simpa using h
  | tru | fls => rfl
  | neg φ ih => simp [ih h]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [vars_and, vars_or, Finset.mem_union] at h
    simp [ihφ fun v hv ↦ h v (.inl hv), ihψ fun v hv ↦ h v (.inr hv)]

/-- A formula is a subformula of itself. -/
@[simp]
theorem mem_subformulas_self (φ : PropForm V) : φ ∈ φ.subformulas := by
  cases φ <;> simp

/-- A subformula of a subformula is a subformula. -/
theorem subformulas_subset_of_mem (h : ψ ∈ φ.subformulas) : ψ.subformulas ⊆ φ.subformulas := by
  induction φ with
  | var | tru | fls => simp_all
  | neg φ ih =>
    rw [subformulas_neg, Finset.mem_insert] at h
    rcases h with rfl | h
    · rfl
    · exact (ih h).trans (Finset.subset_insert _ _)
  | and φ χ ihφ ihχ | or φ χ ihφ ihχ =>
    simp only [subformulas_and, subformulas_or, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · rfl
    all_goals simp only [subformulas_and, subformulas_or]
    · exact (ihφ h).trans (Finset.subset_union_left.trans (Finset.subset_insert _ _))
    · exact (ihχ h).trans (Finset.subset_union_right.trans (Finset.subset_insert _ _))

/-- The negated formula of a subformula `neg ψ` is a subformula. -/
theorem mem_subformulas_of_neg_mem (h : neg ψ ∈ φ.subformulas) : ψ ∈ φ.subformulas :=
  subformulas_subset_of_mem h (by simp)

/-- The left formula of a subformula `and ψ χ` is a subformula. -/
theorem mem_subformulas_of_and_mem_left (h : and ψ χ ∈ φ.subformulas) : ψ ∈ φ.subformulas :=
  subformulas_subset_of_mem h (by simp)

/-- The right formula of a subformula `and ψ χ` is a subformula. -/
theorem mem_subformulas_of_and_mem_right (h : and ψ χ ∈ φ.subformulas) : χ ∈ φ.subformulas :=
  subformulas_subset_of_mem h (by simp)

/-- The left formula of a subformula `or ψ χ` is a subformula. -/
theorem mem_subformulas_of_or_mem_left (h : or ψ χ ∈ φ.subformulas) : ψ ∈ φ.subformulas :=
  subformulas_subset_of_mem h (by simp)

/-- The right formula of a subformula `or ψ χ` is a subformula. -/
theorem mem_subformulas_of_or_mem_right (h : or ψ χ ∈ φ.subformulas) : χ ∈ φ.subformulas :=
  subformulas_subset_of_mem h (by simp)

/-- The subformulas of `φ` that are not variables are at most `φ.size` many: each constant and
each connective contributes at most one. -/
private theorem card_subformulas_sdiff_le (φ : PropForm V) :
    (φ.subformulas \ φ.vars.image var).card ≤ φ.size := by
  induction φ with
  | var v => simp
  | tru | fls => simp
  | neg φ ih =>
    rw [subformulas_neg, vars_neg, size_neg]
    refine (Finset.card_le_card ?_).trans
      ((Finset.card_insert_le (neg φ) _).trans (Nat.add_le_add_right ih 1))
    intro x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    tauto
  | and φ ψ ihφ ihψ =>
    rw [subformulas_and, vars_and, size_and, Finset.image_union]
    refine (Finset.card_le_card ?_).trans ((Finset.card_insert_le (and φ ψ) _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans (Nat.add_le_add ihφ ihψ)) 1))
    intro x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union]
    tauto
  | or φ ψ ihφ ihψ =>
    rw [subformulas_or, vars_or, size_or, Finset.image_union]
    refine (Finset.card_le_card ?_).trans ((Finset.card_insert_le (or φ ψ) _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans (Nat.add_le_add ihφ ihψ)) 1))
    intro x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union]
    tauto

/-- A formula has at most `φ.size + m` subformulas, where `m` is the number of its distinct
variables. -/
theorem card_subformulas_le (φ : PropForm V) :
    φ.subformulas.card ≤ φ.size + φ.vars.card :=
  Finset.card_le_card_sdiff_add_card.trans
    (Nat.add_le_add (card_subformulas_sdiff_le φ) Finset.card_image_le)

end DecidableEq

/-! ### Negation normal form -/

/-- The **negation normal form at polarity `b`**: `φ.toNNF true` is the negation normal form of
`φ` and `φ.toNNF false` that of `neg φ`. Negations are pushed inwards by the De Morgan laws,
double negations are removed and a negated constant becomes the other constant. -/
def toNNF : Bool → PropForm V → PropForm V
  | true, var v => var v
  | false, var v => neg (var v)
  | true, tru => tru
  | false, tru => fls
  | true, fls => fls
  | false, fls => tru
  | b, neg φ => toNNF (!b) φ
  | true, and φ ψ => and (toNNF true φ) (toNNF true ψ)
  | false, and φ ψ => or (toNNF false φ) (toNNF false ψ)
  | true, or φ ψ => or (toNNF true φ) (toNNF true ψ)
  | false, or φ ψ => and (toNNF false φ) (toNNF false ψ)

/-- The **negation normal form** of a formula: an equivalent formula in which `neg` is applied
to variables only (`equivalent_nnf`, `isNNF_nnf`). -/
def nnf (φ : PropForm V) : PropForm V := toNNF true φ

/-- A formula is **in negation normal form** when `neg` occurs in it only in front of
variables. -/
inductive IsNNF : PropForm V → Prop
  /-- A variable is in negation normal form. -/
  | var (v : V) : IsNNF (var v)
  /-- A negated variable is in negation normal form. -/
  | neg_var (v : V) : IsNNF (neg (var v))
  /-- The constant `tru` is in negation normal form. -/
  | tru : IsNNF tru
  /-- The constant `fls` is in negation normal form. -/
  | fls : IsNNF fls
  /-- A conjunction of formulas in negation normal form is in negation normal form. -/
  | and {φ ψ : PropForm V} : IsNNF φ → IsNNF ψ → IsNNF (and φ ψ)
  /-- A disjunction of formulas in negation normal form is in negation normal form. -/
  | or {φ ψ : PropForm V} : IsNNF φ → IsNNF ψ → IsNNF (or φ ψ)

attribute [simp] IsNNF.var IsNNF.neg_var IsNNF.tru IsNNF.fls

/-- The number of occurrences of **atoms**, that is of variables and constants, in a
formula. -/
def numAtoms : PropForm V → ℕ
  | var _ => 1
  | tru => 1
  | fls => 1
  | neg φ => numAtoms φ
  | and φ ψ => numAtoms φ + numAtoms ψ
  | or φ ψ => numAtoms φ + numAtoms ψ

/-- The number of occurrences of the **binary connectives** `and` and `or` in a formula. -/
def numBinaryConnectives : PropForm V → ℕ
  | var _ => 0
  | tru => 0
  | fls => 0
  | neg φ => numBinaryConnectives φ
  | and φ ψ => numBinaryConnectives φ + numBinaryConnectives ψ + 1
  | or φ ψ => numBinaryConnectives φ + numBinaryConnectives ψ + 1

variable (b : Bool) (φ ψ)

/-- At polarity `true`, a variable is left unchanged. -/
@[simp]
theorem toNNF_true_var : (var v).toNNF true = var v := (rfl)

/-- At polarity `false`, a variable becomes its negation. -/
@[simp]
theorem toNNF_false_var : (var v).toNNF false = neg (var v) := (rfl)

/-- At polarity `true`, the constant `tru` is left unchanged. -/
@[simp]
theorem toNNF_true_tru : (tru : PropForm V).toNNF true = tru := (rfl)

/-- At polarity `false`, the constant `tru` becomes `fls`. -/
@[simp]
theorem toNNF_false_tru : (tru : PropForm V).toNNF false = fls := (rfl)

/-- At polarity `true`, the constant `fls` is left unchanged. -/
@[simp]
theorem toNNF_true_fls : (fls : PropForm V).toNNF true = fls := (rfl)

/-- At polarity `false`, the constant `fls` becomes `tru`. -/
@[simp]
theorem toNNF_false_fls : (fls : PropForm V).toNNF false = tru := (rfl)

/-- A negation flips the polarity. -/
@[simp]
theorem toNNF_neg : (neg φ).toNNF b = φ.toNNF (!b) := by cases b <;> rfl

/-- At polarity `true`, a conjunction stays a conjunction. -/
@[simp]
theorem toNNF_true_and : (and φ ψ).toNNF true = and (φ.toNNF true) (ψ.toNNF true) := (rfl)

/-- At polarity `false`, a conjunction becomes a disjunction (De Morgan). -/
@[simp]
theorem toNNF_false_and : (and φ ψ).toNNF false = or (φ.toNNF false) (ψ.toNNF false) := (rfl)

/-- At polarity `true`, a disjunction stays a disjunction. -/
@[simp]
theorem toNNF_true_or : (or φ ψ).toNNF true = or (φ.toNNF true) (ψ.toNNF true) := (rfl)

/-- At polarity `false`, a disjunction becomes a conjunction (De Morgan). -/
@[simp]
theorem toNNF_false_or : (or φ ψ).toNNF false = and (φ.toNNF false) (ψ.toNNF false) := (rfl)

/-- The negation normal form is the negation normal form at polarity `true`. -/
theorem nnf_eq_toNNF : φ.nnf = φ.toNNF true := (rfl)

/-- A variable is one atom. -/
@[simp]
theorem numAtoms_var : (var v).numAtoms = 1 := (rfl)

/-- The constant `tru` is one atom. -/
@[simp]
theorem numAtoms_tru : (tru : PropForm V).numAtoms = 1 := (rfl)

/-- The constant `fls` is one atom. -/
@[simp]
theorem numAtoms_fls : (fls : PropForm V).numAtoms = 1 := (rfl)

/-- A negation has the atoms of the negated formula. -/
@[simp]
theorem numAtoms_neg : (neg φ).numAtoms = φ.numAtoms := (rfl)

/-- A conjunction has the atoms of both formulas. -/
@[simp]
theorem numAtoms_and : (and φ ψ).numAtoms = φ.numAtoms + ψ.numAtoms := (rfl)

/-- A disjunction has the atoms of both formulas. -/
@[simp]
theorem numAtoms_or : (or φ ψ).numAtoms = φ.numAtoms + ψ.numAtoms := (rfl)

/-- A variable has no binary connectives. -/
@[simp]
theorem numBinaryConnectives_var : (var v).numBinaryConnectives = 0 := (rfl)

/-- The constant `tru` has no binary connectives. -/
@[simp]
theorem numBinaryConnectives_tru : (tru : PropForm V).numBinaryConnectives = 0 := (rfl)

/-- The constant `fls` has no binary connectives. -/
@[simp]
theorem numBinaryConnectives_fls : (fls : PropForm V).numBinaryConnectives = 0 := (rfl)

/-- A negation has the binary connectives of the negated formula. -/
@[simp]
theorem numBinaryConnectives_neg : (neg φ).numBinaryConnectives = φ.numBinaryConnectives :=
  (rfl)

/-- A conjunction adds one binary connective to those of both formulas. -/
@[simp]
theorem numBinaryConnectives_and :
    (and φ ψ).numBinaryConnectives = φ.numBinaryConnectives + ψ.numBinaryConnectives + 1 :=
  (rfl)

/-- A disjunction adds one binary connective to those of both formulas. -/
@[simp]
theorem numBinaryConnectives_or :
    (or φ ψ).numBinaryConnectives = φ.numBinaryConnectives + ψ.numBinaryConnectives + 1 :=
  (rfl)

variable {φ ψ}

/-- A negation is in negation normal form exactly when it negates a variable. -/
@[simp]
theorem isNNF_neg_iff : (neg φ).IsNNF ↔ ∃ v, φ = var v := by
  refine ⟨fun h ↦ ?_, fun ⟨v, h⟩ ↦ h ▸ .neg_var v⟩
  cases h with
  | neg_var v => exact ⟨v, rfl⟩

/-- A conjunction is in negation normal form exactly when both formulas are. -/
@[simp]
theorem isNNF_and_iff : (and φ ψ).IsNNF ↔ φ.IsNNF ∧ ψ.IsNNF := by
  refine ⟨fun h ↦ ?_, fun h ↦ .and h.1 h.2⟩
  cases h with
  | and hφ hψ => exact ⟨hφ, hψ⟩

/-- A disjunction is in negation normal form exactly when both formulas are. -/
@[simp]
theorem isNNF_or_iff : (or φ ψ).IsNNF ↔ φ.IsNNF ∧ ψ.IsNNF := by
  refine ⟨fun h ↦ ?_, fun h ↦ .or h.1 h.2⟩
  cases h with
  | or hφ hψ => exact ⟨hφ, hψ⟩

variable (φ)

/-- The negation normal form at polarity `b` evaluates to `true` exactly when `φ` evaluates
to `b`. -/
@[simp]
theorem eval_toNNF : (φ.toNNF b).eval τ = (φ.eval τ == b) := by
  induction φ generalizing b with
  | neg φ ih => simp [ih]
  | _ => cases b <;> simp_all

/-- The negation normal form at polarity `b` is in negation normal form. -/
theorem isNNF_toNNF : (φ.toNNF b).IsNNF := by
  induction φ generalizing b with
  | neg φ ih => simpa using ih (!b)
  | _ => cases b <;> simp [*]

/-- A formula has one more occurrence of atoms than of binary connectives. -/
theorem numAtoms_eq_numBinaryConnectives_add_one :
    φ.numAtoms = φ.numBinaryConnectives + 1 := by
  induction φ <;> simp [*] <;> omega

/-- The negation normal form at polarity `b` has as many occurrences of `and` and `or`
together as `φ`. -/
@[simp]
theorem numBinaryConnectives_toNNF :
    (φ.toNNF b).numBinaryConnectives = φ.numBinaryConnectives := by
  induction φ generalizing b with
  | neg φ ih => simp [ih]
  | _ => cases b <;> simp [*]

/-- The negation normal form at polarity `b` has as many occurrences of variables and constants
together as `φ`. -/
@[simp]
theorem numAtoms_toNNF : (φ.toNNF b).numAtoms = φ.numAtoms := by
  simp [numAtoms_eq_numBinaryConnectives_add_one]

/-- The negation normal form of `φ` evaluates as `φ`. -/
@[simp]
theorem eval_nnf : φ.nnf.eval τ = φ.eval τ := by
  simp [nnf_eq_toNNF]

/-- The negation normal form of `φ` is equivalent to `φ`. -/
theorem equivalent_nnf : φ.nnf.Equivalent φ := fun τ ↦ eval_nnf τ φ

/-- The negation normal form of `φ` is in negation normal form. -/
theorem isNNF_nnf : φ.nnf.IsNNF := isNNF_toNNF φ true

/-- The negation normal form of `φ` has as many occurrences of `and` and `or` together as `φ`. -/
@[simp]
theorem numBinaryConnectives_nnf : φ.nnf.numBinaryConnectives = φ.numBinaryConnectives :=
  numBinaryConnectives_toNNF φ true

/-- The negation normal form of `φ` has as many occurrences of variables and constants together
as `φ`. -/
@[simp]
theorem numAtoms_nnf : φ.nnf.numAtoms = φ.numAtoms := numAtoms_toNNF φ true

end PropForm

end TauCeti.Propositional
