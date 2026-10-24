/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Syntax

/-!
# Left variables of first-order terms under relabelling and substitution

Mathlib's `FirstOrder.Language.Term.varFinsetLeft` collects the variables of a term over `α ⊕ β`
that come from the left summand `α`. This file characterizes it through the full variable set
`Term.varFinset`, and computes it after `Term.relabel` and `Term.subst`.

## Main results

* `FirstOrder.Language.Term.mem_varFinsetLeft_iff`: `a` is a left variable of `t` exactly when
  `Sum.inl a` is a variable of `t`.
* `FirstOrder.Language.Term.mem_varFinsetLeft_relabel`: the left variables of a relabelled term.
* `FirstOrder.Language.Term.mem_varFinsetLeft_subst`: the left variables of a substituted term.
-/

public section

namespace FirstOrder

namespace Language

namespace Term

variable {L : Language} {α β γ δ : Type*}

/-- A left variable of a term over `α ⊕ β` is a variable `Sum.inl a` of the term. -/
theorem mem_varFinsetLeft_iff [DecidableEq α] [DecidableEq β] {t : L.Term (α ⊕ β)} {a : α} :
    a ∈ t.varFinsetLeft ↔ Sum.inl a ∈ t.varFinset := by
  induction t with
  | var x => cases x <;> simp
  | func f ts ih => simp [ih]

/-- The left variables of `t.relabel f` are the left values of `f` on the variables of `t`. -/
theorem mem_varFinsetLeft_relabel [DecidableEq α] [DecidableEq β] (f : α → β ⊕ γ)
    {t : L.Term α} {b : β} :
    b ∈ (t.relabel f).varFinsetLeft ↔ ∃ x ∈ t.varFinset, f x = Sum.inl b := by
  induction t with
  | var x =>
    rcases hx : f x with c | c <;> simp [hx, eq_comm]
  | func g ts ih =>
    simp only [relabel, varFinsetLeft, varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      ih]
    exact ⟨fun ⟨i, x, hx, h⟩ => ⟨x, ⟨i, hx⟩, h⟩, fun ⟨x, ⟨i, hx⟩, h⟩ => ⟨i, x, hx, h⟩⟩

/-- The left variables of `t.subst σ` are the left variables of `σ x` for the variables `x`
of `t`. -/
theorem mem_varFinsetLeft_subst [DecidableEq α] [DecidableEq β] (σ : α → L.Term (β ⊕ γ))
    {t : L.Term α} {b : β} :
    b ∈ (t.subst σ).varFinsetLeft ↔ ∃ x ∈ t.varFinset, b ∈ (σ x).varFinsetLeft := by
  induction t with
  | var x => simp
  | func g ts ih =>
    simp only [subst, varFinsetLeft, varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      ih]
    exact ⟨fun ⟨i, x, hx, h⟩ => ⟨x, ⟨i, hx⟩, h⟩, fun ⟨x, ⟨i, hx⟩, h⟩ => ⟨i, x, hx, h⟩⟩

end Term

end Language

end FirstOrder
