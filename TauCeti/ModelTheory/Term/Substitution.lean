/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Syntax

/-!
# Substitution in first-order terms

Mathlib's `FirstOrder.Language.Term.subst` replaces each variable of a term by a term. This file
records its algebra: substituting variables for themselves is the identity, two substitutions
compose to one, relabelling is the substitution of variables, and both relabelling and
language maps commute with substitution. These are the term cases of the corresponding laws for
substitution into formulas.

## Main results

* `FirstOrder.Language.Term.subst_var`: substituting each variable by itself.
* `FirstOrder.Language.Term.subst_subst`: two substitutions compose to one.
* `FirstOrder.Language.Term.relabel_eq_subst`: relabelling is substitution of variables.
* `FirstOrder.Language.Term.relabel_subst`, `FirstOrder.Language.Term.subst_relabel`:
  relabelling after and before a substitution.
* `FirstOrder.Language.LHom.onTerm_subst`: language maps commute with substitution.
-/

public section

universe u v u' v' uα uβ uγ

namespace FirstOrder.Language

variable {L : Language.{u, v}} {α : Type uα} {β : Type uβ} {γ : Type uγ}

namespace Term

/-- Substituting each variable by itself leaves a term unchanged. -/
@[simp]
theorem subst_var (t : L.Term α) : t.subst var = t := by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

/-- Two successive substitutions are one substitution, by the substituted terms. -/
@[simp]
theorem subst_subst (t : L.Term α) (f : α → L.Term β) (g : β → L.Term γ) :
    (t.subst f).subst g = t.subst fun a => (f a).subst g := by
  induction t with
  | var => rfl
  | func F ts ih => simp [ih]

/-- Relabelling the variables of a term is substituting variables for them. -/
theorem relabel_eq_subst (t : L.Term α) (f : α → β) : t.relabel f = t.subst (var ∘ f) := by
  induction t with
  | var => rfl
  | func F ts ih => simp [ih]

/-- Relabelling after a substitution relabels the substituted terms. -/
@[simp]
theorem relabel_subst (t : L.Term α) (f : α → L.Term β) (g : β → γ) :
    (t.subst f).relabel g = t.subst fun a => (f a).relabel g := by
  induction t with
  | var => rfl
  | func F ts ih => simp [ih]

/-- Substitution after a relabelling is substitution along the composite. -/
@[simp]
theorem subst_relabel (t : L.Term α) (f : α → β) (g : β → L.Term γ) :
    (t.relabel f).subst g = t.subst (g ∘ f) := by
  induction t with
  | var => rfl
  | func F ts ih => simp [ih]

end Term

namespace LHom

variable {L' : Language.{u', v'}}

/-- A language map commutes with substitution, acting on the substituted terms. -/
@[simp]
theorem onTerm_subst (g : L →ᴸ L') (t : L.Term α) (f : α → L.Term β) :
    g.onTerm (t.subst f) = (g.onTerm t).subst fun a => g.onTerm (f a) := by
  induction t with
  | var => rfl
  | func F ts ih => simp [ih]

end LHom

end FirstOrder.Language
