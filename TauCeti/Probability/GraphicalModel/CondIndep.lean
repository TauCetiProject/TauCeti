/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Basic.NNReal.Basic

/-!
# Margins and conditional independence of finite laws

The variables are indexed by a finite type `V`, the variable at `v` takes values in a finite type
`X v`, and a configuration is an element `x : ∀ v, X v`. A law is a function
`p : (∀ v, X v) → ℝ≥0`; no normalization is imposed. Sets of variables are `Finset V`.

The **margin** `margin p A x`, written `p(x_A)`, is the mass of the configurations that agree with
`x` on `A`. On `A = ∅` it is the total mass of `p`, and on `A = univ` it is `p x`.

The variables in `A` and in `B` are **conditionally independent given** those in `S`, written
`A ⊥ B | S`, when `p(x_S) p(x_{A ∪ B ∪ S}) = p(x_{A ∪ S}) p(x_{B ∪ S})` for every configuration
`x`. This identity between finite sums is the definition by conditional densities with the
denominators cleared: it needs no division, so it is also defined at configurations of mass
zero. The sets need not be disjoint, and `S = ∅` gives independence, scaled by the total mass.

## Main definitions

* `TauCeti.GraphicalModel.margin`: the margin `p(x_A)` of a law on a set of variables.
* `TauCeti.GraphicalModel.CondIndep`: the conditional independence `A ⊥ B | S` under a law.

## Main statements

* `TauCeti.GraphicalModel.margin_empty`, `TauCeti.GraphicalModel.margin_univ`: the margin on no
  variable is the total mass, and the margin on all variables is the law itself.
* `TauCeti.GraphicalModel.margin_anti`: the margin does not increase when the set of variables
  grows.
* `TauCeti.GraphicalModel.condIndep_comm`: `A ⊥ B | S` if and only if `B ⊥ A | S`.
* `TauCeti.GraphicalModel.condIndep_of_subset`: if `A ⊆ S`, then `A ⊥ B | S` for every `B`.
* `TauCeti.GraphicalModel.condIndep_of_subsingleton`: variables with at most one value are
  conditionally independent of all variables, given any set.
* `TauCeti.GraphicalModel.condIndep_smul_iff`: conditional independence does not change when the
  law is multiplied by a nonzero constant.
* `TauCeti.GraphicalModel.condIndep_self_iff`: `A ⊥ A | S` holds if and only if at each
  configuration `p(x_{A ∪ S})` is `0` or `p(x_S)`, so that the variables in `A` are almost surely
  determined by those in `S`.

## References

* R. Evans, *Graphical Models*, lecture notes, University of Oxford, Michaelmas 2018, version of
  January 17, 2019: Definition 2.2, Theorem 2.4 (iv) and Theorem 2.6.
-/

public section

noncomputable section

open Finset
open scoped NNReal

namespace TauCeti.GraphicalModel

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-! ### Margins -/

/-- The margin of the law `p` on the set `A` of variables at the configuration `x`: the mass of
the configurations that agree with `x` on `A`. On `A = ∅` it is the total mass of `p`. -/
def margin (p : (∀ v, X v) → ℝ≥0) (A : Finset V) (x : ∀ v, X v) : ℝ≥0 :=
  ∑ y ∈ univ.filter (fun y => ∀ v ∈ A, y v = x v), p y

variable {p : (∀ v, X v) → ℝ≥0} {A B S T : Finset V} {x : ∀ v, X v}

/-- The margin as a sum over the configurations that agree with `x` on `A`. -/
theorem margin_def :
    margin p A x = ∑ y ∈ univ.filter (fun y => ∀ v ∈ A, y v = x v), p y := (rfl)

/-- The margin on no variable is the total mass. -/
@[simp]
theorem margin_empty : margin p ∅ x = ∑ y, p y := by
  simp [margin_def]

/-- The margin on all variables is the law itself. -/
@[simp]
theorem margin_univ : margin p univ x = p x := by
  simp [margin_def, ← funext_iff, filter_eq']

/-- The margin on `A` depends only on the values of the configuration on `A`. -/
theorem dependsOn_margin : DependsOn (margin p A) (A : Set V) := fun x x' h => by
  simp only [margin_def]
  congr 1
  exact filter_congr fun y _ => forall₂_congr fun v hv => by rw [h v hv]

/-- The margin does not increase when the set of variables grows. -/
theorem margin_anti (h : A ⊆ B) : margin p B x ≤ margin p A x :=
  sum_le_sum_of_subset (monotone_filter_right _ fun _ _ hy v hv => hy v (h hv))

/-- The law at `x` is at most each of its margins at `x`. -/
theorem le_margin : p x ≤ margin p A x :=
  margin_univ (p := p) (x := x) ▸ margin_anti (subset_univ A)

/-- The margin of a multiple of the law is the multiple of the margin. -/
@[simp]
theorem margin_smul (c : ℝ≥0) : margin (c • p) A x = c * margin p A x := by
  simp [margin_def, mul_sum]

/-- A margin of the law of constant mass `c` is `c` times the number of configurations that
agree with `x` on `A`. -/
theorem margin_const (c : ℝ≥0) :
    margin (fun _ => c) A x = #(univ.filter fun y : ∀ v, X v => ∀ v ∈ A, y v = x v) * c := by
  rw [margin_def, sum_const, nsmul_eq_mul]

/-- Variables with at most one value do not change the margin. -/
theorem margin_union_of_subsingleton (h : ∀ v ∈ A, Subsingleton (X v)) :
    margin p (A ∪ T) x = margin p T x := by
  simp only [margin_def]
  congr 1
  refine filter_congr fun y _ => ?_
  simp only [mem_union, or_imp, forall_and]
  exact and_iff_right fun v hv => @Subsingleton.elim _ (h v hv) _ _

/-! ### Conditional independence -/

/-- The variables in `A` and in `B` are conditionally independent given those in `S` under the
law `p`: `p(x_S) p(x_{A ∪ B ∪ S}) = p(x_{A ∪ S}) p(x_{B ∪ S})` for every configuration `x`. -/
def CondIndep (p : (∀ v, X v) → ℝ≥0) (A B S : Finset V) : Prop :=
  ∀ x, margin p S x * margin p (A ∪ B ∪ S) x = margin p (A ∪ S) x * margin p (B ∪ S) x

/-- Conditional independence as the identity between margins at every configuration. -/
theorem condIndep_iff : CondIndep p A B S ↔
    ∀ x, margin p S x * margin p (A ∪ B ∪ S) x = margin p (A ∪ S) x * margin p (B ∪ S) x :=
  Iff.rfl

/-- Conditional independence is symmetric in the two sets of variables. -/
theorem CondIndep.symm (h : CondIndep p A B S) : CondIndep p B A S := fun x => by
  rw [union_comm B A, mul_comm (margin p (B ∪ S) x)]
  exact h x

/-- `A ⊥ B | S` if and only if `B ⊥ A | S`. -/
theorem condIndep_comm : CondIndep p A B S ↔ CondIndep p B A S :=
  ⟨CondIndep.symm, CondIndep.symm⟩

/-- Variables in the conditioning set are conditionally independent of all variables. -/
theorem condIndep_of_subset (h : A ⊆ S) : CondIndep p A B S := fun x => by
  rw [union_right_comm, union_eq_right.2 h, union_comm S B]

/-- The empty set of variables is conditionally independent of every set, given any set. -/
@[simp]
theorem condIndep_empty_left : CondIndep p ∅ B S :=
  condIndep_of_subset (empty_subset S)

/-- Variables with at most one value are conditionally independent of all variables, given any
set of variables. -/
theorem condIndep_of_subsingleton (h : ∀ v ∈ A, Subsingleton (X v)) : CondIndep p A B S :=
  fun x => by
    rw [union_assoc, margin_union_of_subsingleton h, margin_union_of_subsingleton h]

/-- Conditional independence does not change when the law is multiplied by a nonzero
constant. -/
theorem condIndep_smul_iff {c : ℝ≥0} (hc : c ≠ 0) : CondIndep (c • p) A B S ↔ CondIndep p A B S :=
  forall_congr' fun x => by
    simp only [margin_smul, mul_mul_mul_comm c]
    exact mul_right_inj' (mul_ne_zero hc hc)

/-- `A ⊥ A | S` holds if and only if at every configuration the margin on `A ∪ S` is the margin
on `S` or `0`: the variables in `A` are almost surely determined by those in `S`. -/
theorem condIndep_self_iff : CondIndep p A A S ↔
    ∀ x, margin p (A ∪ S) x = margin p S x ∨ margin p (A ∪ S) x = 0 :=
  forall_congr' fun x => by
    rw [union_self, mul_eq_mul_right_iff, eq_comm (a := margin p S x)]

end TauCeti.GraphicalModel
