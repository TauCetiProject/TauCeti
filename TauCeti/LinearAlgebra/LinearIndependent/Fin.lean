/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Concatenating independent finite families

These are the finite-tuple versions of the sum-type span and independence
criteria. They allow bases with a common initial block to be used with
Plücker coordinates, whose row indices are `Fin` types.
-/

public section

open Submodule Set

variable {R V : Type*} {p q : ℕ}

/-- The span of a concatenation is the sum of the two spans. -/
theorem Submodule.span_range_fin_append [Semiring R] [AddCommMonoid V] [Module R V]
    (x : Fin p → V) (y : Fin q → V) :
    span R (range (Fin.append x y)) = span R (range x) ⊔ span R (range y) := by
  rw [← EquivLike.range_comp (Fin.append x y) finSumFinEquiv]
  have heq : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
    ext i
    rcases i with i | i <;> simp
  rw [heq, Sum.elim_range, span_union]

namespace TauCeti

/-- A concatenation is independent exactly when its two parts are independent
and have disjoint spans. -/
theorem linearIndependent_fin_append [Ring R] [AddCommGroup V] [Module R V]
    {x : Fin p → V} {y : Fin q → V} :
    LinearIndependent R (Fin.append x y) ↔
      LinearIndependent R x ∧ LinearIndependent R y ∧
        Disjoint (span R (range x)) (span R (range y)) := by
  rw [← linearIndependent_equiv finSumFinEquiv]
  have heq : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
    ext i
    rcases i with i | i <;> simp
  rw [heq, linearIndependent_sum]
  rfl

end TauCeti
