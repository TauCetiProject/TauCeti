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
  -- `erw` unfolds the equivalence coercion to Mathlib's sum eliminator.
  erw [Fin.append_comp_sumElim]
  rw [Sum.elim_range, span_union]

namespace TauCeti

/-- A concatenation is independent exactly when its two parts are independent
and have disjoint spans. -/
theorem linearIndependent_fin_append [Ring R] [AddCommMonoid V] [Module R V]
    {x : Fin p → V} {y : Fin q → V} :
    LinearIndependent R (Fin.append x y) ↔
      LinearIndependent R x ∧ LinearIndependent R y ∧
        Disjoint (span R (range x)) (span R (range y)) := by
  -- Over a ring, an additive commutative monoid with a module structure is a group.
  let _ := Module.addCommMonoidToAddCommGroup R (M := V)
  rw [← linearIndependent_equiv finSumFinEquiv]
  -- `erw` unfolds the equivalence coercion to Mathlib's sum eliminator.
  erw [Fin.append_comp_sumElim]
  simp only [linearIndependent_sum, Sum.elim_comp_inl, Sum.elim_comp_inr]

end TauCeti

namespace LinearIndependent

open TauCeti

/-- Restricting the right block of a concatenation along an injection preserves independence. -/
theorem fin_append_comp_right [Semiring R] [AddCommMonoid V] [Module R V] {s : ℕ}
    {x : Fin p → V} {y : Fin q → V} {g : Fin s → Fin q} (hg : Function.Injective g)
    (h : LinearIndependent R (Fin.append x y)) :
    LinearIndependent R (Fin.append x (y ∘ g)) := by
  rw [← linearIndependent_equiv' finSumFinEquiv Fin.append_comp_sumElim] at h ⊢
  simpa only [Sum.elim_comp_map, Function.comp_id] using
    h.comp (Sum.map id g) (Function.injective_id.sumMap hg)

/-- Removing the last block of an independent three-block concatenation
preserves independence. -/
theorem fin_append_left_append [Semiring R] [AddCommMonoid V] [Module R V] {r : ℕ}
    {x : Fin p → V} {y : Fin q → V} {z : Fin r → V}
    (h : LinearIndependent R (Fin.append x (Fin.append y z))) :
    LinearIndependent R (Fin.append x y) := by
  simpa [Function.comp_def] using h.fin_append_comp_right (Fin.castAdd_injective q r)

/-- Removing the middle block of an independent three-block concatenation
preserves independence. -/
theorem fin_append_right_append [Semiring R] [AddCommMonoid V] [Module R V] {r : ℕ}
    {x : Fin p → V} {y : Fin q → V} {z : Fin r → V}
    (h : LinearIndependent R (Fin.append x (Fin.append y z))) :
    LinearIndependent R (Fin.append x z) := by
  simpa [Function.comp_def] using h.fin_append_comp_right (Fin.natAdd_injective r q)

end LinearIndependent
