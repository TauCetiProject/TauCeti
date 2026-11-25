/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Concatenating independent finite families

These are the finite-tuple versions of the sum-type span and independence
criteria. They allow bases with a common initial block to be used with
Plücker coordinates, whose row indices are `Fin` types.

Over a division ring, lifting a basis of the range of a linear map `p` gives a family indexed by
`Fin (finrank (range p))` whose images under `p` are independent
(`LinearMap.exists_linearIndependent_comp`, and
`LinearMap.exists_linearIndependent_comp_of_surjective` for a surjective `p`). Together with
`LinearIndependent.fin_append_of_linearIndependent_comp`, this builds independent concatenations
adapted to a linear map.
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

/-- A concatenation is independent when its first block is an independent family in the kernel of
a linear map `f` and the image of its second block under `f` is independent. -/
theorem fin_append_of_linearIndependent_comp [Ring R] [AddCommGroup V] [Module R V] {W : Type*}
    [AddCommGroup W] [Module R W] {x : Fin p → V} {y : Fin q → V} (hx : LinearIndependent R x)
    (f : V →ₗ[R] W) (hfx : ∀ i, f (x i) = 0) (hy : LinearIndependent R (f ∘ y)) :
    LinearIndependent R (Fin.append x y) := by
  refine TauCeti.linearIndependent_fin_append.2
    ⟨hx, hy.of_comp, Submodule.disjoint_def.2 fun z hzx hzy ↦ ?_⟩
  have hfz : f z = 0 := (Submodule.span_le.2 (Set.range_subset_iff.2 fun i ↦
    LinearMap.mem_ker.2 (hfx i)) : span R (range x) ≤ LinearMap.ker f) hzx
  obtain ⟨l, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hzy
  have hl := Fintype.linearIndependent_iff.1 hy l (by simpa [map_sum, map_smul] using hfz)
  simp [hl]

end LinearIndependent

namespace LinearMap

open Module

variable {K W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Lifts along a linear map `p` of a basis of its range: a family of `dim (range p)` vectors whose
images under `p` are linearly independent. -/
theorem exists_linearIndependent_comp (p : V →ₗ[K] W) [FiniteDimensional K (range p)] :
    ∃ a : Fin (finrank K (range p)) → V, LinearIndependent K (p ∘ a) := by
  choose a ha using fun i ↦ p.surjective_rangeRestrict (Module.finBasis K (range p) i)
  refine ⟨a, ?_⟩
  have : ⇑p ∘ a = Subtype.val ∘ Module.finBasis K (range p) :=
    funext fun i ↦ congrArg Subtype.val (ha i)
  rw [this]
  exact (Module.finBasis K _).linearIndependent.map' _ (Submodule.ker_subtype _)

/-- Lifts along a surjective linear map `p` of a basis of its target: a family of `dim W` vectors
whose images under `p` are linearly independent. -/
theorem exists_linearIndependent_comp_of_surjective [FiniteDimensional K W] {p : V →ₗ[K] W}
    (hp : Function.Surjective p) :
    ∃ a : Fin (finrank K W) → V, LinearIndependent K (p ∘ a) := by
  choose a ha using fun i ↦ hp (Module.finBasis K W i)
  exact ⟨a, by rw [show ⇑p ∘ a = Module.finBasis K W from funext ha]; exact
    (Module.finBasis K W).linearIndependent⟩

end LinearMap
