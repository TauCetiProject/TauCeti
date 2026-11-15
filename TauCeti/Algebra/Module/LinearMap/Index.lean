/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.LinearAlgebra.Quotient.Prod

/-!
# Index of linear maps

This file extends Mathlib's algebraic `LinearMap.index` API with its invariance under composing
with a linear equivalence, its additivity under products with finite free kernels and cokernels,
and its behaviour under restriction of scalars along a tower of division rings `K → L`: the index
gets multiplied by `finrank K L`. For instance, the realification of a complex-linear map has
twice its complex index.

These lemmas are absent from `Mathlib.Algebra.Module.LinearMap.Index` and support the
continuous-linear-map results in `TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index`.
-/

public section

namespace LinearMap

variable {R M N P : Type*} [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- Postcomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_equiv_comp (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    ((e : N →ₗ[R] P).comp f).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_comp_of_ker_eq_bot _ (ker_eq_bot.2 e.injective)]
  · rw [range_comp]
    exact_mod_cast (LinearEquiv.finrank_eq
      (Submodule.Quotient.equiv f.range (f.range.map (e : N →ₗ[R] P)) e rfl)).symm

/-- Precomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_comp_equiv (f : M →ₗ[R] N) (e : P ≃ₗ[R] M) :
    (f.comp (e : P →ₗ[R] M)).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  · rw [range_comp_of_range_eq_top _ (range_eq_top.2 e.surjective)]

/-- The index is additive under Cartesian products when the kernels and cokernels are finite
free modules. -/
@[simp]
lemma index_prodMap {Q : Type*} [AddCommGroup Q] [Module R Q] [StrongRankCondition R]
    (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
    [Module.Free R f.ker] [Module.Free R g.ker]
    [Module.Finite R f.ker] [Module.Finite R g.ker]
    [Module.Free R (N ⧸ f.range)] [Module.Free R (Q ⧸ g.range)]
    [Module.Finite R (N ⧸ f.range)] [Module.Finite R (Q ⧸ g.range)] :
    (f.prodMap g).index = f.index + g.index := by
  simp only [index_eq_finrank_sub]
  rw [ker_prodMap, range_prodMap]
  simp only [(Submodule.prodEquiv _ _).finrank_eq, Submodule.finrank_quotient_prod,
    Module.finrank_prod]
  omega

section RestrictScalars

open Module

variable (K : Type*) {L M N : Type*} [DivisionRing K] [DivisionRing L] [Module K L]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]
  [AddCommGroup N] [Module K N] [Module L N] [IsScalarTower K L N]

/-- Restricting scalars along a tower of division rings `K → L` multiplies the index by
`finrank K L`. No finiteness hypothesis is needed: an infinite-dimensional kernel or cokernel
has `finrank` zero over both `K` and `L`. -/
@[simp]
lemma index_restrictScalars (f : M →ₗ[L] N) :
    (f.restrictScalars K).index = finrank K L * f.index := by
  -- `(ker f).restrictScalars K` carries the `K`-module structure that `ker f` inherits from `M`.
  have hker : finrank K ((ker f).restrictScalars K) = finrank K L * finrank L (ker f) :=
    (finrank_mul_finrank K L (ker f)).symm
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_restrictScalars, range_restrictScalars,
    (Submodule.Quotient.restrictScalarsEquiv K (range f)).finrank_eq, hker,
    ← finrank_mul_finrank K L (N ⧸ range f)]
  push_cast
  ring

end RestrictScalars

end LinearMap
