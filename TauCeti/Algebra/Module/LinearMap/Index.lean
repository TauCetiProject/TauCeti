/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import TauCeti.LinearAlgebra.Quotient.Prod
public import TauCeti.LinearAlgebra.LinearMap.Pi
public import TauCeti.LinearAlgebra.Quotient.Pi.Basic

/-!
# Index of linear maps

This file extends Mathlib's algebraic `LinearMap.index` API with its invariance under composing
with a linear equivalence and its additivity under Cartesian and finite coordinatewise products
with finite free kernels and cokernels.

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

/-- The index is additive under finite coordinatewise products with finite free kernels
and cokernels. -/
@[simp]
lemma index_piMap {ι : Type*} [Fintype ι] {E F : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [StrongRankCondition R]
    (f : ∀ i, E i →ₗ[R] F i)
    [∀ i, Module.Free R (f i).ker] [∀ i, Module.Finite R (f i).ker]
    [∀ i, Module.Free R (F i ⧸ (f i).range)]
    [∀ i, Module.Finite R (F i ⧸ (f i).range)] :
    (piMap f).index = ∑ i, (f i).index := by
  have hk := (kerPiMapEquiv f).finrank_eq.trans (Module.finrank_pi_fintype R)
  have hc := TauCeti.finrank_quotient_eq_sum_of_equiv_pi R
    (LinearEquiv.refl R (∀ i, F i)) (piMap f).range (fun i ↦ (f i).range)
    (fun x ↦ by simp [range_piMap])
  simp only [index_eq_finrank_sub, hk, hc, Nat.cast_sum, Finset.sum_sub_distrib]

end LinearMap
