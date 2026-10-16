/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Module.BigOperators

/-!
# Matrices acting on vectors with entries in a topological module

A matrix `A : Matrix κ ι R` acts on vectors `x : ι → M` with entries in an `R`-module `M` by
`k ↦ ∑ i, A k i • x i`. When `M` is a topological additive monoid on which each scalar acts
continuously, this is the continuous additive map `Matrix.smulVecHom A M : (ι → M) →ₜ+ (κ → M)`,
and it is functorial in the matrix (`Matrix.smulVecHom_one`, `Matrix.smulVecHom_mul`). For `M = R`
it is `Matrix.mulVec` (`Matrix.smulVecHom_self_apply`).

The motivating case is `R = ℤ` and `M = AddCircle p`, where an integer matrix induces a map of
tori `(ι → AddCircle p) → (κ → AddCircle p)`.
-/

public section

namespace Matrix

variable {ι κ μ R : Type*} [Fintype ι] [Semiring R] (A : Matrix κ ι R)
  (M : Type*) [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul R M]

/-- The continuous additive map `(ι → M) →ₜ+ (κ → M)` induced by a matrix `A` with entries in `R`,
sending `x` to `k ↦ ∑ i, A k i • x i`. -/
def smulVecHom : (ι → M) →ₜ+ (κ → M) where
  toFun x k := ∑ i, A k i • x i
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp [smul_add, Finset.sum_add_distrib]
  continuous_toFun := by fun_prop

@[simp]
theorem smulVecHom_apply (x : ι → M) (k : κ) : A.smulVecHom M x k = ∑ i, A k i • x i :=
  (rfl)

/-- For `M = R`, the induced map is `Matrix.mulVec`. -/
@[simp]
theorem smulVecHom_self_apply [TopologicalSpace R] [ContinuousAdd R] [ContinuousConstSMul R R]
    (x : ι → R) : A.smulVecHom R x = A *ᵥ x := by
  ext k
  simp [mulVec, dotProduct]

/-- The identity matrix induces the identity map. -/
@[simp]
theorem smulVecHom_one [DecidableEq ι] :
    (1 : Matrix ι ι R).smulVecHom M = ContinuousAddMonoidHom.id _ := by
  ext x i
  simp [one_apply, ite_smul]

/-- The map induced by a product of matrices is the composite of the maps they induce. -/
theorem smulVecHom_mul [Fintype κ] (B : Matrix μ κ R) :
    (B * A).smulVecHom M = (B.smulVecHom M).comp (A.smulVecHom M) := by
  ext x m
  simp only [smulVecHom_apply, ContinuousAddMonoidHom.comp_toFun, mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end Matrix
