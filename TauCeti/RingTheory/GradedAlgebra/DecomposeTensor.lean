/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Graded pieces of an algebra tensored on the right with an algebra

For a family of submodules `𝒜 i` of an `R`-algebra `A` and an `R`-module `H`, Mathlib's
`DirectSum.decomposeTensor 𝒜 H i` is the image of `𝒜 i ⊗[R] H` in `A ⊗[R] H`; it is a
decomposition of `A ⊗[R] H` when `𝒜` is one of `A`. When `H` is itself an `R`-algebra and `𝒜`
is a graded monoid, these pieces multiply according to the grading of `A`: `A ⊗[R] H` is graded
with `H` in degree zero.

This is the right-handed companion of Mathlib's `GradedAlgebra.baseChange`, which grades
`S ⊗[R] A` by the pieces `(𝒜 i).baseChange S`. The right-handed form is the one met by
coactions `V →ₗ[R] V ⊗[R] H` of comodules: an algebra homomorphism `A →ₐ[R] A ⊗[R] H` sending
generators of degree one into the degree-one piece preserves every degree.

## Main results

* `DirectSum.tmul_mem_decomposeTensor`: a pure tensor with homogeneous left factor is
  homogeneous of the same degree.
* `DirectSum.decomposeTensor.gradedMonoid`: the pieces `decomposeTensor 𝒜 H i` form a graded
  monoid.
-/

public section

open scoped TensorProduct

namespace DirectSum

variable {ι R A H : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

section Module

variable [AddCommMonoid H] [Module R H] {𝒜 : ι → Submodule R A}

/-- A pure tensor whose left factor lies in `𝒜 i` lies in the `i`-th piece of `A ⊗[R] H`. -/
theorem tmul_mem_decomposeTensor {i : ι} {a : A} (ha : a ∈ 𝒜 i) (h : H) :
    a ⊗ₜ[R] h ∈ decomposeTensor 𝒜 H i := by
  rw [decomposeTensor_apply]
  exact ⟨⟨a, ha⟩ ⊗ₜ[R] h, by rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]⟩

end Module

variable [AddMonoid ι] [Semiring H] [Algebra R H] (𝒜 : ι → Submodule R A)
  [SetLike.GradedMonoid 𝒜]

/-- A pure tensor with homogeneous left factor multiplies a homogeneous element by adding the
degrees. -/
private theorem tmul_mul_mem_decomposeTensor {i j : ι} {a : A} (ha : a ∈ 𝒜 i) (h : H)
    {y : A ⊗[R] H} (hy : y ∈ decomposeTensor 𝒜 H j) :
    (a ⊗ₜ[R] h) * y ∈ decomposeTensor 𝒜 H (i + j) := by
  rw [decomposeTensor_apply] at hy
  obtain ⟨y, rfl⟩ := hy
  induction y using TensorProduct.inductionOn with
  | tmul b k =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_decomposeTensor (SetLike.mul_mem_graded ha b.2) _
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, mul_add]
    exact add_mem h₁ h₂

/-- The pieces of `A ⊗[R] H` induced by a graded monoid `𝒜` on `A` form a graded monoid, with
the right tensor factor `H` in degree zero. -/
instance decomposeTensor.gradedMonoid : SetLike.GradedMonoid (decomposeTensor 𝒜 H) where
  one_mem := tmul_mem_decomposeTensor (SetLike.one_mem_graded 𝒜) 1
  mul_mem i j x y hx hy := by
    rw [decomposeTensor_apply] at hx
    obtain ⟨x, rfl⟩ := hx
    induction x using TensorProduct.inductionOn with
    | tmul a h => exact tmul_mul_mem_decomposeTensor 𝒜 a.2 h hy
    | add x₁ x₂ h₁ h₂ =>
      rw [map_add, add_mul]
      exact add_mem h₁ h₂

end DirectSum
