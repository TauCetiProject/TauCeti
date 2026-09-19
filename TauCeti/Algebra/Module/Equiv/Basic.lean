/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Evaluating multiplication by a unit of the base ring

Mathlib's `LinearEquiv.smulOfUnit` packages multiplication by a unit `u` of the base ring as a
linear equivalence, but records no lemma evaluating it at a vector. This file supplies that
evaluation lemma, in the `simp`-normal form that rewrites an application of
`LinearEquiv.smulOfUnit` to a scalar multiplication.

## Main results

* `LinearEquiv.map_ker_of_intertwine` and `LinearEquiv.map_range_of_intertwine`: transport of
  kernels and ranges across an intertwining linear equivalence.
* `LinearEquiv.smulOfUnit_apply`: `LinearEquiv.smulOfUnit u` acts as multiplication by `u`.
-/

public section

namespace LinearEquiv

section Intertwining

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- If a linear equivalence `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the kernel of `f` onto the kernel of `g`. -/
theorem map_ker_of_intertwine
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₗ[R] N) (LinearMap.ker f) = LinearMap.ker g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [h d, hd, map_zero]
  · intro hc
    refine ⟨e.symm c, ?_, e.apply_symm_apply c⟩
    have : e (f (e.symm c)) = 0 := by rw [← h, e.apply_symm_apply, hc]
    exact e.map_eq_zero_iff.mp this

/-- If a linear equivalence `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the range of `f` onto the range of `g`. -/
theorem map_range_of_intertwine
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₗ[R] N) (LinearMap.range f) = LinearMap.range g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, ⟨b, rfl⟩, rfl⟩
    exact ⟨e b, h b⟩
  · rintro ⟨b, rfl⟩
    exact ⟨f (e.symm b), ⟨e.symm b, rfl⟩, by rw [← h, e.apply_symm_apply]⟩

end Intertwining

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a unit of the base ring, evaluated: `LinearEquiv.smulOfUnit u` sends `x` to
`u • x`. -/
@[simp]
theorem smulOfUnit_apply (u : Rˣ) (x : M) : (smulOfUnit u : M ≃ₗ[R] M) x = (u : R) • x :=
  (rfl)

end LinearEquiv
