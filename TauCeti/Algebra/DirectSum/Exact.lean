/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of componentwise maps on direct sums

A family of exact pairs of module maps induces an exact pair on the external direct sums. This is
the algebraic input for taking direct sums of projective resolutions: kernels and ranges of the
componentwise maps are themselves computed componentwise.

## Main results

* `Function.Exact.directSum`: componentwise direct sums preserve exact pairs of module maps.
-/

public section

universe uR uι uM uN uP

namespace Function.Exact

variable {R : Type uR} [Semiring R] {ι : Type uι}
  {M : ι → Type uM} {N : ι → Type uN} {P : ι → Type uP}
  [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, AddCommMonoid (P i)]
  [∀ i, Module R (M i)] [∀ i, Module R (N i)] [∀ i, Module R (P i)]
  {f : ∀ i, M i →ₗ[R] N i} {g : ∀ i, N i →ₗ[R] P i}

/-- Componentwise direct sums preserve exact pairs of module maps. -/
theorem directSum (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff, DirectSum.range_lmap, DirectSum.ker_lmap]
  ext x
  simp only [Submodule.mem_comap, DirectSum.coeFnLinearMap_apply, Submodule.mem_pi, Set.mem_univ,
    true_implies]
  exact forall_congr' fun i ↦
    SetLike.ext_iff.mp (LinearMap.exact_iff.mp (h i)) (x i)

end Function.Exact
