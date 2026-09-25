/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Reading a vector off a one-point coordinate support

A vector whose coordinates in a basis vanish outside a single index is that one coordinate times
the corresponding basis vector.  This repackages `Module.Basis.repr_symm_single`, which it runs
through in the same direction, for the common situation where what one holds is a bound on the
support rather than an explicit `Finsupp.single`.

Nothing here needs more than a semiring of scalars, since only `Finsupp.support_subset_singleton`
and the coordinate isomorphism are involved.

## Main results

* `Module.Basis.eq_smul_of_repr_support_subset_singleton`: a vector supported on one coordinate is
  that coordinate times the corresponding basis vector.
-/

public section

namespace Module.Basis

variable {ι K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

/-- **A vector whose only possibly nonzero coordinate is the `i`-th one is that coordinate times
the `i`-th basis vector.** -/
theorem eq_smul_of_repr_support_subset_singleton (b : Module.Basis ι K V) {w : V} {i : ι}
    (h : (b.repr w).support ⊆ {i}) : w = b.repr w i • b i :=
  calc w = b.repr.symm (b.repr w) := (b.repr.symm_apply_apply w).symm
    _ = b.repr.symm (Finsupp.single i (b.repr w i)) :=
        congrArg _ (Finsupp.support_subset_singleton.1 h)
    _ = b.repr w i • b i := b.repr_symm_single i _

/-- A linear map carrying one basis to another preserves the corresponding coordinates. -/
theorem repr_map_eq_of_map_basis
    {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (b : Module.Basis ι R M) (c : Module.Basis ι R N) (f : M →ₗ[R] N)
    (hf : ∀ i, f (b i) = c i) (x : M) : c.repr (f x) = b.repr x := by
  have h : c.repr.toLinearMap ∘ₗ f = b.repr.toLinearMap := by
    apply b.ext
    intro i
    exact (congrArg c.repr (hf i)).trans
      ((c.repr_self i).trans (b.repr_self i).symm)
  exact DFunLike.congr_fun h x

end Module.Basis
