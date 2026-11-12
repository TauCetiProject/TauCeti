/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Dimensions of products

Mathlib's `Module.finrank_prod` computes the dimension of `M × M'` for finite free modules. For
`M × M` no finiteness is needed: if `M` is not finite then neither is `M × M`, and both
dimensions are `0` by convention. So `finrank (M × M) = 2 * finrank M` for every free module `M`
over a semiring with the strong rank condition (`Module.finrank_prod_self`).

For linear maps `f` and `g` between vector spaces, the kernel of `f.prodMap g` is
`ker f × ker g` (`LinearMap.ker_prodMap`), so it is finite-dimensional when those of `f` and `g`
are (`LinearMap.finiteDimensional_ker_prodMap`), with dimension `dim ker f + dim ker g`
(`LinearMap.finrank_ker_prodMap`).
-/

public section

namespace Module

variable (R M : Type*) [Semiring R] [StrongRankCondition R] [AddCommMonoid M] [Module R M]
  [Module.Free R M]

/-- The dimension of `M × M` is twice that of `M`, whether or not `M` is finite. -/
theorem finrank_prod_self : finrank R (M × M) = 2 * finrank R M := by
  by_cases hM : Module.Finite R M
  · rw [Module.finrank_prod, two_mul]
  · have : ¬ Module.Finite R (M × M) := fun h =>
      hM (Module.Finite.of_surjective (LinearMap.fst R M M) Prod.fst_surjective)
    rw [finrank_of_not_finite hM, finrank_of_not_finite this, mul_zero]

end Module

namespace LinearMap

variable {K : Type*} [Field K] {M N M' N' : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  (f : M →ₗ[K] N) (g : M' →ₗ[K] N') [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]

/-- The kernel of `f.prodMap g` is finite-dimensional when those of `f` and `g` are. -/
instance finiteDimensional_ker_prodMap : FiniteDimensional K (ker (f.prodMap g)) :=
  ((LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans
    (Submodule.prodEquiv (ker f) (ker g))).symm.finiteDimensional

/-- The kernel of `f.prodMap g` has dimension `dim ker f + dim ker g`. -/
theorem finrank_ker_prodMap :
    Module.finrank K (ker (f.prodMap g)) = Module.finrank K (ker f) + Module.finrank K (ker g) := by
  rw [((LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans
    (Submodule.prodEquiv (ker f) (ker g))).finrank_eq, Module.finrank_prod]

end LinearMap
