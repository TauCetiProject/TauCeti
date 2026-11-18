/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.LinearAlgebra.LinearMap.Prod

/-!
# Dimensions of products

Mathlib's `Module.finrank_prod` computes the dimension of `M × M'` for finite free modules. For
`M × M` no finiteness is needed: if `M` is not finite then neither is `M × M`, and both
dimensions are `0` by convention. So `finrank (M × M) = 2 * finrank M` for every free module `M`
over a semiring with the strong rank condition (`Module.finrank_prod_self`).

A product `p.prod q` of finite free submodules has rank `rank p + rank q`
(`Submodule.finrank_prod`). In particular, for linear maps `f` and `g` the kernel of
`f.prodMap g`, which is `ker f × ker g` (`LinearMap.kerProdMapEquiv`), has rank
`rank ker f + rank ker g` (`LinearMap.finrank_ker_prodMap`).
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

namespace Submodule

variable {R M M' : Type*} [Semiring R] [StrongRankCondition R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] (p : Submodule R M) (q : Submodule R M')

/-- A product of finite free submodules has rank the sum of their ranks. -/
@[simp]
theorem finrank_prod [Module.Free R p] [Module.Free R q] [Module.Finite R p] [Module.Finite R q] :
    Module.finrank R (p.prod q) = Module.finrank R p + Module.finrank R q := by
  rw [(p.prodEquiv q).finrank_eq, Module.finrank_prod]

end Submodule

namespace LinearMap

variable {R : Type*} [Semiring R] {M N M' N' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
  (f : M →ₗ[R] N) (g : M' →ₗ[R] N')

/-- The kernel of `f.prodMap g` has rank `rank ker f + rank ker g`. -/
@[simp]
theorem finrank_ker_prodMap [StrongRankCondition R] [Module.Free R (ker f)]
    [Module.Free R (ker g)] [Module.Finite R (ker f)] [Module.Finite R (ker g)] :
    Module.finrank R (ker (f.prodMap g)) = Module.finrank R (ker f) + Module.finrank R (ker g) := by
  rw [ker_prodMap]
  exact Submodule.finrank_prod _ _

end LinearMap
