/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Dimensions of products

Mathlib's `Module.finrank_prod` computes the dimension of `M × M'` for finite free modules. For
`M × M` no finiteness is needed: if `M` is not finite then neither is `M × M`, and both
dimensions are `0` by convention. So `finrank (M × M) = 2 * finrank M` for every free module `M`
over a semiring with the strong rank condition (`Module.finrank_prod_self`).

For linear maps `f` and `g`, the kernel of `f.prodMap g` is `ker f × ker g`
(`LinearMap.kerProdMapEquiv`), so it is finite when those of `f` and `g` are
(`LinearMap.finite_ker_prodMap`), with rank `rank ker f + rank ker g` when they are free
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

variable {R : Type*} [Semiring R] {M N M' N' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
  (f : M →ₗ[R] N) (g : M' →ₗ[R] N')

/-- The kernel of `f.prodMap g` is the product of the kernels of `f` and `g`. -/
def kerProdMapEquiv : ker (f.prodMap g) ≃ₗ[R] ker f × ker g :=
  (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv _ _)

@[simp]
theorem coe_kerProdMapEquiv_apply_fst (x : ker (f.prodMap g)) :
    ((kerProdMapEquiv f g x).1 : M) = (x : M × M').1 := by
  simp [kerProdMapEquiv]

@[simp]
theorem coe_kerProdMapEquiv_apply_snd (x : ker (f.prodMap g)) :
    ((kerProdMapEquiv f g x).2 : M') = (x : M × M').2 := by
  simp [kerProdMapEquiv]

@[simp]
theorem coe_kerProdMapEquiv_symm_apply (x : ker f × ker g) :
    ((kerProdMapEquiv f g).symm x : M × M') = ((x.1 : M), (x.2 : M')) := by
  simp [kerProdMapEquiv]

/-- The kernel of `f.prodMap g` is finite when those of `f` and `g` are. -/
instance finite_ker_prodMap [Module.Finite R (ker f)] [Module.Finite R (ker g)] :
    Module.Finite R (ker (f.prodMap g)) :=
  .equiv (kerProdMapEquiv f g).symm

/-- The kernel of `f.prodMap g` has rank `rank ker f + rank ker g`. -/
theorem finrank_ker_prodMap [StrongRankCondition R] [Module.Free R (ker f)]
    [Module.Free R (ker g)] [Module.Finite R (ker f)] [Module.Finite R (ker g)] :
    Module.finrank R (ker (f.prodMap g)) = Module.finrank R (ker f) + Module.finrank R (ker g) := by
  rw [(kerProdMapEquiv f g).finrank_eq, Module.finrank_prod]

end LinearMap
