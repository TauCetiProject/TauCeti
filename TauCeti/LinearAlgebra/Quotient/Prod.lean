/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotients by products of submodules

The quotient by a product submodule is the product of the two quotients:

`(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.

Mathlib has the additive-group form of this statement,
`QuotientAddGroup.prodAddEquiv`; `quotientProdEquiv` below records the analogous scalar-compatible
equivalence, which is the form module-theoretic consumers need. There is no submodule form upstream.
In particular the cokernel of a product map `f.prodMap g` is the product of the cokernels.

## Main declarations

* `Submodule.quotientProdEquiv`: `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.
* `Submodule.finrank_quotient_prod`: the ranks of the quotients add.
* `LinearMap.quotientRangeProdMapEquiv`: the cokernel of `f.prodMap g` is linearly equivalent to
  the product of the cokernels of `f` and `g`.

## Implementation notes

`quotientProdEquiv` is assembled from `Submodule.liftQ`, `Submodule.mapQ` and `LinearMap.coprod`,
so its computation rules are stated in the `Submodule.Quotient.mk` API rather than through
`AddEquiv` wrappers.
-/

public section

namespace Submodule

section Quotient

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- The quotient by a product of submodules is the product of the quotients.

This is the module analogue of `QuotientAddGroup.prodAddEquiv`. Its action and inverse action on
quotient representatives are recorded by `quotientProdEquiv_apply_mk` and
`quotientProdEquiv_symm_apply_mk`. -/
def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) :=
  .ofLinearMap ((p.prod q).liftQ (p.mkQ.prodMap q.mkQ) (by simp))
    ((p.mapQ _ (.inl R M N) (prod_comap_inl p q).ge).coprod
      (q.mapQ _ (.inr R M N) (prod_comap_inr p q).ge))
    (by ext <;> simp) (by ext <;> simp)

@[simp]
theorem quotientProdEquiv_apply_mk (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdEquiv p q (Quotient.mk x) = (Quotient.mk x.1, Quotient.mk x.2) := by
  simp [quotientProdEquiv]

@[simp]
theorem quotientProdEquiv_symm_apply_mk
    (p : Submodule R M) (q : Submodule R N) (x : M) (y : N) :
    (quotientProdEquiv p q).symm (Quotient.mk x, Quotient.mk y) = Quotient.mk (x, y) := by
  simp [quotientProdEquiv, ← Quotient.mk_add]

/-- The quotient by a product of submodules has rank the sum of the two quotients' ranks. -/
@[simp]
theorem finrank_quotient_prod [StrongRankCondition R] (p : Submodule R M) (q : Submodule R N)
    [Module.Free R (M ⧸ p)] [Module.Free R (N ⧸ q)]
    [Module.Finite R (M ⧸ p)] [Module.Finite R (N ⧸ q)] :
    Module.finrank R ((M × N) ⧸ p.prod q)
      = Module.finrank R (M ⧸ p) + Module.finrank R (N ⧸ q) := by
  rw [(quotientProdEquiv p q).finrank_eq, Module.finrank_prod]

end Quotient

end Submodule

namespace LinearMap

variable {R M N M' N' : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

/-- The cokernel of the product map `f.prodMap g` is the product of the cokernels of `f` and `g`:
`(N × N') ⧸ range (f.prodMap g) ≃ (N ⧸ range f) × (N' ⧸ range g)`. -/
def quotientRangeProdMapEquiv (f : M →ₗ[R] N) (g : M' →ₗ[R] N') :
    ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[R] (N ⧸ range f) × (N' ⧸ range g) :=
  (Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans (Submodule.quotientProdEquiv _ _)

@[simp]
theorem quotientRangeProdMapEquiv_apply_mk (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (x : N × N') :
    quotientRangeProdMapEquiv f g (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  simp [quotientRangeProdMapEquiv]

@[simp]
theorem quotientRangeProdMapEquiv_symm_apply_mk (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (x : N)
    (y : N') :
    (quotientRangeProdMapEquiv f g).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) := by
  rw [LinearEquiv.symm_apply_eq, quotientRangeProdMapEquiv_apply_mk]

end LinearMap
