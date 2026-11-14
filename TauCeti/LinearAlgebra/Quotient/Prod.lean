/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Quotients by products of submodules

The quotient by a product submodule is the product of the two quotients:

`(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.

Mathlib has the additive-group form of this statement,
`QuotientAddGroup.prodAddEquiv`; `quotientProdEquiv` below records the analogous scalar-compatible
equivalence, which is the form module-theoretic consumers need. There is no submodule form upstream.

## Main declarations

* `Submodule.quotientProdEquiv`: `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.
* `Submodule.finrank_quotient_prod`: the ranks of the quotients add, and the quotient is finite
  (`Submodule.finite_quotient_prod`) or free (`Submodule.free_quotient_prod`) when both
  quotients are.
* `LinearMap.cokerProdMapEquiv`: the cokernel of `f.prodMap g` is `coker f × coker g`.
* `LinearMap.finrank_quotient_range_prodMap`: the cokernel of `f.prodMap g` has rank
  `rank coker f + rank coker g`, and is finite when those of `f` and `g` are
  (`LinearMap.finite_quotient_range_prodMap`) or free (`LinearMap.free_quotient_range_prodMap`).

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

/-- The quotient by a product of submodules is finite when the two quotients are. -/
instance finite_quotient_prod (p : Submodule R M) (q : Submodule R N) [Module.Finite R (M ⧸ p)]
    [Module.Finite R (N ⧸ q)] : Module.Finite R ((M × N) ⧸ p.prod q) :=
  .equiv (quotientProdEquiv p q).symm

/-- The quotient by a product of submodules is free when the two quotients are. -/
instance free_quotient_prod (p : Submodule R M) (q : Submodule R N) [Module.Free R (M ⧸ p)]
    [Module.Free R (N ⧸ q)] : Module.Free R ((M × N) ⧸ p.prod q) :=
  .of_equiv (quotientProdEquiv p q).symm

end Quotient

end Submodule

namespace LinearMap

variable {R : Type*} [Ring R] {M N M' N' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (f : M →ₗ[R] N) (g : M' →ₗ[R] N')

/-- The cokernel of `f.prodMap g` is the product of the cokernels of `f` and `g`. -/
def cokerProdMapEquiv : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[R] (N ⧸ range f) × (N' ⧸ range g) :=
  (Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans (Submodule.quotientProdEquiv _ _)

@[simp]
theorem cokerProdMapEquiv_apply_mk (x : N × N') :
    cokerProdMapEquiv f g (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  simp [cokerProdMapEquiv]

@[simp]
theorem cokerProdMapEquiv_symm_apply_mk (x : N) (y : N') :
    (cokerProdMapEquiv f g).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) := by
  rw [LinearEquiv.symm_apply_eq, cokerProdMapEquiv_apply_mk]

@[simp]
theorem cokerProdMapEquiv_symm_apply_mk_zero (x : N) :
    (cokerProdMapEquiv f g).symm (Submodule.Quotient.mk x, 0) = Submodule.Quotient.mk (x, 0) := by
  rw [← Submodule.Quotient.mk_zero, cokerProdMapEquiv_symm_apply_mk]

@[simp]
theorem cokerProdMapEquiv_symm_apply_zero_mk (y : N') :
    (cokerProdMapEquiv f g).symm (0, Submodule.Quotient.mk y) = Submodule.Quotient.mk (0, y) := by
  rw [← Submodule.Quotient.mk_zero, cokerProdMapEquiv_symm_apply_mk]

/-- The cokernel of `f.prodMap g` is finite when those of `f` and `g` are. -/
instance finite_quotient_range_prodMap [Module.Finite R (N ⧸ range f)]
    [Module.Finite R (N' ⧸ range g)] : Module.Finite R ((N × N') ⧸ range (f.prodMap g)) :=
  .equiv (cokerProdMapEquiv f g).symm

/-- The cokernel of `f.prodMap g` is free when those of `f` and `g` are. -/
instance free_quotient_range_prodMap [Module.Free R (N ⧸ range f)]
    [Module.Free R (N' ⧸ range g)] : Module.Free R ((N × N') ⧸ range (f.prodMap g)) :=
  .of_equiv (cokerProdMapEquiv f g).symm

/-- The cokernel of `f.prodMap g` has rank `rank coker f + rank coker g`. -/
@[simp]
theorem finrank_quotient_range_prodMap [StrongRankCondition R] [Module.Free R (N ⧸ range f)]
    [Module.Free R (N' ⧸ range g)] [Module.Finite R (N ⧸ range f)]
    [Module.Finite R (N' ⧸ range g)] :
    Module.finrank R ((N × N') ⧸ range (f.prodMap g)) =
      Module.finrank R (N ⧸ range f) + Module.finrank R (N' ⧸ range g) := by
  rw [range_prodMap]
  exact Submodule.finrank_quotient_prod _ _

end LinearMap
