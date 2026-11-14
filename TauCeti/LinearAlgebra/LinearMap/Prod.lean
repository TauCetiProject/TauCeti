/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Kernels of products of linear maps

A product `p.prod q` of submodules is isomorphic to `p × q` (`Submodule.prodEquiv`), so it is
finite (`Submodule.finite_prod`) and free (`Submodule.free_prod`) when `p` and `q` are.

For linear maps `f` and `g`, the kernel of `f.prodMap g` is `ker f × ker g`
(`LinearMap.kerProdMapEquiv`), so it is finite (`LinearMap.finite_ker_prodMap`) and free
(`LinearMap.free_ker_prodMap`) when those of `f` and `g` are.
-/

public section

namespace Submodule

variable {R : Type*} [Semiring R] {M M' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] (p : Submodule R M) (q : Submodule R M')

/-- A product of finite submodules is finite. -/
instance finite_prod [Module.Finite R p] [Module.Finite R q] : Module.Finite R (p.prod q) :=
  .equiv (p.prodEquiv q).symm

/-- A product of free submodules is free. -/
instance free_prod [Module.Free R p] [Module.Free R q] : Module.Free R (p.prod q) :=
  .of_equiv (p.prodEquiv q).symm

end Submodule

namespace LinearMap

variable {R : Type*} [Semiring R] {M N M' N' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
  (f : M →ₗ[R] N) (g : M' →ₗ[R] N')

/-- The kernel of `f.prodMap g` is the product of the kernels of `f` and `g`. -/
def kerProdMapEquiv : ker (f.prodMap g) ≃ₗ[R] ker f × ker g :=
  (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv _ _)

@[simp]
theorem kerProdMapEquiv_apply (x : ker (f.prodMap g)) :
    kerProdMapEquiv f g x =
      (⟨(x : M × M').1, congrArg Prod.fst (mem_ker.mp x.2)⟩,
        ⟨(x : M × M').2, congrArg Prod.snd (mem_ker.mp x.2)⟩) := by
  ext <;> simp [kerProdMapEquiv]

@[simp]
theorem kerProdMapEquiv_symm_apply (x : ker f × ker g) :
    (kerProdMapEquiv f g).symm x =
      ⟨((x.1 : M), (x.2 : M')), mem_ker.mpr (Prod.ext (mem_ker.mp x.1.2) (mem_ker.mp x.2.2))⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  ext <;> simp

/-- The kernel of `f.prodMap g` is finite when those of `f` and `g` are. -/
instance finite_ker_prodMap [Module.Finite R (ker f)] [Module.Finite R (ker g)] :
    Module.Finite R (ker (f.prodMap g)) :=
  .equiv (kerProdMapEquiv f g).symm

/-- The kernel of `f.prodMap g` is free when those of `f` and `g` are. -/
instance free_ker_prodMap [Module.Free R (ker f)] [Module.Free R (ker g)] :
    Module.Free R (ker (f.prodMap g)) :=
  .of_equiv (kerProdMapEquiv f g).symm

end LinearMap
