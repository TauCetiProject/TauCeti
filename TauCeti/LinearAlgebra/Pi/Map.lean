/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Kernel, range and cokernel of a coordinatewise linear map

For a family of linear maps `f i : M i → N i`, the coordinatewise map
`LinearMap.piMap f : (∀ i, M i) → (∀ i, N i)` acts on each coordinate separately. Its kernel and
its range are therefore the products of the kernels and of the ranges of the `f i`
(`LinearMap.ker_piMap`, `LinearMap.range_piMap`). This gives the kernel splitting
`ker (piMap f) ≃ ∀ i, ker (f i)` (`LinearMap.kerPiMapEquiv`) and, for finitely many indices, the
cokernel splitting `(∀ i, N i) ⧸ range (piMap f) ≃ ∀ i, N i ⧸ range (f i)`
(`LinearMap.cokerPiMapEquiv`), through Mathlib's `Submodule.quotientPi`, over a commutative
ring. In particular a finite
family of maps with finite kernels and cokernels has a coordinatewise map with finite kernel and
cokernel.

These are the finite-family analogues of the kernel and cokernel of a direct sum
`LinearMap.prodMap`, and they compute the determinant line of a coordinatewise map of Fredholm
operators.
-/

public section

namespace LinearMap

section Semiring

variable {R : Type*} [Semiring R] {ι : Type*} {M N : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

theorem mem_ker_piMap {x : ∀ i, M i} : x ∈ ker (piMap f) ↔ ∀ i, x i ∈ ker (f i) := by
  simp [funext_iff, Pi.map_apply]

/-- The kernel of a coordinatewise map is the product of the kernels. -/
@[simp]
theorem ker_piMap : ker (piMap f) = Submodule.pi Set.univ fun i ↦ ker (f i) := by
  ext x
  simp only [mem_ker_piMap, Submodule.mem_pi, Set.mem_univ, forall_const]

/-- The range of a coordinatewise map is the product of the ranges. -/
@[simp]
theorem range_piMap : range (piMap f) = Submodule.pi Set.univ fun i ↦ range (f i) :=
  SetLike.coe_injective <| by
    simpa only [coe_range, coe_piMap, Submodule.coe_pi] using Set.range_piMap fun i ↦ ⇑(f i)

/-- **The kernel of a coordinatewise map** is the product of the kernels of its components. -/
def kerPiMapEquiv : ker (piMap f) ≃ₗ[R] ∀ i, ker (f i) where
  toFun x i := ⟨x.val i, (mem_ker_piMap f).1 x.property i⟩
  invFun y := ⟨fun i ↦ y i, (mem_ker_piMap f).2 fun i ↦ (y i).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_kerPiMapEquiv_apply (x : ker (piMap f)) (i : ι) :
    (kerPiMapEquiv f x i : M i) = (x : ∀ i, M i) i :=
  (rfl)

@[simp]
theorem coe_kerPiMapEquiv_symm_apply (y : ∀ i, ker (f i)) :
    ((kerPiMapEquiv f).symm y : ∀ i, M i) = fun i ↦ (y i : M i) :=
  (rfl)

instance [Finite ι] [∀ i, Module.Finite R (ker (f i))] : Module.Finite R (ker (piMap f)) :=
  Module.Finite.equiv (kerPiMapEquiv f).symm

end Semiring

section CommRing

variable {R : Type*} [CommRing R] {ι : Type*} {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

section Fintype

variable [Fintype ι] [DecidableEq ι]

/-- **The cokernel of a coordinatewise map** over finitely many indices is the product of the
cokernels of its components: the class of `y` goes to the family of the classes of the `y i`
(`LinearMap.cokerPiMapEquiv_mk`). -/
def cokerPiMapEquiv : ((∀ i, N i) ⧸ range (piMap f)) ≃ₗ[R] ∀ i, N i ⧸ range (f i) :=
  Submodule.quotEquivOfEq _ _ (range_piMap f) ≪≫ₗ Submodule.quotientPi _

@[simp]
theorem cokerPiMapEquiv_mk (y : ∀ i, N i) :
    cokerPiMapEquiv f (Submodule.Quotient.mk y) = fun i ↦ Submodule.Quotient.mk (y i) := by
  funext i
  simp [cokerPiMapEquiv]

@[simp]
theorem cokerPiMapEquiv_symm_apply (y : ∀ i, N i) :
    (cokerPiMapEquiv f).symm (fun i ↦ Submodule.Quotient.mk (y i)) = Submodule.Quotient.mk y := by
  rw [LinearEquiv.symm_apply_eq, cokerPiMapEquiv_mk]

end Fintype

instance [Finite ι] [∀ i, Module.Finite R (N i ⧸ range (f i))] :
    Module.Finite R ((∀ i, N i) ⧸ range (piMap f)) := by
  have := Fintype.ofFinite ι
  classical
  exact Module.Finite.equiv (cokerPiMapEquiv f).symm

end CommRing

end LinearMap
