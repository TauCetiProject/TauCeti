/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Kernel, range and cokernel of a coordinatewise linear map

For a family of linear maps `f i : M i → N i`, the coordinatewise map
`LinearMap.piMap f : (∀ i, M i) → (∀ i, N i)` acts on each coordinate separately. Its kernel and
its range are therefore the products of the kernels and of the ranges of the `f i`
(`LinearMap.ker_piMap`, `LinearMap.range_piMap`). This gives the kernel splitting
`ker (piMap f) ≃ ∀ i, ker (f i)` (`LinearMap.kerPiMapEquiv`) and, over a ring, the cokernel
splitting `(∀ i, N i) ⧸ range (piMap f) ≃ ∀ i, N i ⧸ range (f i)` (`LinearMap.cokerPiMapEquiv`),
for any index type. In particular a finite family of maps with finite kernels and cokernels has a
coordinatewise map with finite kernel and cokernel, and when these are free their ranks add
(`LinearMap.finrank_ker_piMap`, `LinearMap.finrank_quotient_range_piMap`).

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

/-- The kernel of a finite coordinatewise map has rank the sum of the ranks of the kernels of its
components. -/
@[simp]
theorem finrank_ker_piMap [Fintype ι] [StrongRankCondition R] [∀ i, Module.Free R (ker (f i))]
    [∀ i, Module.Finite R (ker (f i))] :
    Module.finrank R (ker (piMap f)) = ∑ i, Module.finrank R (ker (f i)) := by
  rw [(kerPiMapEquiv f).finrank_eq, Module.finrank_pi_fintype]

end Semiring

section Ring

variable {R : Type*} [Ring R] {ι : Type*} {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

/-- **The cokernel of a coordinatewise map** is the product of the cokernels of its components:
the class of `y` goes to the family of the classes of the `y i` (`LinearMap.cokerPiMapEquiv_mk`). -/
noncomputable def cokerPiMapEquiv : ((∀ i, N i) ⧸ range (piMap f)) ≃ₗ[R] ∀ i, N i ⧸ range (f i) :=
  Submodule.quotEquivOfEq _ _ (by simp only [range_piMap, ker_piMap, Submodule.ker_mkQ]) ≪≫ₗ
    (piMap fun i ↦ (range (f i)).mkQ).quotKerEquivOfSurjective
      (by simpa using Function.Surjective.piMap fun i ↦ (range (f i)).mkQ_surjective)

@[simp]
theorem cokerPiMapEquiv_mk (y : ∀ i, N i) :
    cokerPiMapEquiv f (Submodule.Quotient.mk y) = fun i ↦ Submodule.Quotient.mk (y i) := by
  funext i
  simp [cokerPiMapEquiv]

@[simp]
theorem cokerPiMapEquiv_symm_apply (y : ∀ i, N i) :
    (cokerPiMapEquiv f).symm (fun i ↦ Submodule.Quotient.mk (y i)) = Submodule.Quotient.mk y := by
  rw [LinearEquiv.symm_apply_eq, cokerPiMapEquiv_mk]

instance [Finite ι] [∀ i, Module.Finite R (N i ⧸ range (f i))] :
    Module.Finite R ((∀ i, N i) ⧸ range (piMap f)) :=
  Module.Finite.equiv (cokerPiMapEquiv f).symm

/-- The cokernel of a finite coordinatewise map has rank the sum of the ranks of the cokernels of
its components. -/
@[simp]
theorem finrank_quotient_range_piMap [Fintype ι] [StrongRankCondition R]
    [∀ i, Module.Free R (N i ⧸ range (f i))] [∀ i, Module.Finite R (N i ⧸ range (f i))] :
    Module.finrank R ((∀ i, N i) ⧸ range (piMap f)) =
      ∑ i, Module.finrank R (N i ⧸ range (f i)) := by
  rw [(cokerPiMapEquiv f).finrank_eq, Module.finrank_pi_fintype]

end Ring

end LinearMap
