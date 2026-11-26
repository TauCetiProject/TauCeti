/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Module.Lattice

/-!
# Tensor products of full lattices

For full `R`-lattices `L ⊆ V` and `M ⊆ W` in vector spaces over the fraction field `K`,
their tensor lattice is the existing bilinear image
`Submodule.map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M`.
It is a full lattice in `V ⊗[K] W`. If the two lattices are free, their abstract tensor
product over `R` embeds in the ambient tensor product and is isomorphic to this image.
Thus the embedded lattice retains the tensor product of the integral modules, rather than
merely its rank. This is needed for tensor operations on vector spaces with period lattices.

The construction uses Mathlib's full-lattice predicate and tensor-product bases, and the
extension of lattice bases to ambient bases. No additional lattice structure is introduced.
-/

public section

open Module TensorProduct

namespace Submodule

variable {R K V W : Type*} [CommRing R]

section CommRing

variable [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

/-- The map from the tensor product of two integral submodules to the tensor product
of their ambient modules over the larger scalar ring. -/
def tensorProductMap (L : Submodule R V) (M : Submodule R W) :
    L ⊗[R] M →ₗ[R] V ⊗[K] W :=
  (TensorProduct.lift ((TensorProduct.mk K V W).restrictScalars₁₂ R R)).comp
    (TensorProduct.mapIncl L M)

/-- The tensor map sends a pure integral tensor to the corresponding ambient tensor. -/
@[simp]
theorem tensorProductMap_tmul (L : Submodule R V) (M : Submodule R W) (x : L) (y : M) :
    L.tensorProductMap M (x ⊗ₜ[R] y) = (x : V) ⊗ₜ[K] (y : W) := (rfl)

/-- The tensor map has as image the bilinear image of the two submodules. -/
@[simp]
theorem range_tensorProductMap (L : Submodule R V) (M : Submodule R W) :
    LinearMap.range (L.tensorProductMap (K := K) M) =
      map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M :=
  (TensorProduct.map₂_eq_range_lift_comp_mapIncl _ L M).symm

variable [FaithfulSMul R K]

/-- The tensor product of free full lattices embeds in the tensor product of the
ambient modules. The coefficient algebra need only be commutative and faithful over `R`. -/
theorem tensorProductMap_injective (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [M.IsFullLattice K] [Module.Free R L] [Module.Free R M] :
    Function.Injective (L.tensorProductMap (K := K) M) := by
  let b := Module.Free.chooseBasis R L
  let c := Module.Free.chooseBasis R M
  have h := ((b.extendOfIsFullLattice K).tensorProduct
    (c.extendOfIsFullLattice K)).linearIndependent.restrict_scalars' R
  have heq : (b.tensorProduct c).constr R
      (fun i ↦ ((b.extendOfIsFullLattice K).tensorProduct (c.extendOfIsFullLattice K)) i) =
      L.tensorProductMap (K := K) M := by
    apply (b.tensorProduct c).ext
    rintro ⟨i, j⟩
    rw [Basis.constr_basis]
    simp
  rw [← heq]
  exact (b.tensorProduct c).injective_constr_of_linearIndependent h

/-- The abstract tensor product of two free full lattices is canonically isomorphic to
their bilinear image in the ambient tensor product. -/
noncomputable def tensorProductEquiv (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [M.IsFullLattice K] [Module.Free R L] [Module.Free R M] :
    L ⊗[R] M ≃ₗ[R] map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M :=
  (LinearEquiv.ofInjective (L.tensorProductMap M) (L.tensorProductMap_injective M)).trans
    (LinearEquiv.ofEq _ _ (L.range_tensorProductMap M))

/-- The tensor-lattice equivalence agrees with the ambient tensor map. -/
@[simp]
theorem coe_tensorProductEquiv_apply (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [M.IsFullLattice K] [Module.Free R L] [Module.Free R M]
    (z : L ⊗[R] M) :
    (L.tensorProductEquiv (K := K) M z : V ⊗[K] W) = L.tensorProductMap M z := by
  simp [tensorProductEquiv]

/-- The inverse tensor-lattice equivalence recovers a pure integral tensor from its
ambient realization. -/
@[simp]
theorem tensorProductEquiv_symm_tmul (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [M.IsFullLattice K] [Module.Free R L] [Module.Free R M]
    (x : L) (y : M) :
    (L.tensorProductEquiv (K := K) M).symm
      ⟨(x : V) ⊗ₜ[K] (y : W), apply_mem_map₂ _ x.property y.property⟩ = x ⊗ₜ[R] y := by
  apply (L.tensorProductEquiv (K := K) M).injective
  apply Subtype.ext
  simp

/-- The tensor lattice of two free full lattices is free, without a PID hypothesis. -/
instance free_map₂_tensorProduct (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [M.IsFullLattice K] [Module.Free R L] [Module.Free R M] :
    Module.Free R (map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M) :=
  Module.Free.of_equiv (L.tensorProductEquiv (K := K) M)

end CommRing

section Field

variable [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

/-- The bilinear image of two full lattices is a full lattice in the tensor product
over the fraction field. Freeness of the lattices is not needed for fullness. -/
instance isFullLattice_map₂_tensorProduct
    (L : Submodule R V) (M : Submodule R W) [L.IsFullLattice K] [M.IsFullLattice K] :
    (map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M).IsFullLattice K where
  __ := IsLattice.of_fg K
    ((IsLattice.fg K L).map₂ _ (IsLattice.fg K M))
  span_eq_top := by
    rw [map₂_eq_span_image2, span_span_of_tower]
    simp only [LinearMap.restrictScalars₁₂_apply_apply]
    rw [← map₂_span_span K (TensorProduct.mk K V W),
      IsFullLattice.span_eq_top, IsFullLattice.span_eq_top,
      TensorProduct.map₂_mk_top_top_eq_top]

end Field

end Submodule
