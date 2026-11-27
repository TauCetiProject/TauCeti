/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.Algebra.Module.Lattice

/-!
# Tensor products of full lattices

For full `R`-lattices `L ⊆ V` and `M ⊆ W` over a localization `K`, their tensor lattice
is the existing bilinear image
`Submodule.map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M`.
It is a full lattice in `V ⊗[K] W`. If `L` is free and full, its abstract tensor product
with any submodule `M` embeds in the ambient tensor product and is isomorphic to this image.
The image is free when `M` is also free. Thus the embedded lattice retains the tensor product
of the integral modules, rather than merely its rank. This is needed for tensor operations on
vector spaces with period lattices.

The tensor map and range formula in `TensorProduct.Submodule` use Mathlib's
`TensorProduct.map₂_eq_range_lift_comp_mapIncl`. The embedding uses
`Submodule.isBaseChange_subtype` and `TensorProduct.cancelBaseChangeLeft`, with flatness of
free modules. Fullness uses Mathlib's `Submodule.FG.map₂` and
`LinearIndependent.localization`. No additional lattice structure is introduced.
-/

public section

open Module TensorProduct

namespace Submodule

variable {R K V W : Type*} [CommRing R]

section CommRing

variable [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

/-- The tensor product of a free full lattice and any submodule embeds in the tensor product
of the ambient modules. -/
theorem tensorProductMap_injective (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [Module.Free R L] :
    Function.Injective (L.tensorProductMap (K := K) M) := by
  let e : L ⊗[R] W ≃ₗ[R] V ⊗[K] W :=
    (TensorProduct.cancelBaseChangeLeft R K L W).symm.trans
      (((L.isBaseChange_subtype (K := K)).equiv.rTensor W).restrictScalars R)
  have h : L.tensorProductMap (K := K) M = e.toLinearMap.comp (M.subtype.lTensor L) := by
    ext x y
    simp [e, IsBaseChange.equiv_tmul]
  rw [h]
  exact e.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap M.subtype M.injective_subtype)

/-- The abstract tensor product of a free full lattice and any submodule is canonically
isomorphic to their bilinear image in the ambient tensor product. -/
noncomputable def tensorProductEquiv (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [Module.Free R L] :
    L ⊗[R] M ≃ₗ[R] map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M :=
  (LinearEquiv.ofInjective (L.tensorProductMap M) (L.tensorProductMap_injective M)).trans
    (LinearEquiv.ofEq _ _ (L.range_tensorProductMap M))

/-- The tensor-lattice equivalence agrees with the ambient tensor map. -/
@[simp]
theorem coe_tensorProductEquiv_apply (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [Module.Free R L]
    (z : L ⊗[R] M) :
    (L.tensorProductEquiv (K := K) M z : V ⊗[K] W) = L.tensorProductMap M z := by
  simp [tensorProductEquiv]

/-- The tensor-lattice equivalence sends a pure tensor to its ambient realization. -/
@[simp]
theorem tensorProductEquiv_tmul (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [Module.Free R L] (x : L) (y : M) :
    L.tensorProductEquiv (K := K) M (x ⊗ₜ[R] y) =
      ⟨(x : V) ⊗ₜ[K] (y : W), apply_mem_map₂ _ x.property y.property⟩ := by
  apply Subtype.ext
  simp

/-- The inverse tensor-lattice equivalence recovers a pure integral tensor from its
ambient realization. -/
@[simp]
theorem tensorProductEquiv_symm_tmul (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [Module.Free R L]
    (x : L) (y : M) :
    (L.tensorProductEquiv (K := K) M).symm
      ⟨(x : V) ⊗ₜ[K] (y : W), apply_mem_map₂ _ x.property y.property⟩ = x ⊗ₜ[R] y := by
  apply (L.tensorProductEquiv (K := K) M).injective
  apply Subtype.ext
  simp

/-- The tensor image of a free full lattice and a free submodule is free,
without a PID hypothesis. -/
instance free_map₂_tensorProductMk (L : Submodule R V) (M : Submodule R W)
    [L.IsFullLattice K] [Module.Free R L] [Module.Free R M] :
    Module.Free R (map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M) :=
  Module.Free.of_equiv (L.tensorProductEquiv (K := K) M)

/-- The bilinear image of two full lattices is a full lattice in the tensor product
over a localization. Freeness of the lattices is not needed for fullness. -/
theorem isFullLattice_map₂_tensorProductMk_of_isLocalization
    (L : Submodule R V) (M : Submodule R W) (S : Submonoid R) [IsLocalization S K]
    [L.IsFullLattice K] [M.IsFullLattice K] :
    (map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M).IsFullLattice K where
  fg := (IsLattice.fg K L).map₂ _ (IsLattice.fg K M)
  linearIndepOn _ _ h := h.localization K S
  span_eq_top := by
    rw [map₂_eq_span_image2, span_span_of_tower]
    simp only [LinearMap.restrictScalars₁₂_apply_apply]
    rw [← map₂_span_span K (TensorProduct.mk K V W),
      IsFullLattice.span_eq_top, IsFullLattice.span_eq_top,
      TensorProduct.map₂_mk_top_top_eq_top]

end CommRing

section Field

variable [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

/-- Over the fraction field, the tensor image of full lattices is a full lattice. -/
instance isFullLattice_map₂_tensorProductMk
    (L : Submodule R V) (M : Submodule R W) [L.IsFullLattice K] [M.IsFullLattice K] :
    (map₂ ((TensorProduct.mk K V W).restrictScalars₁₂ R R) L M).IsFullLattice K :=
  isFullLattice_map₂_tensorProductMk_of_isLocalization L M (nonZeroDivisors R)

end Field

end Submodule
