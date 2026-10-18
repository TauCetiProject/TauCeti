/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Data.Fintype.Option
import TauCeti.LinearAlgebra.PiTensorProduct.Option

/-!
# Indexed tensor products of binary tensor products

For a finite index type `ι` and families of modules `M i` and `N i`, the indexed tensor product
of the binary tensor products is the binary tensor product of the indexed tensor products:

```text
⨂ᵢ (Mᵢ ⊗ Nᵢ) ≃ (⨂ᵢ Mᵢ) ⊗ (⨂ᵢ Nᵢ),     ⨂ₜ (mᵢ ⊗ₜ nᵢ) ↦ (⨂ₜ mᵢ) ⊗ₜ (⨂ₜ nᵢ).
```

The equivalence `PiTensorProduct.tensorDistribEquiv` is fixed by this formula on pure tensors.
Its inverse is Mathlib's `PiTensorProduct.map₂` applied to the factorwise tensor maps. It
commutes with factorwise linear maps and with reindexing the factors, so it is equivariant for
every action built from these two operations; in particular, it shows that tensor induction of
representations takes tensor products to tensor products.

Finiteness of `ι` is needed: over an infinite index type, a multilinear map out of
`∏ᵢ (Mᵢ ⊗ Nᵢ)` would have to expand infinitely many sums at once.

## Main definitions

* `PiTensorProduct.tensorDistribEquiv`: the equivalence `⨂ᵢ (Mᵢ ⊗ Nᵢ) ≃ (⨂ᵢ Mᵢ) ⊗ (⨂ᵢ Nᵢ)`.

## Main results

* `PiTensorProduct.tensorDistribEquiv_tprod`: the defining formula on pure tensors.
* `PiTensorProduct.tensorDistribEquiv_symm_toLinearMap`: the inverse is `map₂` of the
  factorwise tensor maps.
* `PiTensorProduct.ext_tprod_tmul`: linear maps out of `⨂ᵢ (Mᵢ ⊗ Nᵢ)` are determined on the
  tensors `⨂ₜ (mᵢ ⊗ₜ nᵢ)`.
* `PiTensorProduct.tensorDistribEquiv_map` and `PiTensorProduct.tensorDistribEquiv_reindex`:
  compatibility with factorwise linear maps and with reindexing.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v w x y

variable {R : Type u} [CommSemiring R]

private theorem exists_tensorDistribEquiv (ι : Type x) [Finite ι] :
    ∀ (M : ι → Type v) (N : ι → Type w) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
      [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)],
      ∃ e : (⨂[R] i, M i ⊗[R] N i) ≃ₗ[R] (⨂[R] i, M i) ⊗[R] (⨂[R] i, N i),
        ∀ (m : ∀ i, M i) (n : ∀ i, N i),
          e (tprod R fun i ↦ m i ⊗ₜ n i) = tprod R m ⊗ₜ tprod R n := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro M N _ _ _ _
    obtain ⟨f, hf⟩ := ih (fun i ↦ M (e i)) (fun i ↦ N (e i))
    refine ⟨(reindex R (fun i ↦ M i ⊗[R] N i) e.symm).trans (f.trans
      (TensorProduct.congr (reindex R M e.symm).symm (reindex R N e.symm).symm)),
      fun m n ↦ ?_⟩
    simp only [LinearEquiv.trans_apply, reindex_tprod, Equiv.symm_symm, hf,
      TensorProduct.congr_tmul, reindex_symm_symm_tprod]
  | h_empty =>
    intro M N _ _ _ _
    refine ⟨(isEmptyEquiv PEmpty).trans ((TensorProduct.lid R R).symm.trans
      (TensorProduct.congr (isEmptyEquiv PEmpty).symm (isEmptyEquiv PEmpty).symm)),
      fun m n ↦ ?_⟩
    simp only [LinearEquiv.trans_apply, isEmptyEquiv_apply_tprod,
      TensorProduct.lid_symm_apply, TensorProduct.congr_tmul]
    congr 1 <;> rw [LinearEquiv.symm_apply_eq, isEmptyEquiv_apply_tprod]
  | @h_option α _ ih =>
    intro M N _ _ _ _
    obtain ⟨f, hf⟩ := ih (fun i ↦ M (some i)) (fun i ↦ N (some i))
    refine ⟨(optionEquiv fun o ↦ M o ⊗[R] N o).trans
      ((TensorProduct.congr f (LinearEquiv.refl R _)).trans
        ((TensorProduct.tensorTensorTensorComm R _ _ _ _).trans
          (TensorProduct.congr (optionEquiv M).symm (optionEquiv N).symm))),
      fun m n ↦ ?_⟩
    simp only [LinearEquiv.trans_apply, optionEquiv_tprod, TensorProduct.congr_tmul, hf,
      LinearEquiv.refl_apply, TensorProduct.tensorTensorTensorComm_tmul,
      optionEquiv_symm_tmul]

variable {ι : Type x} [Finite ι]
  {M : ι → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : ι → Type w} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (R M N) in
/-- An indexed tensor product of binary tensor products is the binary tensor product of the
indexed tensor products: `⨂ᵢ (Mᵢ ⊗ Nᵢ) ≃ (⨂ᵢ Mᵢ) ⊗ (⨂ᵢ Nᵢ)`. The index type must be finite. -/
noncomputable def tensorDistribEquiv :
    (⨂[R] i, M i ⊗[R] N i) ≃ₗ[R] (⨂[R] i, M i) ⊗[R] (⨂[R] i, N i) :=
  (exists_tensorDistribEquiv (R := R) ι M N).choose

/-- The distributivity equivalence separates the two components of every tensor factor. -/
@[simp]
theorem tensorDistribEquiv_tprod (m : ∀ i, M i) (n : ∀ i, N i) :
    tensorDistribEquiv R M N (tprod R fun i ↦ m i ⊗ₜ n i) = tprod R m ⊗ₜ tprod R n :=
  (exists_tensorDistribEquiv (R := R) ι M N).choose_spec m n

/-- The inverse distributivity equivalence pairs up the factors of two pure tensors. -/
@[simp]
theorem tensorDistribEquiv_symm_tmul (m : ∀ i, M i) (n : ∀ i, N i) :
    (tensorDistribEquiv R M N).symm (tprod R m ⊗ₜ tprod R n) = tprod R fun i ↦ m i ⊗ₜ n i := by
  rw [LinearEquiv.symm_apply_eq, tensorDistribEquiv_tprod]

/-- The inverse distributivity equivalence is `map₂` of the factorwise tensor maps. -/
theorem tensorDistribEquiv_symm_toLinearMap :
    (tensorDistribEquiv R M N).symm.toLinearMap =
      TensorProduct.lift (map₂ fun i ↦ TensorProduct.mk R (M i) (N i)) := by
  apply TensorProduct.ext
  apply PiTensorProduct.ext
  ext m n
  simp [map₂_tprod_tprod]

/-- Linear maps out of `⨂ᵢ (Mᵢ ⊗ Nᵢ)` agree once they agree on the tensors `⨂ₜ (mᵢ ⊗ₜ nᵢ)`. -/
theorem ext_tprod_tmul {P : Type y} [AddCommMonoid P] [Module R P]
    {f g : (⨂[R] i, M i ⊗[R] N i) →ₗ[R] P}
    (h : ∀ (m : ∀ i, M i) (n : ∀ i, N i),
      f (tprod R fun i ↦ m i ⊗ₜ n i) = g (tprod R fun i ↦ m i ⊗ₜ n i)) :
    f = g := by
  have H : f ∘ₗ (tensorDistribEquiv R M N).symm.toLinearMap =
      g ∘ₗ (tensorDistribEquiv R M N).symm.toLinearMap := by
    apply TensorProduct.ext
    apply PiTensorProduct.ext
    ext m n
    simp [h]
  refine LinearMap.ext fun z ↦ ?_
  simpa using LinearMap.congr_fun H (tensorDistribEquiv R M N z)

/-- The distributivity equivalence commutes with applying linear maps in every factor. -/
theorem tensorDistribEquiv_map
    {M' : ι → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    {N' : ι → Type*} [∀ i, AddCommMonoid (N' i)] [∀ i, Module R (N' i)]
    (f : ∀ i, M i →ₗ[R] M' i) (g : ∀ i, N i →ₗ[R] N' i) (z : ⨂[R] i, M i ⊗[R] N i) :
    tensorDistribEquiv R M' N' (map (fun i ↦ TensorProduct.map (f i) (g i)) z) =
      TensorProduct.map (map f) (map g) (tensorDistribEquiv R M N z) := by
  have H : (tensorDistribEquiv R M' N').toLinearMap ∘ₗ
        map (fun i ↦ TensorProduct.map (f i) (g i)) =
      TensorProduct.map (map f) (map g) ∘ₗ (tensorDistribEquiv R M N).toLinearMap := by
    apply ext_tprod_tmul
    intro m n
    simp
  exact LinearMap.congr_fun H z

/-- The distributivity equivalence commutes with reindexing the tensor factors. -/
theorem tensorDistribEquiv_reindex {ι₂ : Type*} [Finite ι₂] (e : ι ≃ ι₂)
    (z : ⨂[R] i, M i ⊗[R] N i) :
    tensorDistribEquiv R (fun j ↦ M (e.symm j)) (fun j ↦ N (e.symm j))
        (reindex R (fun i ↦ M i ⊗[R] N i) e z) =
      TensorProduct.map (reindex R M e).toLinearMap (reindex R N e).toLinearMap
        (tensorDistribEquiv R M N z) := by
  have H : (tensorDistribEquiv R (fun j ↦ M (e.symm j)) (fun j ↦ N (e.symm j))).toLinearMap ∘ₗ
        (reindex R (fun i ↦ M i ⊗[R] N i) e).toLinearMap =
      TensorProduct.map (reindex R M e).toLinearMap (reindex R N e).toLinearMap ∘ₗ
        (tensorDistribEquiv R M N).toLinearMap := by
    apply ext_tprod_tmul
    intro m n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, reindex_tprod,
      tensorDistribEquiv_tprod, TensorProduct.map_tmul]
  exact LinearMap.congr_fun H z

end PiTensorProduct
