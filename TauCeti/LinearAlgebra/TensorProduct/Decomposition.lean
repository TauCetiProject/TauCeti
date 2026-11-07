/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition

/-!
# Tensor products of internal decompositions

If `M` and `N` are internal direct sums of families of submodules `A i` and `B j`, then
`M ⊗ N` is the internal direct sum of the images `A i ⊗ B j`. Mathlib supplies the external
tensor-product/direct-sum equivalence and the decomposition obtained from one decomposed factor;
this file records the symmetric two-factor consequence for internal decompositions.

## Main result

* `DirectSum.IsInternal.tensorProduct`: the images of the tensor products of the summands form an
  internal decomposition of the ambient tensor product.
-/

public section

open TensorProduct

namespace DirectSum.IsInternal

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {M : Type v} {N : Type w} [AddCommMonoid M] [Module K M]
  [AddCommMonoid N] [Module K N]
variable {ι : Type x} {κ : Type y} [DecidableEq ι] [DecidableEq κ]
variable (A : ι → Submodule K M) (B : κ → Submodule K N)

/-- **Tensor products of internal decompositions are internal.** If `A` and `B` internally
decompose `M` and `N`, the images of `A i ⊗ B j` under the canonical map internally decompose
`M ⊗ N`.

The summand is written with `Submodule.map₂` because this is the canonical submodule of the
ambient tensor product spanned by pure tensors from the two factors. -/
theorem tensorProduct (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B) :
    DirectSum.IsInternal fun p : ι × κ ↦
      Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2) := by
  let _ := hA.chooseDecomposition
  let _ := hB.chooseDecomposition
  -- The summand inclusions are split by the decompositions, so their tensor product is injective.
  have hinj (i : ι) (j : κ) : Function.Injective (mapIncl (A i) (B j)) :=
    LinearMap.injective_of_comp_eq_id _
      (TensorProduct.map (component K ι (fun i ↦ A i) i ∘ₗ decomposeLinearEquiv A)
        (component K κ (fun j ↦ B j) j ∘ₗ decomposeLinearEquiv B)) (by ext; simp)
  let C := fun p : ι × κ ↦ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)
  let e (p : ι × κ) : A p.1 ⊗[K] B p.2 ≃ₗ[K] C p :=
    (LinearEquiv.ofInjective _ (hinj p.1 p.2)).trans
      (LinearEquiv.ofEq _ _ (range_mapIncl (A p.1) (B p.2)))
  let E : M ⊗[K] N ≃ₗ[K] ⨁ p, C p :=
    TensorProduct.congr (decomposeLinearEquiv A) (decomposeLinearEquiv B) ≪≫ₗ
      TensorProduct.directSum K K (fun i ↦ A i) (fun j ↦ B j) ≪≫ₗ congrLinearEquiv e
  -- Recomposition is inverse to `E`: check it on the image of each summand `A i ⊗ B j`.
  have hcoe : coeLinearMap C = E.symm.toLinearMap := by
    refine linearMap_ext K fun p ↦ LinearMap.ext fun z ↦ ?_
    obtain ⟨x, rfl⟩ := (e p).surjective z
    rw [LinearMap.comp_apply, coeLinearMap_lof, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.eq_symm_apply]
    obtain ⟨i, j⟩ := p
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [E, e, coe_congrLinearEquiv]
    | add x y hx hy => simp_all
  let _ : Decomposition C := .ofLinearMap C E.toLinearMap
    (by rw [hcoe, LinearEquiv.symm_comp]) (by rw [hcoe, LinearEquiv.comp_symm])
  exact Decomposition.isInternal C

end DirectSum.IsInternal
