/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import TauCeti.Algebra.DirectSum.Component

/-!
# Tensor products of internal decompositions

If `M` and `N` are internal direct sums of families of submodules `A i` and `B j`, then
`M ⊗ N` is the internal direct sum of the images `A i ⊗ B j`. Mathlib supplies the external
tensor-product/direct-sum equivalence and the decomposition obtained from one decomposed factor;
this file records the symmetric two-factor consequence for internal decompositions together with
its bidegree projection API expressed via `TauCeti.homogeneousComponent`.

## Main results

* `DirectSum.IsInternal.tensorProduct`: the images of the tensor products of the summands form an
  internal decomposition of the ambient tensor product.
* `TauCeti.tensorProductDecomposition`: the chosen `DirectSum.Decomposition` of `M ⊗ N` into the
  bidegree submodules `Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)`.
* `TauCeti.homogeneousComponent_tensorProduct` and `TauCeti.coe_decompose_tensorProduct`: the
  `(i, j)`-component projection equals
  `TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j)`.
* `TauCeti.tensorProduct_ext_homogeneousComponent`: tensors are determined by their bidegree
  homogeneous-component projections.
* `TauCeti.map_homogeneousComponent_of_mem` and
  `TauCeti.map_homogeneousComponent_eq_zero_of_mem_ne`: a bidegree projection fixes its own
  pure-bidegree summand and vanishes on every other pure-bidegree summand.
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

namespace TauCeti

variable {K M N ι κ : Type*} [CommSemiring K]
  [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
  [DecidableEq ι] [DecidableEq κ]
  (A : ι → Submodule K M) (B : κ → Submodule K N)
  [DirectSum.Decomposition A] [DirectSum.Decomposition B]

/-- The internal direct-sum decomposition of `M ⊗[K] N` into the bidegree submodules
`Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)`, chosen from the internal
decompositions of `M` and `N`. -/
@[instance_reducible]
noncomputable def tensorProductDecomposition :
    DirectSum.Decomposition fun p : ι × κ ↦
      Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2) :=
  (DirectSum.IsInternal.tensorProduct A B
    (DirectSum.Decomposition.isInternal A)
    (DirectSum.Decomposition.isInternal B)).chooseDecomposition

/-- For any internal bidegree decomposition of `M ⊗[K] N`, projection onto the `(i, j)`-summand
equals the tensor product of the factor projections `homogeneousComponent A i` and
`homogeneousComponent B j`. -/
theorem homogeneousComponent_tensorProduct
    [DirectSum.Decomposition fun p : ι × κ ↦
      Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)]
    (i : ι) (j : κ) :
    homogeneousComponent (fun p : ι × κ ↦
      Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)) (i, j) =
      TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j) := by
  let C : ι × κ → Submodule K (M ⊗[K] N) :=
    fun p ↦ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)
  refine TensorProduct.ext' fun a b ↦ ?_
  induction a using DirectSum.Decomposition.inductionOn A with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | @homogeneous i' a =>
    induction b using DirectSum.Decomposition.inductionOn B with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | @homogeneous j' b =>
      have hab : (a : M) ⊗ₜ[K] (b : N) ∈ C (i', j') :=
        Submodule.apply_mem_map₂ _ a.property b.property
      by_cases hp : (i', j') = (i, j)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        rw [homogeneousComponent_apply_of_mem C hab, TensorProduct.map_tmul,
          homogeneousComponent_apply_of_mem A a.property,
          homogeneousComponent_apply_of_mem B b.property]
      · rw [homogeneousComponent_apply_of_mem_ne C hab hp, TensorProduct.map_tmul]
        by_cases hi : i' = i
        · rw [homogeneousComponent_apply_of_mem_ne B b.property (fun hj ↦ hp (Prod.ext hi hj)),
            TensorProduct.tmul_zero]
        · rw [homogeneousComponent_apply_of_mem_ne A a.property hi, TensorProduct.zero_tmul]

/-- For any internal bidegree decomposition of `M ⊗[K] N`, the `(i, j)`-component of `t`
coincides with `TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j) t`. -/
theorem coe_decompose_tensorProduct
    [DirectSum.Decomposition fun p : ι × κ ↦
      Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)]
    (t : M ⊗[K] N) (i : ι) (j : κ) :
    (DirectSum.decompose (fun p : ι × κ ↦
      Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)) t (i, j) : M ⊗[K] N) =
      TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j) t := by
  rw [← homogeneousComponent_apply, homogeneousComponent_tensorProduct]

/-- Elements of the tensor product of two internally decomposed modules are determined by their
bidegree homogeneous-component projections. -/
theorem tensorProduct_ext_homogeneousComponent {t s : M ⊗[K] N}
    (h : ∀ i j,
      TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j) t =
        TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j) s) :
    t = s := by
  let _ := tensorProductDecomposition A B
  refine (DirectSum.decomposeLinearEquiv
    (fun p : ι × κ ↦ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2))).injective
    (DirectSum.ext fun ⟨i, j⟩ ↦ Subtype.ext ?_)
  exact (coe_decompose_tensorProduct A B t i j).trans
    ((h i j).trans (coe_decompose_tensorProduct A B s i j).symm)

/-- A bidegree projection fixes every element of its own pure-bidegree tensor summand. -/
theorem map_homogeneousComponent_of_mem {i : ι} {j : κ} {t : M ⊗[K] N}
    (ht : t ∈ Submodule.map₂ (TensorProduct.mk K M N) (A i) (B j)) :
    TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j) t = t := by
  let _ := tensorProductDecomposition A B
  rw [← coe_decompose_tensorProduct A B t i j]
  exact DirectSum.decompose_of_mem_same
    (fun p : ι × κ ↦ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)) ht

/-- A bidegree projection vanishes on any pure-bidegree tensor summand of a different
bidegree. -/
theorem map_homogeneousComponent_eq_zero_of_mem_ne {p : ι × κ} {t : M ⊗[K] N}
    (ht : t ∈ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2))
    {i : ι} {j : κ} (hp : p ≠ (i, j)) :
    TensorProduct.map (homogeneousComponent A i) (homogeneousComponent B j) t = 0 := by
  let _ := tensorProductDecomposition A B
  rw [← coe_decompose_tensorProduct A B t i j]
  exact DirectSum.decompose_of_mem_ne
    (fun q : ι × κ ↦ Submodule.map₂ (TensorProduct.mk K M N) (A q.1) (B q.2)) ht hp

end TauCeti
