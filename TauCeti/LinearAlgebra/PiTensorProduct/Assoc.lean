/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Regrouping finite tensor powers

An iterated tensor power with finite outer index can be flattened to the tensor power indexed by
the product of the two index types. The characteristic equation on tensors of pure tensors fixes
this equivalence and makes it compatible with factorwise linear maps.

This regrouping is used for transitivity of tensor induction. It is the constant-fibre case of
the dependent-sum regrouping `PiTensorProduct.sigmaEquiv`, transported along
`Equiv.sigmaEquivProd`. Finiteness of the outer index permits expansion of tensors of sums in the
inner tensor powers; the inner index need not be finite.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v w x

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {ι : Type w} {κ : Type x}

/-- Flatten an iterated tensor power along a finite outer index to the tensor power indexed by
the product. The inner index can be arbitrary. -/
noncomputable def prodEquiv [Finite ι] :
    (⨂[R] _ : ι, ⨂[R] _ : κ, M) ≃ₗ[R] (⨂[R] _ : ι × κ, M) :=
  (sigmaEquiv (κ := fun _ : ι ↦ κ) (M := fun _ _ ↦ M)).trans
    (reindex R (fun _ ↦ M) (Equiv.sigmaEquivProd ι κ))

/-- Flattening a tensor of pure tensors concatenates the two index coordinates. -/
@[simp] theorem prodEquiv_tprod [Finite ι] (m : ι → κ → M) :
    prodEquiv (R := R) (tprod R fun i ↦ tprod R (m i)) =
      tprod R (fun p : ι × κ ↦ m p.1 p.2) := by
  simp [prodEquiv]

/-- The inverse regrouping forms the inner tensor in each outer coordinate. -/
@[simp] theorem prodEquiv_symm_tprod [Finite ι] (m : ι × κ → M) :
    (prodEquiv (R := R) (M := M) (ι := ι) (κ := κ)).symm (tprod R m) =
      tprod R (fun i ↦ tprod R (fun j ↦ m (i, j))) := by
  apply (prodEquiv (R := R)).injective
  simp

/-- Flattening commutes with applying a chosen linear map in each tensor factor. -/
theorem prodEquiv_map [Finite ι] {N : Type*} [AddCommMonoid N] [Module R N]
    (f : ι → κ → M →ₗ[R] N) (z : ⨂[R] _ : ι, ⨂[R] _ : κ, M) :
    prodEquiv (map (fun i : ι ↦ map (f i)) z) =
      map (fun p : ι × κ ↦ f p.1 p.2) (prodEquiv z) := by
  have H : (prodEquiv (R := R) (M := N) (ι := ι) (κ := κ)).toLinearMap ∘ₗ
        map (fun i : ι ↦ map (f i)) =
      map (fun p : ι × κ ↦ f p.1 p.2) ∘ₗ prodEquiv.toLinearMap := by
    apply ext_sigma_tprod
    intro m
    simp
  exact LinearMap.congr_fun H z

end PiTensorProduct

/-! A scalar-valued evaluator computes the four entries of a reshaped tensor. -/
example (R : Type*) [CommSemiring R] :
    PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R (Fin 2 × Fin 2) R)
      (PiTensorProduct.prodEquiv (R := R)
        (PiTensorProduct.tprod R fun i : Fin 2 ↦
          PiTensorProduct.tprod R (fun j : Fin 2 ↦ (![![2, 3], ![5, 7]] i j : R)))) = 210 := by
  norm_num [MultilinearMap.mkPiAlgebra_apply, Fintype.prod_prod_type, Fin.prod_univ_two]
