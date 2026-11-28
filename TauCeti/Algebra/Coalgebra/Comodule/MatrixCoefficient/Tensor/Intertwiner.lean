/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Tensor.Product
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Detecting tensor intertwiners by matrix coefficients

An equivalence from a tensor product of right comodules to another comodule is colinear
exactly when the target coefficient of each pure dual precomposed with `e.symm`, evaluated
at `e (m ⊗ₜ n)`, is the product of the corresponding coefficients of the two factors.
The tensor product carries the native diagonal coaction. This criterion lets a multiplication
formula on coefficients supply a comodule isomorphism, as in tensor reconstruction.
The criterion holds for arbitrary projective modules over a commutative semiring, hence for all
vector spaces over a field, with no finite-dimensionality or characteristic restriction.

## References

Deligne–Milne, *Tannakian categories*, Proposition 2.16 (multiplication of matrix coefficients).
-/

public section

open Module TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace LinearEquiv

section Criterion

variable {R B M N P : Type*} [CommSemiring R] [Semiring B] [Bialgebra R B]
  [AddCommMonoid M] [Module R M] [Comodule R B M]
  [AddCommMonoid N] [Module R N] [Comodule R B N]
  [AddCommMonoid P] [Module R P] [Comodule R B P]

attribute [local instance] Comodule.tensor

private theorem map_coact_tensor_of_matrixCoefficient
    [Module.Projective R M] [Module.Projective R N]
    (e : M ⊗[R] N ≃ₗ[R] P)
    (h : ∀ m n α β,
      matrixCoefficient (C := B)
          ((TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)).comp e.symm.toLinearMap)
          (e (m ⊗ₜ[R] n)) =
        matrixCoefficient (C := B) α m * matrixCoefficient (C := B) β n) :
    TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ coact (R := R) (C := B) =
      coact (R := R) (C := B) ∘ₗ e.toLinearMap := by
  have hcontract (α : Module.Dual R M) (β : Module.Dual R N) :
      LinearMap.tensorComponent (M := B) α ∘ₗ LinearMap.tensorComponent β ∘ₗ
          (TensorProduct.assoc R B M N).symm.toLinearMap ∘ₗ
          (TensorProduct.comm R (M ⊗[R] N) B).toLinearMap =
        (TensorProduct.lid R B).toLinearMap ∘ₗ
          TensorProduct.map (TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)) LinearMap.id := by
    rw [← LinearMap.comp_assoc, LinearMap.tensorComponent_comp_tensorComponent]
    ext m n b
    simp [mul_comm]
  refine TensorProduct.ext' fun m n ↦ ?_
  apply (TensorProduct.congr e.symm (LinearEquiv.refl R B)).injective
  simp only [← LinearEquiv.coe_coe, TensorProduct.toLinearMap_congr,
    LinearEquiv.refl_toLinearMap, LinearMap.comp_apply, TensorProduct.map_map,
    e.symm_comp, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  apply (TensorProduct.comm R (M ⊗[R] N) B).injective
  apply (TensorProduct.assoc R B M N).symm.injective
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro β
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro α
  have hc := fun x => DFunLike.congr_fun (hcontract α β) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  rw [hc, hc]
  simpa only [matrixCoefficient_def, TensorProduct.map_map, LinearMap.comp_id,
    LinearEquiv.coe_coe] using
    (matrixCoefficient_tensor (C := B) α β m n).trans (h m n α β).symm

/-- An equivalence out of the native diagonal tensor comodule is colinear if and only if
the target coefficient of each pure dual precomposed with `e.symm`, evaluated at
`e (m ⊗ₜ n)`, is the product of the corresponding factor coefficients. Only projectivity
of the two tensor factors is required, so vector spaces may have arbitrary dimension. -/
theorem map_coact_tensor_iff_matrixCoefficient [Module.Projective R M] [Module.Projective R N]
    (e : M ⊗[R] N ≃ₗ[R] P) :
    TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ coact (R := R) (C := B) =
        coact (R := R) (C := B) ∘ₗ e.toLinearMap ↔
      ∀ m n α β,
        matrixCoefficient (C := B)
            ((TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)).comp e.symm.toLinearMap)
            (e (m ⊗ₜ[R] n)) =
          matrixCoefficient (C := B) α m * matrixCoefficient (C := B) β n := by
  constructor
  · intro h m n α β
    calc
      _ = matrixCoefficient (C := B)
          (((TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)).comp e.symm.toLinearMap).comp
            e.toLinearMap) (m ⊗ₜ[R] n) :=
        matrixCoefficient_map (⟨e.toLinearMap, h⟩ : Comodule.Hom R B (M ⊗[R] N) P) _ _
      _ = _ := by
        simpa only [LinearMap.comp_assoc, e.symm_comp, LinearMap.comp_id] using
          matrixCoefficient_tensor (C := B) α β m n
  · exact map_coact_tensor_of_matrixCoefficient e

end Criterion

end LinearEquiv
