/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Hopf algebra morphisms

Mathlib defines morphisms in `HopfAlgCat R` to be bialgebra morphisms; the missing
algebraic fact is that such a morphism automatically preserves the antipode.
We prove that here by the uniqueness of inverses in the convolution monoid.

## Main results

* `BialgHomClass.coe_comp_antipode`: a bialgebra morphism between Hopf algebras commutes
  with the antipodes as underlying linear maps.
* `BialgHomClass.map_antipode`: a bialgebra morphism between Hopf algebras commutes with
  the antipodes, pointwise.

## References

The proof uses Mathlib's convolution product on linear maps, due to Yaël Dillies,
Michał Mrugała and Yunzhou Xie.
-/

public section

open WithConv

namespace BialgHomClass

variable {R A B F : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [HopfAlgebra R A] [HopfAlgebra R B]
variable [FunLike F A B] [BialgHomClass F R A B]

/-- A bialgebra-hom-like map between Hopf algebras commutes with the antipodes, as a statement
about underlying linear maps. -/
@[simp]
theorem coe_comp_antipode (φ : F) :
    (φ : A →ₗ[R] B).comp (HopfAlgebra.antipode R (A := A)) =
      (HopfAlgebra.antipode R (A := B)).comp (φ : A →ₗ[R] B) := by
  have hφ : (CoalgHom.ofClass φ).toLinearMap = (φ : A →ₗ[R] B) := by
    ext a
    simp
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv (φ : A →ₗ[R] B))
  · apply WithConv.ofConv_injective
    calc
      _ = (AlgHom.ofClass φ).toLinearMap.comp
          (toConv (HopfAlgebra.antipode R (A := A)) *
            toConv (LinearMap.id : A →ₗ[R] A)).ofConv := by
        simpa only [ofConv_toConv, AlgHom.toLinearMap_eq_coe,
          AlgHomClass.linearMapOfClass_ofClass, LinearMap.comp_id] using
          (LinearMap.algHom_comp_convMul_distrib (AlgHom.ofClass φ)
            (toConv (HopfAlgebra.antipode R)) (toConv LinearMap.id)).symm
      _ = _ := by
        rw [LinearMap.antipode_mul_id]
        ext a
        simp [AlgHomClass.commutes]
  · apply WithConv.ofConv_injective
    calc
      _ = (toConv (LinearMap.id : B →ₗ[R] B) *
          toConv (HopfAlgebra.antipode R (A := B))).ofConv.comp
          (CoalgHom.ofClass φ).toLinearMap := by
        simpa only [ofConv_toConv, hφ, LinearMap.id_comp] using
          (LinearMap.convMul_comp_coalgHom_distrib (toConv LinearMap.id)
            (toConv (HopfAlgebra.antipode R)) (CoalgHom.ofClass φ)).symm
      _ = _ := by
        rw [LinearMap.id_mul_antipode]
        ext a
        simp

/-- A bialgebra-hom-like map between Hopf algebras commutes with the antipodes, pointwise. -/
@[simp]
theorem map_antipode (φ : F) (a : A) :
    φ (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (φ a) :=
  LinearMap.congr_fun (coe_comp_antipode φ) a

end BialgHomClass
