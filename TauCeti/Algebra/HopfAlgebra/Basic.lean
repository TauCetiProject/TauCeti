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

open Coalgebra WithConv

namespace BialgHom

variable {R A B : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [HopfAlgebra R A] [HopfAlgebra R B]

private lemma toLinearMap_comp_antipode (φ : A →ₐc[R] B) :
    φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A)) =
      (HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap := by
  let f : WithConv (A →ₗ[R] B) := toConv φ.toLinearMap
  let g : WithConv (A →ₗ[R] B) :=
    toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A)))
  let h : WithConv (A →ₗ[R] B) :=
    toConv ((HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap)
  have hφ_alg : φ.toLinearMap = (φ : A →ₐ[R] B).toLinearMap :=
    (CoalgHom.toLinearMap_eq_ofClass (φ : A →ₗc[R] B)).trans
      (BialgHom.toAlgHom_toLinearMap φ).symm
  have hφ_coalg : φ.toLinearMap = (φ : A →ₗc[R] B).toLinearMap := rfl
  have hg_left : g * f = 1 := by
    refine WithConv.ofConv_injective ?_
    dsimp only [g, f]
    rw [hφ_alg]
    have hdistrib :=
      (LinearMap.algHom_comp_convMul_distrib (φ : A →ₐ[R] B)
        (toConv (HopfAlgebra.antipode R (A := A)))
        (toConv (LinearMap.id : A →ₗ[R] A))).symm
    simpa only [LinearMap.comp_id] using hdistrib.trans (by
      rw [LinearMap.antipode_mul_id]
      ext a
      exact (φ : A →ₐ[R] B).commutes (counit a))
  have hh_right : f * h = 1 := by
    refine WithConv.ofConv_injective ?_
    dsimp only [f, h]
    rw [hφ_coalg]
    have hdistrib :=
      (LinearMap.convMul_comp_coalgHom_distrib
        (toConv (LinearMap.id : B →ₗ[R] B))
        (toConv (HopfAlgebra.antipode R (A := B)))
        (φ : A →ₗc[R] B)).symm
    simpa only [LinearMap.id_comp] using hdistrib.trans (by
      rw [LinearMap.id_mul_antipode]
      ext a
      exact congr_arg (algebraMap R B) (CoalgHomClass.counit_comp_apply φ a))
  exact WithConv.toConv_injective (left_inv_eq_right_inv hg_left hh_right)

end BialgHom

namespace BialgHomClass

variable {R A B F : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [HopfAlgebra R A] [HopfAlgebra R B]
variable [FunLike F A B] [BialgHomClass F R A B]

/-- A bialgebra-hom-like map between Hopf algebras commutes with the antipodes, as a statement
about underlying linear maps. -/
@[simp]
theorem coe_comp_antipode (φ : F) :
    (φ : A →ₗ[R] B).comp (HopfAlgebra.antipode R (A := A)) =
      (HopfAlgebra.antipode R (A := B)).comp (φ : A →ₗ[R] B) :=
  BialgHom.toLinearMap_comp_antipode (φ : A →ₐc[R] B)

/-- A bialgebra-hom-like map between Hopf algebras commutes with the antipodes, pointwise. -/
@[simp]
theorem map_antipode (φ : F) (a : A) :
    φ (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (φ a) :=
  LinearMap.congr_fun (coe_comp_antipode φ) a

end BialgHomClass
