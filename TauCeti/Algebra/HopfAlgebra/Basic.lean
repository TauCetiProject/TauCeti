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

section

variable {R A B : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [CoalgebraStruct R A]
variable [Semiring B] [Algebra R B] [CoalgebraStruct R B]

/-- Applying an algebra homomorphism to a convolution product, oriented so it rewrites the
`WithConv.ofConv` shape arising from bialgebra morphism composition. -/
private lemma algHom_comp_convMul_ofConv (φ : A →ₐc[R] B) (f g : A →ₗ[R] A) :
    (toConv (φ.toLinearMap.comp f) *
          toConv (φ.toLinearMap.comp g)).ofConv =
      φ.toLinearMap.comp (toConv f * toConv g).ofConv :=
  (LinearMap.algHom_comp_convMul_distrib (φ : A →ₐ[R] B) (toConv f) (toConv g)).symm

end

section CoalgHom

variable {R A B : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [CoalgebraStruct R A]
variable [Semiring B] [Algebra R B] [Coalgebra R B]

/-- Precomposing a convolution product with a coalgebra homomorphism, oriented so it rewrites
the `WithConv.ofConv` shape arising from bialgebra morphism composition. -/
private lemma convMul_comp_coalgHom_ofConv (f g : B →ₗ[R] B) (φ : A →ₐc[R] B) :
    (toConv (f.comp φ.toLinearMap) *
          toConv (g.comp φ.toLinearMap)).ofConv =
      (toConv f * toConv g).ofConv.comp φ.toLinearMap :=
  (LinearMap.convMul_comp_coalgHom_distrib (toConv f) (toConv g) (φ : A →ₗc[R] B)).symm

end CoalgHom

section SourceAntipode

variable {R A B : Type*} [CommSemiring R]
variable [Semiring A] [HopfAlgebraStruct R A]
variable [Semiring B] [Algebra R B] [CoalgebraStruct R B]

/-- Applying a bialgebra homomorphism to the convolution product `S * id`, in the exact
normal form used in the antipode-preservation proof. -/
private lemma algHom_comp_antipode_id_ofConv (φ : A →ₐc[R] B) :
    (toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A))) *
          toConv φ.toLinearMap).ofConv =
      φ.toLinearMap.comp
        (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv := by
  simpa only [LinearMap.comp_id] using
    algHom_comp_convMul_ofConv φ (HopfAlgebra.antipode R (A := A)) LinearMap.id

end SourceAntipode

section TargetAntipode

variable {R A B : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [CoalgebraStruct R A]
variable [Semiring B] [HopfAlgebraStruct R B]

/-- Precomposing the convolution product `id * S` with a bialgebra homomorphism, in the
exact normal form used in the antipode-preservation proof. -/
private lemma id_antipode_comp_coalgHom_ofConv (φ : A →ₐc[R] B) :
    (toConv φ.toLinearMap *
          toConv ((HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap)).ofConv =
      (toConv LinearMap.id * toConv (HopfAlgebra.antipode R (A := B))).ofConv.comp
        φ.toLinearMap := by
  simpa only [LinearMap.id_comp] using
    convMul_comp_coalgHom_ofConv (LinearMap.id : B →ₗ[R] B)
      (HopfAlgebra.antipode R (A := B)) φ

end TargetAntipode

section Main

variable {R A B : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [HopfAlgebra R A] [HopfAlgebra R B]

/-- A bialgebra morphism between Hopf algebras commutes with the antipodes, as a statement
about underlying linear maps. -/
private lemma toLinearMap_comp_antipode (φ : A →ₐc[R] B) :
    φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A)) =
      (HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap := by
  let f : WithConv (A →ₗ[R] B) := toConv φ.toLinearMap
  let g : WithConv (A →ₗ[R] B) :=
    toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A)))
  let h : WithConv (A →ₗ[R] B) :=
    toConv ((HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap)
  have hg_left : g * f = 1 := by
    refine WithConv.ofConv_injective ?_
    dsimp only [g, f]
    rw [algHom_comp_antipode_id_ofConv φ]
    rw [LinearMap.antipode_mul_id]
    ext a
    exact (φ : A →ₐ[R] B).commutes (counit a)
  have hh_right : f * h = 1 := by
    refine WithConv.ofConv_injective ?_
    dsimp only [f, h]
    rw [id_antipode_comp_coalgHom_ofConv φ]
    rw [LinearMap.id_mul_antipode]
    ext a
    exact congr_arg (algebraMap R B) (CoalgHomClass.counit_comp_apply φ a)
  exact WithConv.toConv_injective (left_inv_eq_right_inv hg_left hh_right)

end Main

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
