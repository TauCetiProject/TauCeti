/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebra morphisms

This file records Hopf-algebra API needed for the affine-group-scheme dictionary in the
reductive-groups roadmap. Mathlib defines morphisms in `HopfAlgCat R` to be bialgebra
morphisms; the missing algebraic fact is that such a morphism automatically preserves the
antipode. We prove that here by the usual convolution-inverse uniqueness argument.

## Main results

* `TauCeti.HopfAlgebra.antipode_convMul_id` and
  `TauCeti.HopfAlgebra.id_convMul_antipode`: the antipode is respectively a left and right
  convolution inverse of the identity linear map.
* `BialgHom.toLinearMap_comp_antipode` and `BialgHom.map_antipode`: a bialgebra morphism
  between Hopf algebras commutes with the antipodes.

## References

This supplies a formal prerequisite for the Tau Ceti reductive-groups roadmap, Layer 0,
"the functor of points and the three-way dictionary": morphisms in the Hopf-algebra model
must respect the inverse map in the affine group-scheme model. The proof uses Mathlib's
convolution product on linear maps, due to Yaël Dillies, Michał Mrugała and Yunzhou Xie.
-/

open Coalgebra HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace HopfAlgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

/-- The antipode is a left convolution inverse of the identity in the convolution ring of
linear maps: `S * id = 1`. This is a restatement of the antipode axiom
`HopfAlgebra.mul_antipode_rTensor_comul`. -/
@[simp]
lemma antipode_convMul_id :
    (toConv (antipode R) : WithConv (H →ₗ[R] H)) * toConv LinearMap.id = 1 := by
  refine WithConv.ext ?_
  ext h
  simp only [LinearMap.convMul_apply, LinearMap.convOne_apply,
    ← LinearMap.rTensor_def]
  exact mul_antipode_rTensor_comul_apply h

/-- The antipode is a right convolution inverse of the identity in the convolution ring of
linear maps: `id * S = 1`. This is a restatement of the antipode axiom
`HopfAlgebra.mul_antipode_lTensor_comul`. -/
@[simp]
lemma id_convMul_antipode :
    (toConv LinearMap.id : WithConv (H →ₗ[R] H)) * toConv (antipode R) = 1 := by
  refine WithConv.ext ?_
  ext h
  simp only [LinearMap.convMul_apply, LinearMap.convOne_apply,
    ← LinearMap.lTensor_def]
  exact mul_antipode_lTensor_comul_apply h

end HopfAlgebra

namespace BialgHom

variable {R A B : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [_root_.HopfAlgebra R A] [_root_.HopfAlgebra R B]

/-- A bialgebra morphism between Hopf algebras commutes with the antipodes, as a statement
about underlying linear maps. -/
@[simp]
theorem toLinearMap_comp_antipode (φ : A →ₐc[R] B) :
    φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A)) =
      (HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap := by
  let f : WithConv (A →ₗ[R] B) := toConv φ.toLinearMap
  let g : WithConv (A →ₗ[R] B) :=
    toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A)))
  let h : WithConv (A →ₗ[R] B) :=
    toConv ((HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap)
  have hg_left : g * f = 1 := by
    refine WithConv.ofConv_injective ?_
    dsimp [g, f]
    -- `algHom_comp_convMul_distrib` is stated after applying an algebra hom to a
    -- convolution product. The definitions of `BialgHom.toAlgHom`, `LinearMap.comp`, and
    -- `WithConv.ofConv` reduce this goal to that exact shape.
    change
      (toConv ((φ : A →ₐ[R] B).toLinearMap.comp (HopfAlgebra.antipode R (A := A))) *
          toConv ((φ : A →ₐ[R] B).toLinearMap.comp LinearMap.id)).ofConv =
        (1 : WithConv (A →ₗ[R] B)).ofConv
    rw [← LinearMap.algHom_comp_convMul_distrib (φ : A →ₐ[R] B)
      (toConv (HopfAlgebra.antipode R (A := A))) (toConv LinearMap.id)]
    rw [HopfAlgebra.antipode_convMul_id]
    ext a
    exact (φ : A →ₐ[R] B).commutes (Coalgebra.counit a)
  have hh_right : f * h = 1 := by
    refine WithConv.ofConv_injective ?_
    dsimp [f, h]
    -- Dually, `convMul_comp_coalgHom_distrib` is stated before wrapping the two composed
    -- linear maps with `toConv`; unfolding the coalgebra-hom coercion gives that form.
    change
      (toConv ((toConv (LinearMap.id : B →ₗ[R] B)).ofConv.comp
            (φ : A →ₗc[R] B).toLinearMap) *
          toConv ((toConv (HopfAlgebra.antipode R (A := B))).ofConv.comp
            (φ : A →ₗc[R] B).toLinearMap)).ofConv =
        (1 : WithConv (A →ₗ[R] B)).ofConv
    rw [← LinearMap.convMul_comp_coalgHom_distrib
      (toConv (LinearMap.id : B →ₗ[R] B)) (toConv (HopfAlgebra.antipode R (A := B)))
      (φ : A →ₗc[R] B)]
    rw [HopfAlgebra.id_convMul_antipode]
    ext a
    exact congr_arg (algebraMap R B) (CoalgHomClass.counit_comp_apply φ a)
  have h_eq : g = h := by
    calc
      g = g * 1 := by rw [mul_one]
      _ = g * (f * h) := by rw [hh_right]
      _ = (g * f) * h := by rw [mul_assoc]
      _ = 1 * h := by rw [hg_left]
      _ = h := by rw [one_mul]
  exact WithConv.toConv_injective h_eq

/-- A bialgebra morphism between Hopf algebras commutes with the antipodes, pointwise. -/
@[simp]
theorem map_antipode (φ : A →ₐc[R] B) (a : A) :
    φ (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (φ a) :=
  LinearMap.congr_fun (toLinearMap_comp_antipode φ) a

end BialgHom

namespace BialgHomClass

variable {R A B F : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [_root_.HopfAlgebra R A] [_root_.HopfAlgebra R B]
variable [FunLike F A B] [BialgHomClass F R A B]

/-- A bialgebra-hom-like map between Hopf algebras commutes with the antipodes, pointwise. -/
@[simp]
theorem map_antipode (φ : F) (a : A) :
    φ (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (φ a) :=
  BialgHom.map_antipode (φ : A →ₐc[R] B) a

end BialgHomClass

end TauCeti
