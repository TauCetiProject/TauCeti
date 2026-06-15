/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

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
* `TauCeti.TensorProduct.antipode_tmul`: the antipode on a tensor product of Hopf algebras
  acts componentwise on pure tensors.
* `BialgHom.toLinearMap_comp_antipode` and `BialgHom.map_antipode`: a bialgebra morphism
  between Hopf algebras commutes with the antipodes.

## References

This supplies a formal prerequisite for the Tau Ceti reductive-groups roadmap, Layer 0,
"the functor of points and the three-way dictionary": morphisms in the Hopf-algebra model
must respect the inverse map in the affine group-scheme model. The proof uses Mathlib's
convolution product on linear maps, due to Yaël Dillies, Michał Mrugała and Yunzhou Xie.
The tensor-product antipode formula uses Mathlib's
`Mathlib.RingTheory.HopfAlgebra.TensorProduct`, specifically `TensorProduct.antipode_def`.
-/

open Coalgebra HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
  [Algebra R S] [_root_.HopfAlgebra R A] [_root_.HopfAlgebra S B] [Algebra R B]
  [IsScalarTower R S B]

/-- The antipode on a tensor product of Hopf algebras acts componentwise on pure tensors. -/
@[simp]
lemma antipode_tmul (b : B) (a : A) :
    antipode S (A := B ⊗[R] A) (b ⊗ₜ[R] a) =
      antipode S b ⊗ₜ[R] antipode R a := by
  simp [_root_.TensorProduct.antipode_def]

end TensorProduct

namespace HopfAlgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

/-- The antipode is antimultiplicative. This wraps Mathlib's moving API under a stable
Tau Ceti name. -/
theorem antipode_mul_antidistrib (a b : H) :
    antipode R (a * b) = antipode R b * antipode R a := by
  -- We show that the linear maps `S ∘ μ` and `μ ∘ (S ⊗ S) ∘ comm` are equal,
  -- by proving they are both convolution inverses of `μ`.
  suffices h : antipode R ∘ₗ LinearMap.mul' R H =
      LinearMap.mul' R H ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ
        TensorProduct.comm R H H by
    exact congr(($h) (a ⊗ₜ b))
  refine toConv_injective
    (left_inv_eq_right_inv
      (b := toConv (antipode R ∘ₗ LinearMap.mul' R H))
      (a := toConv (LinearMap.mul' R H))
      (c := toConv (LinearMap.mul' R H ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ
        TensorProduct.comm R H H))
      ?_ ?_)
  · refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
    simp only [LinearMap.convMul_apply, LinearMap.convOne_apply]
    rw [TensorProduct.comul_tmul]
    let ℛx := ℛ R x
    let ℛy := ℛ R y
    conv_lhs => rw [← ℛx.eq, ← ℛy.eq]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [Finset.sum_comm]
    simp only [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
    have key := mul_antipode_rTensor_comul_apply (R := R) (x * y)
    rw [Bialgebra.comul_mul, ← ℛx.eq, ← ℛy.eq] at key
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
      map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Bialgebra.counit_mul] at key
    rw [Finset.sum_comm] at key
    simpa [Algebra.algebraMap_eq_smul_one, mul_comm (counit x) (counit y)] using key
  · refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
    simp only [LinearMap.convMul_apply, LinearMap.convOne_apply]
    rw [TensorProduct.comul_tmul]
    let ℛx := ℛ R x
    let ℛy := ℛ R y
    conv_lhs => rw [← ℛx.eq, ← ℛy.eq]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [Finset.sum_comm]
    simp only [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
    calc ∑ i ∈ ℛx.index, ∑ j ∈ ℛy.index,
        (ℛx.left i * ℛy.left j) * (antipode R (ℛy.right j) * antipode R (ℛx.right i))
      _ = ∑ i ∈ ℛx.index, ∑ j ∈ ℛy.index,
          ℛx.left i * (ℛy.left j * antipode R (ℛy.right j) * antipode R (ℛx.right i)) := by
        simp [mul_assoc]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          ((∑ j ∈ ℛy.index, ℛy.left j * antipode R (ℛy.right j)) * antipode R (ℛx.right i)) := by
        simp [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          (counit y • 1 * antipode R (ℛx.right i)) := by
        rw [sum_mul_antipode_eq_smul ℛy]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          (algebraMap R H (counit y) * antipode R (ℛx.right i)) := by
        simp [Algebra.smul_def]
      _ = ∑ i ∈ ℛx.index, algebraMap R H (counit y) *
          (ℛx.left i * antipode R (ℛx.right i)) := by
        congr 1
        ext i
        rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
      _ = algebraMap R H (counit y) *
          ∑ i ∈ ℛx.index, ℛx.left i * antipode R (ℛx.right i) := by
        rw [← Finset.mul_sum]
      _ = algebraMap R H (counit y) * (counit (R := R) x • (1 : H)) := by
        rw [sum_mul_antipode_eq_smul ℛx]
      _ = (counit (R := R) x * counit y) • (1 : H) := by
        simp only [Algebra.smul_def, mul_one, ← map_mul, mul_comm (counit x)]
      _ = (counit (R := R) y • counit x) • (1 : H) := by
        simp only [smul_eq_mul, mul_comm (counit y)]

/-- The antipode on the base-changed Hopf algebra `K ⊗[k] A` sends a pure tensor
`s ⊗ a` to `s ⊗ S a`. -/
@[simp]
lemma baseChange_antipode_tmul {k K A : Type*} [CommSemiring k] [CommSemiring K]
    [Semiring A] [Algebra k K] [_root_.HopfAlgebra k A] (s : K) (a : A) :
    antipode K (A := K ⊗[k] A) (s ⊗ₜ[k] a) =
      s ⊗ₜ[k] antipode k a := by
  simp

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

/-- The algebra-hom projection of a bialgebra hom has the same underlying linear map as the
bialgebra hom itself. -/
private lemma toAlgHom_toLinearMap (φ : A →ₐc[R] B) :
    (φ : A →ₐ[R] B).toLinearMap = φ.toLinearMap :=
  _root_.BialgHom.toAlgHom_toLinearMap φ

/-- The coalgebra-hom projection of a bialgebra hom has the same underlying linear map as the
bialgebra hom itself. -/
private lemma toCoalgHom_toLinearMap (φ : A →ₐc[R] B) :
    (φ.toCoalgHom : A →ₗ[R] B) = φ.toLinearMap :=
  rfl

/-- The coalgebra-hom coercion of a bialgebra hom has the same underlying linear map as the
bialgebra hom itself. -/
private lemma coe_coalgHom_toLinearMap (φ : A →ₐc[R] B) :
    ((φ : A →ₗc[R] B) : A →ₗ[R] B) = φ.toLinearMap :=
  rfl

/-- Applying an algebra homomorphism to a convolution product, oriented so it rewrites the
`WithConv.ofConv` shape arising from bialgebra morphism composition. -/
private lemma algHom_comp_convMul_ofConv (φ : A →ₐc[R] B) (f g : A →ₗ[R] A) :
    (toConv (φ.toLinearMap.comp f) *
          toConv (φ.toLinearMap.comp g)).ofConv =
      φ.toLinearMap.comp (toConv f * toConv g).ofConv := by
  have hφ : φ.toLinearMap = (φ : A →ₐ[R] B).toLinearMap :=
    (toAlgHom_toLinearMap φ).symm
  rw [hφ]
  simpa using
    (LinearMap.algHom_comp_convMul_distrib (φ : A →ₐ[R] B) (toConv f) (toConv g)).symm

/-- Precomposing a convolution product with a coalgebra homomorphism, oriented so it rewrites
the `WithConv.ofConv` shape arising from bialgebra morphism composition. -/
private lemma convMul_comp_coalgHom_ofConv (f g : B →ₗ[R] B) (φ : A →ₐc[R] B) :
    (toConv (f.comp φ.toLinearMap) *
          toConv (g.comp φ.toLinearMap)).ofConv =
      (toConv f * toConv g).ofConv.comp φ.toLinearMap := by
  have hφ : φ.toLinearMap = ((φ : A →ₗc[R] B) : A →ₗ[R] B) :=
    (coe_coalgHom_toLinearMap φ).symm
  rw [hφ]
  simpa using
    (LinearMap.convMul_comp_coalgHom_distrib (toConv f) (toConv g)
      (φ : A →ₗc[R] B)).symm

/-- Applying a bialgebra homomorphism to the convolution product `S * id`, in the exact
normal form used in the antipode-preservation proof. -/
private lemma algHom_comp_antipode_id_ofConv (φ : A →ₐc[R] B) :
    (toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R (A := A))) *
          toConv φ.toLinearMap).ofConv =
      φ.toLinearMap.comp
        (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv := by
  have h := algHom_comp_convMul_ofConv φ (HopfAlgebra.antipode R (A := A)) LinearMap.id
  simpa only [LinearMap.comp_id] using h

/-- Precomposing the convolution product `id * S` with a bialgebra homomorphism, in the
exact normal form used in the antipode-preservation proof. -/
private lemma id_antipode_comp_coalgHom_ofConv (φ : A →ₐc[R] B) :
    (toConv φ.toLinearMap *
          toConv ((HopfAlgebra.antipode R (A := B)).comp φ.toLinearMap)).ofConv =
      (toConv LinearMap.id * toConv (HopfAlgebra.antipode R (A := B))).ofConv.comp
        φ.toLinearMap := by
  have h := convMul_comp_coalgHom_ofConv (LinearMap.id : B →ₗ[R] B)
    (HopfAlgebra.antipode R (A := B)) φ
  simpa only [LinearMap.id_comp] using h

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
    rw [toCoalgHom_toLinearMap φ]
    rw [algHom_comp_antipode_id_ofConv φ]
    rw [HopfAlgebra.antipode_convMul_id]
    ext a
    exact (φ : A →ₐ[R] B).commutes (Coalgebra.counit a)
  have hh_right : f * h = 1 := by
    refine WithConv.ofConv_injective ?_
    dsimp [f, h]
    rw [toCoalgHom_toLinearMap φ]
    rw [id_antipode_comp_coalgHom_ofConv φ]
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
