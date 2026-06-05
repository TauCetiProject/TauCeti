/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of Hopf algebras

This file supplies the small API around the scalar extension `K ⊗[k] A` of a Hopf algebra
`A` over `k`. Mathlib already provides the Hopf algebra instance on tensor products of Hopf
algebras in `Mathlib.RingTheory.HopfAlgebra.TensorProduct`; the declarations here name the
base-change object and record the canonical inclusion, the induced Hopf operations, and
functoriality in bialgebra maps.

This is a prerequisite for the reductive-groups roadmap, Layer 0, "Base change":
geometric properties of affine group schemes are defined after extending scalars, and on
coordinate rings this is the Hopf algebra `K ⊗[k] A`.
-/

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

namespace BialgHom

variable {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B]
variable [HopfAlgebra k A] [HopfAlgebra k B]

/-- A bialgebra homomorphism between Hopf algebras commutes with the antipode, as an equality of
linear maps. -/
lemma antipode_comp (f : A →ₐc[k] B) :
    (HopfAlgebra.antipode k : B →ₗ[k] B).comp (f : A →ₗ[k] B) =
      (f : A →ₗ[k] B).comp (HopfAlgebra.antipode k : A →ₗ[k] A) := by
  -- The Hopf-algebra inverse uniqueness theorem is stated for linear maps. Naming the
  -- underlying linear map makes the two coercions definitionally identical for that theorem.
  let u : A →ₗ[k] B := f
  change (HopfAlgebra.antipode k : B →ₗ[k] B).comp u =
    u.comp (HopfAlgebra.antipode k : A →ₗ[k] A)
  apply WithConv.toConv_injective
  exact left_inv_eq_right_inv (a := WithConv.toConv u)
    (b := WithConv.toConv ((HopfAlgebra.antipode k : B →ₗ[k] B).comp u))
    (c := WithConv.toConv (u.comp (HopfAlgebra.antipode k : A →ₗ[k] A)))
    (by
      ext x
      rw [(ℛ k x).convMul_apply, LinearMap.convOne_apply]
      simpa [u, Coalgebra.Repr.induced, Algebra.smul_def,
        CoalgHomClass.counit_comp_apply f x]
        using HopfAlgebra.sum_antipode_mul_eq_smul ((ℛ k x).induced f))
    (by
      ext x
      rw [(ℛ k x).convMul_apply, LinearMap.convOne_apply]
      simpa [u, Algebra.smul_def, map_sum, map_mul, AlgHomClass.commutes f]
        using congr_arg f (HopfAlgebra.sum_mul_antipode_eq_smul (ℛ k x)))

/-- A bialgebra homomorphism between Hopf algebras preserves the antipode. -/
@[simp]
lemma map_antipode (f : A →ₐc[k] B) (a : A) :
    f (HopfAlgebraStruct.antipode k a) = HopfAlgebraStruct.antipode k (f a) := by
  exact LinearMap.congr_fun (antipode_comp f).symm a

end BialgHom

namespace TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [HopfAlgebra R A] [HopfAlgebra S B] [Algebra R B] [IsScalarTower R S B]

/-- The antipode on a tensor product of Hopf algebras applies the antipode in each factor on
pure tensors. -/
@[simp]
lemma antipode_tmul (b : B) (a : A) :
    HopfAlgebraStruct.antipode S (b ⊗ₜ[R] a : B ⊗[R] A) =
      HopfAlgebraStruct.antipode S b ⊗ₜ[R] HopfAlgebraStruct.antipode R a := by
  simp [_root_.TensorProduct.antipode_def]

end TensorProduct

namespace Bialgebra.TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Bialgebra S A] [Bialgebra R B] [Algebra R A] [Algebra R S] [IsScalarTower R S A]

/-- The tensor product of identity bialgebra homomorphisms is the identity. -/
@[simp]
lemma map_id :
    Bialgebra.TensorProduct.map (BialgHom.id S A) (BialgHom.id R B) =
      BialgHom.id S (A ⊗[R] B) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

variable {C D E F : Type*} [Semiring C] [Semiring D] [Semiring E] [Semiring F]
variable [Bialgebra S C] [Bialgebra R D] [Bialgebra S E] [Bialgebra R F]
variable [Algebra R C] [Algebra R E] [IsScalarTower R S C] [IsScalarTower R S E]

/-- Tensor product of bialgebra homomorphisms preserves composition. -/
lemma map_comp (f₂ : C →ₐc[S] E) (f₁ : A →ₐc[S] C)
    (g₂ : D →ₐc[R] F) (g₁ : B →ₐc[R] D) :
    Bialgebra.TensorProduct.map (f₂.comp f₁) (g₂.comp g₁) =
      (Bialgebra.TensorProduct.map f₂ g₂).comp (Bialgebra.TensorProduct.map f₁ g₁) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

end Bialgebra.TensorProduct

namespace HopfAlgebra

variable (k K A : Type*) [CommSemiring k] [CommSemiring K] [Semiring A]
variable [Algebra k K] [Algebra k A]

/-- The scalar extension `K ⊗[k] A` of a Hopf algebra `A` over `k` to a commutative
`k`-algebra `K`.

The underlying type only needs the algebra structures; when `A` is a Hopf algebra, Mathlib's
tensor-product instance equips this type with the induced Hopf algebra structure over `K`. -/
abbrev baseChange : Type _ :=
  K ⊗[k] A

namespace BaseChange

variable {k K A : Type*} [CommSemiring k] [CommSemiring K] [Semiring A]
variable [Algebra k K]

/-- The canonical inclusion sends scalars from `k` through the scalar extension. -/
@[simp]
lemma includeRight_algebraMap [Algebra k A] (r : k) :
    Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A) (algebraMap k A r) =
      algebraMap K (HopfAlgebra.baseChange k K A) (algebraMap k K r) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

section CoalgebraStructOperations

variable [Algebra k A] [CoalgebraStruct k A]

/-- The counit of the canonical inclusion is obtained by extending scalars from `k` to `K`. -/
@[simp]
lemma counit_includeRight (a : A) :
    Coalgebra.counit (R := K)
        (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A) a :
          HopfAlgebra.baseChange k K A) =
      algebraMap k K (Coalgebra.counit (R := k) a) := by
  simp [Algebra.smul_def]

end CoalgebraStructOperations

section CoalgebraOperations

variable [Algebra k A] [Coalgebra k A]

/-- The comultiplication of the canonical inclusion is the scalar extension of the
comultiplication of the original coalgebra. -/
@[simp]
lemma comul_includeRight (a : A) :
    Coalgebra.comul (R := K)
        (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A) a :
          HopfAlgebra.baseChange k K A) =
      ∑ i ∈ (ℛ k a).index,
        Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A) ((ℛ k a).left i) ⊗ₜ[K]
          Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A) ((ℛ k a).right i) := by
  rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.comul_tmul]
  simp [← (ℛ k a).eq,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.tmul_sum]

end CoalgebraOperations

section HopfOperations

variable [HopfAlgebra k A]

/-- The antipode on scalar extension applies the antipode in each tensor factor on pure tensors. -/
@[simp]
lemma antipode_tmul (r : K) (a : A) :
    HopfAlgebraStruct.antipode K (r ⊗ₜ[k] a : HopfAlgebra.baseChange k K A) =
      HopfAlgebraStruct.antipode K r ⊗ₜ[k] HopfAlgebraStruct.antipode k a := by
  exact TauCeti.TensorProduct.antipode_tmul r a

/-- The antipode commutes with the canonical inclusion into the scalar extension. -/
@[simp]
lemma antipode_includeRight (a : A) :
    HopfAlgebraStruct.antipode K
        (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A) a :
          HopfAlgebra.baseChange k K A) =
      Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A)
        (HopfAlgebraStruct.antipode k a) := by
  simp

end HopfOperations

section Map

variable [Bialgebra k A]
variable {B C : Type*} [Semiring B] [Semiring C] [Bialgebra k B] [Bialgebra k C]

/-- Scalar extension of a bialgebra homomorphism. -/
noncomputable def map (f : A →ₐc[k] B) :
    HopfAlgebra.baseChange k K A →ₐc[K] HopfAlgebra.baseChange k K B :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) f

/-- Scalar extension of a bialgebra homomorphism agrees with `f` on the right tensor factor
and with the identity on scalars. -/
@[simp]
lemma map_tmul (f : A →ₐc[k] B) (r : K) (a : A) :
    map (K := K) f (r ⊗ₜ[k] a) = r ⊗ₜ[k] f a := by
  simp [map]

/-- Scalar extension sends the canonical inclusion of `a` to the canonical inclusion of `f a`. -/
@[simp]
lemma map_includeRight (f : A →ₐc[k] B) (a : A) :
    map (K := K) f (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A) a) =
      Algebra.TensorProduct.includeRight (R := k) (A := K) (B := B) (f a) := by
  simp

/-- Scalar extension sends the identity bialgebra homomorphism to the identity. -/
@[simp]
lemma map_id :
    map (K := K) (BialgHom.id k A) =
      BialgHom.id K (HopfAlgebra.baseChange k K A) := by
  exact Bialgebra.TensorProduct.map_id

/-- Scalar extension preserves composition of bialgebra homomorphisms. -/
lemma map_comp (g : B →ₐc[k] C) (f : A →ₐc[k] B) :
    map (K := K) (g.comp f) = (map (K := K) g).comp (map (K := K) f) := by
  exact Bialgebra.TensorProduct.map_comp (BialgHom.id K K) (BialgHom.id K K) g f

/-- Pointwise form of compatibility of scalar extension with composition. -/
@[simp]
lemma map_comp_apply (g : B →ₐc[k] C) (f : A →ₐc[k] B)
    (x : HopfAlgebra.baseChange k K A) :
    map (K := K) (g.comp f) x = map (K := K) g (map (K := K) f x) := by
  rw [map_comp]
  rfl

/-- The underlying algebra homomorphism of scalar extension is the usual tensor-product map. -/
@[simp]
lemma map_toAlgHom (f : A →ₐc[k] B) :
    (map (K := K) f : HopfAlgebra.baseChange k K A →ₐ[K] HopfAlgebra.baseChange k K B) =
      Algebra.TensorProduct.map (AlgHom.id K K) (f : A →ₐ[k] B) := by
  ext x
  simp [map]

/-- The underlying coalgebra homomorphism of scalar extension is the usual tensor-product map. -/
@[simp]
lemma map_toCoalgHom (f : A →ₐc[k] B) :
    (map (K := K) f : HopfAlgebra.baseChange k K A →ₗc[K] HopfAlgebra.baseChange k K B) =
      Coalgebra.TensorProduct.map (BialgHom.id K K : K →ₗc[K] K) (f : A →ₗc[k] B) := by
  ext x
  simp [map]

end Map

section HopfMap

variable [HopfAlgebra k A]
variable {B : Type*} [Semiring B] [HopfAlgebra k B]

/-- Scalar extension of a bialgebra homomorphism between Hopf algebras preserves antipodes. -/
@[simp]
lemma map_antipode (f : A →ₐc[k] B) (x : HopfAlgebra.baseChange k K A) :
    map (K := K) f (HopfAlgebraStruct.antipode K x) =
      HopfAlgebraStruct.antipode K (map (K := K) f x) := by
  exact TauCeti.BialgHom.map_antipode (map (K := K) f) x

end HopfMap

end BaseChange

end HopfAlgebra

end TauCeti
