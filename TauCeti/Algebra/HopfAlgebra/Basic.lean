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
  -- Postcomposing `S * id = 1` with `φ` makes `φ ∘ S` a left convolution inverse of `φ`;
  -- precomposing `id * S = 1` with `φ` makes `S ∘ φ` a right one.
  apply toConv_injective
  refine left_inv_eq_right_inv (a := toConv (φ : A →ₗ[R] B)) ?_ ?_
  · have h := congr((AlgHom.ofClass φ).convPostcomp $(LinearMap.antipode_mul_id (C := A)))
    rw [map_mul, map_one] at h
    convert h using 2 <;> ext <;> simp
  · have h := congr((CoalgHom.ofClass φ).convPrecomp $(LinearMap.id_mul_antipode (C := B)))
    rw [map_mul, map_one] at h
    convert h using 2 <;> ext <;> simp

/-- A bialgebra-hom-like map between Hopf algebras commutes with the antipodes, pointwise. -/
@[simp]
theorem map_antipode (φ : F) (a : A) :
    φ (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (φ a) :=
  LinearMap.congr_fun (coe_comp_antipode φ) a

end BialgHomClass
