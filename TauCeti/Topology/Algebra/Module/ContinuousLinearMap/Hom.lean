/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Bundling continuous linear maps as algebra homomorphisms

A continuous `R`-linear map between topological `R`-algebras that preserves multiplication bundles
directly as a continuous nonunital `R`-algebra homomorphism
(`ContinuousLinearMap.toNonUnitalAlgHomOfMul`), and if it additionally preserves `star`, as a
continuous nonunital `⋆`-algebra homomorphism
(`ContinuousLinearMap.toNonUnitalStarAlgHomOfMulStar`).
-/

public section

namespace ContinuousLinearMap

section AlgHomExtension

variable {R A B : Type*} [Semiring R]
  [TopologicalSpace A] [NonUnitalNonAssocSemiring A] [Module R A]
  [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [Module R B]

/-- Bundle a multiplicative continuous linear map `f : A →L[R] B` as a nonunital `R`-algebra
homomorphism. -/
def toNonUnitalAlgHomOfMul (f : A →L[R] B) (hf_mul : ∀ x y : A, f (x * y) = f x * f y) :
    A →ₙₐ[R] B where
  toFun := f
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := hf_mul

@[simp]
theorem toNonUnitalAlgHomOfMul_apply (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (x : A) :
    f.toNonUnitalAlgHomOfMul hf_mul x = f x :=
  (rfl)

theorem coe_toNonUnitalAlgHomOfMul (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) :
    ⇑(f.toNonUnitalAlgHomOfMul hf_mul) = f :=
  (rfl)

@[fun_prop]
theorem continuous_toNonUnitalAlgHomOfMul (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) :
    Continuous (f.toNonUnitalAlgHomOfMul hf_mul) :=
  f.continuous

end AlgHomExtension

section StarAlgHomExtension

variable {R A B : Type*} [Semiring R]
  [TopologicalSpace A] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- Bundle a multiplicative star-preserving continuous linear map `f : A →L[R] B` as a nonunital
`⋆`-algebra homomorphism. -/
def toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    A →⋆ₙₐ[R] B where
  __ := f.toNonUnitalAlgHomOfMul hf_mul
  map_star' := hf_star

/-- The underlying nonunital algebra homomorphism of `f.toNonUnitalStarAlgHomOfMulStar` is
`f.toNonUnitalAlgHomOfMul`. -/
@[simp]
theorem toNonUnitalAlgHom_toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    (f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star).toNonUnitalAlgHom =
      f.toNonUnitalAlgHomOfMul hf_mul :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHomOfMulStar_apply (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x))
    (x : A) :
    f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star x = f x :=
  (rfl)

theorem coe_toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    ⇑(f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star) = f :=
  (rfl)

@[fun_prop]
theorem continuous_toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    Continuous (f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star) :=
  f.continuous

end StarAlgHomExtension

end ContinuousLinearMap
