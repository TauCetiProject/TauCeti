/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Functoriality of the graded tensor product of algebras

Mathlib's `GradedTensorProduct R 𝒜 ℬ`, written `𝒜 ᵍ⊗[R] ℬ`, is the tensor product `A ⊗[R] B` with
the Koszul-signed multiplication. Its universal property `GradedTensorProduct.lift` assembles an
algebra map out of it from two maps that supercommute on homogeneous elements. This file uses it
to make the construction functorial in homomorphisms of graded algebras: two graded algebra maps
`f : 𝒜 →ₐᵍ[R] 𝒞` and `g : ℬ →ₐᵍ[R] 𝒟` induce `a ᵍ⊗ₜ b ↦ f a ᵍ⊗ₜ g b`. Grading preservation is
what makes the Koszul signs on the two sides agree, so an arbitrary pair of algebra maps does not
induce a map of graded tensor products.

The construction is used to compare Clifford algebras of orthogonal sums along quadratic
isometries, through Mathlib's `CliffordAlgebra.prodEquiv`.

## Main definitions

* `GradedTensorProduct.map`: the algebra map `𝒜 ᵍ⊗[R] ℬ →ₐ[R] 𝒞 ᵍ⊗[R] 𝒟` induced by graded
  algebra maps `f` and `g`.

## Main results

* `GradedTensorProduct.map_tmul`: `map f g (a ᵍ⊗ₜ b) = f a ᵍ⊗ₜ g b`.
* `GradedTensorProduct.map_comp_includeLeft`, `GradedTensorProduct.map_comp_includeRight`: the
  restrictions of `map f g` to the two factors.
* `GradedTensorProduct.map_id`, `GradedTensorProduct.map_comp`: functoriality.
-/

public section

open scoped TensorProduct

namespace GradedTensorProduct

variable {R ι A B C D : Type*}
variable [CommSemiring ι] [DecidableEq ι] [Module ι (Additive ℤˣ)]
variable [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
variable {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
  {𝒞 : ι → Submodule R C} {𝒟 : ι → Submodule R D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

/-- The algebra map `𝒜 ᵍ⊗[R] ℬ →ₐ[R] 𝒞 ᵍ⊗[R] 𝒟`, `a ᵍ⊗ₜ b ↦ f a ᵍ⊗ₜ g b`, induced by two
homomorphisms of graded algebras. -/
noncomputable def map (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒟) : 𝒜 ᵍ⊗[R] ℬ →ₐ[R] 𝒞 ᵍ⊗[R] 𝒟 :=
  lift 𝒜 ℬ ((includeLeft 𝒞 𝒟).comp f) ((includeRight 𝒞 𝒟).comp g) fun i j a b ↦ by
    -- The images `f a ∈ 𝒞 i` and `g b ∈ 𝒟 j` are homogeneous of the same degrees, so the Koszul
    -- sign of `𝒞 ᵍ⊗[R] 𝒟` is the required one.
    have h := tmul_coe_mul_coe_tmul 𝒞 𝒟 (1 : C) ⟨g b, GradedFunLike.map_mem g b.property⟩
      ⟨f a, GradedFunLike.map_mem f a.property⟩ (1 : D)
    simp only [one_mul, mul_one] at h
    simp only [AlgHom.comp_apply, GradedAlgHom.coe_toAlgHom, includeLeft_apply,
      includeRight_apply, h, tmul_one_mul_one_tmul, smul_smul, Int.units_mul_self, one_smul]

/-- `GradedTensorProduct.map f g` applies `f` and `g` to the two factors of a pure tensor. -/
@[simp]
theorem map_tmul (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒟) (a : A) (b : B) :
    map f g (a ᵍ⊗ₜ b) = f a ᵍ⊗ₜ g b := by
  simp only [map, lift_tmul, AlgHom.comp_apply, GradedAlgHom.coe_toAlgHom, includeLeft_apply,
    includeRight_apply, tmul_one_mul_one_tmul]

/-- On the left factor, `GradedTensorProduct.map f g` is `f` followed by the left inclusion. -/
@[simp]
theorem map_comp_includeLeft (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒟) :
    (map f g).comp (includeLeft 𝒜 ℬ) = (includeLeft 𝒞 𝒟).comp (f : A →ₐ[R] C) := by
  ext a
  simp

/-- On the right factor, `GradedTensorProduct.map f g` is `g` followed by the right inclusion. -/
@[simp]
theorem map_comp_includeRight (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒟) :
    (map f g).comp (includeRight 𝒜 ℬ) = (includeRight 𝒞 𝒟).comp (g : B →ₐ[R] D) := by
  ext b
  simp

variable (𝒜 ℬ) in
/-- The identity maps of the two factors induce the identity of the graded tensor product. -/
@[simp]
theorem map_id : map (GradedAlgHom.id R 𝒜) (GradedAlgHom.id R ℬ) = AlgHom.id R (𝒜 ᵍ⊗[R] ℬ) := by
  ext <;> simp

/-- `GradedTensorProduct.map` respects composition of graded algebra maps. -/
theorem map_comp {A' B' : Type*} [Ring A'] [Ring B'] [Algebra R A'] [Algebra R B']
    {𝒜' : ι → Submodule R A'} {ℬ' : ι → Submodule R B'} [GradedAlgebra 𝒜'] [GradedAlgebra ℬ']
    (f' : 𝒞 →ₐᵍ[R] 𝒜') (g' : 𝒟 →ₐᵍ[R] ℬ') (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒟) :
    map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) := by
  ext <;> simp

end GradedTensorProduct
