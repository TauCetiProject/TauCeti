/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.RingTheory.TensorProduct.Free

import Mathlib.Algebra.Algebra.Bilinear

/-!
# Support submodules of additive monoid algebras

Mathlib's `AddMonoidAlgebra.supported` fixes the set of allowed exponents in a monoid algebra.
The supported characters form a basis, so extending scalars changes only their coefficients.
Convolution restricts to a bilinear map whenever addition of exponents lands in the target
support set.
-/

public section

open scoped Pointwise TensorProduct

namespace AddMonoidAlgebra

variable {M : Type*} {R S T : Type*}

section Basis

variable [Semiring R] (s : Set M)

/-- The monomial basis of the submodule supported on `s`, indexed by the elements of `s`. -/
noncomputable def supportedBasis : Module.Basis s R (supported R R s) :=
  Module.Basis.ofRepr (supportedEquivFinsupp s)

/-- The coordinates in the supported monomial basis are the corresponding coefficients. -/
@[simp]
theorem supportedBasis_repr_apply (f : supported R R s) (m : s) :
    (supportedBasis s).repr f m = (f : R[M]).coeff m :=
  (rfl)

/-- A supported monomial basis vector is the monomial with coefficient one at its index. -/
@[simp]
theorem coe_supportedBasis (m : s) :
    (supportedBasis (R := R) s m : R[M]) = single (m : M) 1 := by
  classical
  simp [supportedBasis, supportedEquivFinsupp]

end Basis

section Coefficients

variable [Semiring R] [Semiring S] [Semiring T] (s : Set M)

/-- Apply a ring homomorphism to the coefficients of a supported monoid-algebra element. -/
noncomputable def supportedMap (φ : R →+* S) :
    supported R R s →ₛₗ[φ] supported S S s :=
  (supportedEquivFinsupp s).symm.toLinearMap.comp <|
    (Finsupp.mapRange.linearMap φ.toSemilinearMap).comp (supportedEquivFinsupp s).toLinearMap

/-- Coefficient change applies the given map to each coefficient. -/
@[simp]
theorem coeff_supportedMap (φ : R →+* S) (f : supported R R s) (m : M) :
    (supportedMap s φ f : S[M]).coeff m = φ ((f : R[M]).coeff m) := by
  classical
  by_cases hm : m ∈ s
  · let j : s := ⟨m, hm⟩
    rw [← supportedBasis_repr_apply s _ j, ← supportedBasis_repr_apply s f j]
    simp [supportedMap, supportedBasis]
  · rw [mem_supported'.1 (supportedMap s φ f).property m hm, mem_supported'.1 f.property m hm,
      map_zero]

/-- Coefficient change of a supported element agrees with coefficient change in the ambient
algebra. -/
theorem coe_supportedMap [AddMonoid M] (φ : R →+* S) (f : supported R R s) :
    (supportedMap s φ f : S[M]) = mapRingHom M φ f := by
  ext m
  simp

@[simp]
theorem supportedMap_id (f : supported R R s) : supportedMap s (RingHom.id R) f = f := by
  apply Subtype.ext
  ext m
  simp

@[simp]
theorem supportedMap_comp (φ : R →+* S) (ψ : S →+* T) (f : supported R R s) :
    supportedMap s (ψ.comp φ) f = supportedMap s ψ (supportedMap s φ f) := by
  apply Subtype.ext
  ext m
  simp

end Coefficients

section BaseChange

variable [CommSemiring R] [Semiring S] [Algebra R S] (s : Set M)

/-- The scalar extension of the supported submodule is the submodule with the same allowed
exponents over the new coefficient semiring. -/
noncomputable def supportedBaseChange :
    S ⊗[R] supported R R s ≃ₗ[S] supported S S s :=
  (Algebra.TensorProduct.basis S (supportedBasis s)).repr.trans
    (supportedEquivFinsupp s).symm

/-- On pure tensors the scalar extension is coefficient change followed by scalar multiplication. -/
@[simp]
theorem supportedBaseChange_tmul (c : S) (f : supported R R s) :
    supportedBaseChange s (c ⊗ₜ[R] f) = c • supportedMap s (algebraMap R S) f := by
  apply (supportedBasis s).repr.injective
  ext m
  simp [supportedBaseChange, supportedBasis, supportedMap]

end BaseChange

section Multiplication

variable [Semiring R] [Add M] {s t u : Set M}

/-- The product of two elements with restricted supports is supported on any set containing all
sums of exponents of the two support sets. -/
theorem mul_mem_supported_of_add_subset (h : s + t ⊆ u) {f g : R[M]}
    (hf : f ∈ supported R R s) (hg : g ∈ supported R R t) :
    f * g ∈ supported R R u := by
  classical
  refine mem_supported.2 fun m hm ↦ h ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g hm)
  exact Set.add_mem_add (mem_supported.1 hf ha) (mem_supported.1 hg hb)

end Multiplication

variable [CommSemiring R] [AddMonoid M] {s t u : Set M}

/-- Convolution on supported submodules, with the target support specified by addition of
exponents. -/
noncomputable def supportedMul (h : s + t ⊆ u) :
    supported R R s →ₗ[R] supported R R t →ₗ[R] supported R R u :=
  ((LinearMap.mul R R[M]).domRestrict₁₂ _ _).codRestrict₂
    (supported R R u).subtype (Submodule.subtype_injective _) fun f g ↦ by
      rw [LinearMap.domRestrict₁₂_apply, LinearMap.mul_apply', Submodule.range_subtype]
      exact mul_mem_supported_of_add_subset h f.property g.property

/-- The product in the supported submodule is ordinary convolution in the ambient algebra. -/
@[simp]
theorem coe_supportedMul (h : s + t ⊆ u) (f : supported R R s) (g : supported R R t) :
    (supportedMul h f g : R[M]) = (f : R[M]) * (g : R[M]) := by
  rw [← Submodule.subtype_apply, supportedMul, LinearMap.codRestrict₂_apply,
    LinearMap.domRestrict₁₂_apply, LinearMap.mul_apply']

/-- Coefficient change commutes with convolution on supported submodules. -/
@[simp]
theorem supportedMap_mul [CommSemiring S] (φ : R →+* S) (h : s + t ⊆ u)
    (f : supported R R s) (g : supported R R t) :
    supportedMap u φ (supportedMul h f g) =
      supportedMul h (supportedMap s φ f) (supportedMap t φ g) := by
  apply Subtype.ext
  simp only [coe_supportedMap, coe_supportedMul, map_mul]

end AddMonoidAlgebra
