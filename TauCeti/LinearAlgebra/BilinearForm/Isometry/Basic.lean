/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Isometry
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Isometric endomorphisms of a bilinear form

This file defines the predicate that an endomorphism preserves a bilinear form and provides its
elementary API, including the bridge to Mathlib's bundled isometric maps. It also records that
scaling two forms by the same non-zero-divisor preserves whether they are isometric
(`LinearMap.BilinForm.equivalent_smul_iff`), and gives the evaluation lemmas
`LinearMap.BilinForm.IsometryEquiv.trans_apply`,
`LinearMap.BilinForm.IsometryEquiv.symm_apply_apply` and
`LinearMap.BilinForm.IsometryEquiv.apply_symm_apply` for Mathlib's isometric equivalences, which
map the kernel of one form onto the kernel of the other
(`LinearMap.BilinForm.IsometryEquiv.map_ker`).
Isometric bilinear forms have isometric associated quadratic maps
(`LinearMap.BilinForm.Equivalent.toQuadraticMap`). The isometry group and the determinant,
base-change, and orthogonal-complement API are developed in
`TauCeti.LinearAlgebra.BilinearForm.Isometry`.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- An endomorphism `f` of `M` is an *isometry* of the bilinear form `B` when it preserves `B`,
that is, when `B (f x) (f y) = B x y` for all `x` and `y`.

Isometric endomorphisms form a monoid, not a group: for the zero form on `ℤ ^ 2` every endomorphism
is one. For a finite free `ℤ`-module `V` and a left-separating integral form `Q` an isometric
endomorphism is automatically invertible (`TauCeti.BilinForm.IsIsometry.toIsometryGroup`), and the
resulting automorphisms are the arithmetic group `Aut(V, Q)`; see
`TauCeti.BilinForm.isometryGroup`. -/
def IsIsometry (B : BilinForm R M) (f : M →ₗ[R] M) : Prop :=
  ∀ x y, B (f x) (f y) = B x y

variable {B : BilinForm R M} {f g : M →ₗ[R] M}

/-- An endomorphism is an isometry of `B` exactly when it preserves `B` pointwise. -/
theorem isIsometry_iff : IsIsometry B f ↔ ∀ x y, B (f x) (f y) = B x y := (Iff.rfl)

/-- An endomorphism is an isometry of `B` exactly when precomposing `B` with it on both sides
returns `B`. -/
theorem isIsometry_iff_comp : IsIsometry B f ↔ B.comp f f = B :=
  ⟨fun h => LinearMap.BilinForm.ext fun x y => h x y, fun h x y =>
    LinearMap.BilinForm.congr_fun h x y⟩

/-- The underlying map of one of Mathlib's isometric maps `B →bᵢ B` is an isometry. -/
theorem isIsometry_toLinearMap (φ : B →bᵢ B) : IsIsometry B φ.toLinearMap := φ.map_app

namespace IsIsometry

/-- An isometry takes the same value under `B` after applying the endomorphism to both inputs. -/
@[grind =]
protected theorem apply (hf : IsIsometry B f) (x y : M) : B (f x) (f y) = B x y :=
  isIsometry_iff.mp hf x y

/-- An isometry, bundled as one of Mathlib's isometric maps `B →bᵢ B`. -/
def toIsometry (hf : IsIsometry B f) : B →bᵢ B := ⟨f, hf⟩

@[simp]
theorem toIsometry_apply (hf : IsIsometry B f) (x : M) : hf.toIsometry x = f x := (rfl)

@[simp]
theorem toIsometry_toLinearMap (hf : IsIsometry B f) : hf.toIsometry.toLinearMap = f := (rfl)

protected theorem id : IsIsometry B LinearMap.id := fun _ _ => rfl

protected theorem comp (hf : IsIsometry B f) (hg : IsIsometry B g) : IsIsometry B (f ∘ₗ g) :=
  fun x y => (hf (g x) (g y)).trans (hg x y)

end IsIsometry

end CommSemiring

end BilinForm

end TauCeti

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {C : BilinForm R M} {C' : BilinForm R M'} {a : R}

/-- Scaling two bilinear forms by the same non-zero-divisor `a` neither creates nor destroys an
isometry between them. In particular the constituents `a • C` and `a • C'` of two Jordan splittings
are isometric exactly when their unimodular rescalings `C` and `C'` are. -/
@[simp] theorem equivalent_smul_iff (ha : a ∈ nonZeroDivisors R) :
    (a • C).Equivalent (a • C') ↔ C.Equivalent C' :=
  ⟨fun ⟨e⟩ ↦ ⟨⟨e.toLinearEquiv, fun x y ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp (by
      simpa using e.map_app y x)⟩⟩,
    fun ⟨e⟩ ↦ ⟨⟨e.toLinearEquiv, fun x y ↦ by simp⟩⟩⟩

namespace IsometryEquiv

variable {R M₁ M₂ M₃ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃] {B₁ : BilinForm R M₁}
  {B₂ : BilinForm R M₂} {B₃ : BilinForm R M₃}

/-- A composite of isometric equivalences applies the first and then the second. -/
@[simp]
theorem trans_apply (f : B₁.IsometryEquiv B₂) (g : B₂.IsometryEquiv B₃) (x : M₁) :
    f.trans g x = g (f x) :=
  (rfl)

/-- The inverse of an isometric equivalence undoes it. -/
@[simp]
theorem symm_apply_apply (f : B₁.IsometryEquiv B₂) (x : M₁) : f.symm (f x) = x :=
  f.toLinearEquiv.symm_apply_apply x

/-- An isometric equivalence undoes its inverse. -/
@[simp]
theorem apply_symm_apply (f : B₁.IsometryEquiv B₂) (x : M₂) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

/-- An isometric equivalence maps the kernel of one bilinear form onto the kernel of the other. -/
theorem map_ker (f : B₁.IsometryEquiv B₂) :
    (LinearMap.ker B₁).map (f : M₁ ≃ₗ[R] M₂).toLinearMap = LinearMap.ker B₂ := by
  ext y
  obtain ⟨x, rfl⟩ := (f : M₁ ≃ₗ[R] M₂).surjective y
  simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, LinearMap.mem_ker,
    LinearMap.ext_iff, LinearMap.zero_apply]
  -- Every vector of `M₂` is `f z`, and `B₂ (f x) (f z) = B₁ x z`.
  rw [← (f : M₁ ≃ₗ[R] M₂).toEquiv.forall_congr_right]
  simp

end IsometryEquiv

/-- Isometric bilinear forms have isometric associated quadratic maps `x ↦ B x x`. -/
theorem Equivalent.toQuadraticMap {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂}
    (h : B₁.Equivalent B₂) : B₁.toQuadraticMap.Equivalent B₂.toQuadraticMap :=
  h.map fun f ↦ { f.toLinearEquiv with map_app' := fun x ↦ by simp }

end LinearMap.BilinForm
