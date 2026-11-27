/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers along a bijective change of scalars

Let `S` be an `R`-algebra and `M` an `S`-module, viewed as an `R`-module by restriction. Sending
`m₁ ∧ ⋯ ∧ mₙ` over `R` to the same wedge over `S` defines an `R`-linear comparison
`⋀[R]^n M → ⋀[S]^n M`. It is surjective when `algebraMap R S` is, and an isomorphism when
`algebraMap R S` is bijective. The latter case arises when a ring carries a second name, such as a
copy of `ℂ` with a different algebra structure over a subring: the exterior powers of a module over
the two names of the ring are then canonically identified.

## Main definitions

* `exteriorPower.restrictScalars`: the comparison `⋀[R]^n M →ₗ[R] ⋀[S]^n M`.
* `exteriorPower.restrictScalarsEquiv`: the comparison as an isomorphism, when `algebraMap R S`
  is bijective.
-/

public section

noncomputable section

namespace exteriorPower

open Function

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M]

variable (R S M) in
/-- The comparison `⋀[R]^n M → ⋀[S]^n M` sending a wedge over `R` to the same wedge over `S`. -/
def restrictScalars (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[S]^n M :=
  alternatingMapLinearEquiv
    { (ιMulti S n).toMultilinearMap.restrictScalars R with
      map_eq_zero_of_eq' := fun _ _ _ ↦ (ιMulti S n).map_eq_zero_of_eq _ }

@[simp]
theorem restrictScalars_ιMulti (n : ℕ) (m : Fin n → M) :
    restrictScalars R S M n (ιMulti R n m) = ιMulti S n m :=
  alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The comparison `⋀[R]^n M → ⋀[S]^n M` is surjective when `algebraMap R S` is surjective. -/
theorem restrictScalars_surjective (h : Surjective (algebraMap R S)) (n : ℕ) :
    Surjective (restrictScalars R S M n) := by
  intro y
  induction mem_span_ιMulti y using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨_, restrictScalars_ιMulti n m⟩
  | zero => exact ⟨0, map_zero _⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
  | smul s _ _ hx =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := h s
    exact ⟨r • x, by rw [map_smul, algebraMap_smul]⟩

/-- A left inverse of the comparison, for any action of `S` on `⋀[R]^n M` through which
`algebraMap R S r` acts as `r`. -/
private def restrictScalarsInv (n : ℕ) [Module S (⋀[R]^n M)]
    (hs : ∀ (r : R) (z : ⋀[R]^n M), algebraMap R S r • z = r • z)
    (h : Surjective (algebraMap R S)) : ⋀[S]^n M →ₗ[S] ⋀[R]^n M :=
  alternatingMapLinearEquiv
    { toFun := fun m ↦ ιMulti R n m
      map_update_add' := fun m i x y ↦ (ιMulti R n).map_update_add m i x y
      map_update_smul' := fun m i s x ↦ by
        obtain ⟨r, rfl⟩ := h s
        rw [RingHom.id_apply, hs, algebraMap_smul, (ιMulti R n).map_update_smul]
      map_eq_zero_of_eq' := fun _ _ _ ↦ (ιMulti R n).map_eq_zero_of_eq _ }

theorem restrictScalars_injective (h : Bijective (algebraMap R S)) (n : ℕ) :
    Injective (restrictScalars R S M n) := by
  let _ : Module S (⋀[R]^n M) := Module.compHom _ (RingEquiv.ofBijective _ h).symm.toRingHom
  have hs (r : R) (z : ⋀[R]^n M) : algebraMap R S r • z = r • z :=
    congrArg (· • z) ((RingEquiv.ofBijective _ h).symm_apply_apply r)
  have : IsScalarTower R S (⋀[R]^n M) := ⟨fun r s z ↦ by rw [Algebra.smul_def, mul_smul, hs]⟩
  have hinv : (restrictScalarsInv n hs h.2).restrictScalars R ∘ₗ restrictScalars R S M n =
      LinearMap.id :=
    linearMap_ext <| AlternatingMap.ext fun m ↦ by simp [restrictScalarsInv]
  exact LeftInverse.injective (g := restrictScalarsInv n hs h.2) (LinearMap.congr_fun hinv)

variable (h : Bijective (algebraMap R S))

/-- When `algebraMap R S` is bijective, the comparison `⋀[R]^n M ≃ₗ[R] ⋀[S]^n M` sending a wedge
over `R` to the same wedge over `S` is an isomorphism. -/
def restrictScalarsEquiv (n : ℕ) : ⋀[R]^n M ≃ₗ[R] ⋀[S]^n M :=
  .ofBijective (restrictScalars R S M n)
    ⟨restrictScalars_injective h n, restrictScalars_surjective h.2 n⟩

@[simp]
theorem restrictScalarsEquiv_apply (n : ℕ) (x : ⋀[R]^n M) :
    restrictScalarsEquiv h n x = restrictScalars R S M n x :=
  (rfl)

theorem restrictScalarsEquiv_ιMulti (n : ℕ) (m : Fin n → M) :
    restrictScalarsEquiv h n (ιMulti R n m) = ιMulti S n m := by
  simp

@[simp]
theorem restrictScalarsEquiv_symm_ιMulti (n : ℕ) (m : Fin n → M) :
    (restrictScalarsEquiv h n).symm (ιMulti S n m) = ιMulti R n m := by
  rw [LinearEquiv.symm_apply_eq, restrictScalarsEquiv_ιMulti]

end exteriorPower
