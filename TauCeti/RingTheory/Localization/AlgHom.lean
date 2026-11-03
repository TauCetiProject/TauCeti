/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Algebra homomorphisms out of a localization

Let `B` be a localization of a commutative `k`-algebra `A` at a submonoid `M`. Restriction along
`A → B` identifies the `k`-algebra homomorphisms `B →ₐ[k] R` with those `A →ₐ[k] R` sending every
element of `M` to a unit: it is injective by `IsLocalization.algHom_ext`, and this file computes
its image. For a localization away from `f`, the image consists of the homomorphisms sending `f`
to a unit. In the language of points, the `R`-points of the basic open `Spec A_f` of `Spec A` are
the `R`-points of `Spec A` at which `f` takes a unit value.

## Main results

* `IsLocalization.range_comp_toAlgHom`: the image of restriction along `A → B` for a localization
  at `M` is `{x | ∀ m ∈ M, IsUnit (x m)}`.
* `IsLocalization.Away.range_comp_toAlgHom`: for a localization away from `f`, the image is
  `{x | IsUnit (x f)}`.
-/

public section

variable {k A B R : Type*} [CommSemiring k] [CommSemiring A] [Algebra k A]
  [CommSemiring B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [CommSemiring R] [Algebra k R]

/-- A `k`-algebra homomorphism out of `A` extends to the localization `B` of `A` at `M` exactly
when it sends every element of `M` to a unit. -/
theorem IsLocalization.range_comp_toAlgHom (M : Submonoid A) [IsLocalization M B] :
    Set.range (fun x : B →ₐ[k] R ↦ x.comp (IsScalarTower.toAlgHom k A B)) =
      {x | ∀ m ∈ M, IsUnit (x m)} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ m hm
    exact (IsLocalization.map_units B ⟨m, hm⟩).map y
  · intro hx
    exact ⟨IsLocalization.liftAlgHom (S := B) fun m : M ↦ hx m m.2,
      AlgHom.ext fun a ↦ IsLocalization.lift_eq _ a⟩

/-- A `k`-algebra homomorphism out of `A` extends to the localization `B` of `A` away from `f`
exactly when it sends `f` to a unit. -/
theorem IsLocalization.Away.range_comp_toAlgHom (f : A) [IsLocalization.Away f B] :
    Set.range (fun x : B →ₐ[k] R ↦ x.comp (IsScalarTower.toAlgHom k A B)) =
      {x | IsUnit (x f)} := by
  rw [IsLocalization.range_comp_toAlgHom (Submonoid.powers f)]
  ext x
  refine ⟨fun hx ↦ hx f (Submonoid.mem_powers f), ?_⟩
  rintro hx _ ⟨n, rfl⟩
  simpa only [map_pow] using hx.pow n
