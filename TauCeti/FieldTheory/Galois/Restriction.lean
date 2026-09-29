/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Restricting automorphisms along an embedding of a normal extension

Mathlib's `AlgEquiv.restrictNormalHom` restricts automorphisms of `K/F` to a normal subextension
`M/F` given by a scalar tower `F → M → K`. This file restricts along an arbitrary embedding
`f : M →ₐ[F] K` instead, which is convenient when `M` is an intermediate field sitting inside `K`
through a map other than the algebra map (for example an `IntermediateField.inclusion`).

In an abstract scalar tower with a normal intermediate field, restriction to the intermediate
field is the identity precisely when the automorphism fixes it pointwise; its kernel is the image
of restriction of scalars.

## Main definitions and results

* `AlgHom.restrictNormalHom`: restriction `Gal(K/F) →* Gal(M/F)` along `f : M →ₐ[F] K`.
* `AlgHom.restrictNormalHom_eq_iff`: `f.restrictNormalHom σ` is the unique automorphism of `M`
  intertwined with `σ` by `f`.
* `AlgHom.restrictNormalHom_toAlgHom`: for the algebra map of a scalar tower this is
  `AlgEquiv.restrictNormalHom`.
* `AlgHom.restrictNormalHom_surjective` and `AlgHom.ker_restrictNormalHom`: for a normal `K/F`
  restriction is surjective, and its kernel is the subgroup fixing the image of `f`.
* `AlgEquiv.restrictNormal_eq_one_iff_algebraMap`: restriction is trivial precisely when the
  automorphism fixes the intermediate field pointwise.
* `AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one` and
  `AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom`: the restriction kernel is
  the image of restriction of scalars.
* `AlgEquiv.restrictNormal_mul_restrictScalars`: multiplying by an automorphism of the top field
  over the intermediate one does not change the restriction.
-/

public section

namespace TauCeti

section RestrictAlong

variable {F K M : Type*} [Field F] [Field K] [Field M] [Algebra F K] [Algebra F M]

/-- Restriction of automorphisms along an embedding `f : M →ₐ[F] K` of a normal extension `M/F`.
Every `σ : Gal(K/F)` maps the image of `f` to itself, and `f.restrictNormalHom σ` is the
automorphism of `M` it induces, so that `f (f.restrictNormalHom σ x) = σ (f x)`
(`AlgHom.restrictNormalHom_commutes`). For the algebra map of a scalar tower this is
`AlgEquiv.restrictNormalHom` (`AlgHom.restrictNormalHom_toAlgHom`). -/
noncomputable def _root_.AlgHom.restrictNormalHom (f : M →ₐ[F] K) [Normal F M] :
    Gal(K/F) →* Gal(M/F) :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormalHom M

@[simp]
theorem _root_.AlgHom.restrictNormalHom_commutes (f : M →ₐ[F] K) [Normal F M] (σ : Gal(K/F))
    (x : M) : f (f.restrictNormalHom σ x) = σ (f x) :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormal_commutes σ M x

/-- `f.restrictNormalHom σ` is the unique automorphism of `M` intertwined with `σ` by `f`. -/
theorem _root_.AlgHom.restrictNormalHom_eq_iff (f : M →ₐ[F] K) [Normal F M] {σ : Gal(K/F)}
    {τ : Gal(M/F)} : f.restrictNormalHom σ = τ ↔ ∀ x, σ (f x) = f (τ x) := by
  refine ⟨fun h x ↦ by rw [← h, AlgHom.restrictNormalHom_commutes], fun h ↦ ?_⟩
  ext x
  exact f.injective ((f.restrictNormalHom_commutes σ x).trans (h x))

/-- For the algebra map of a scalar tower, restriction along it is Mathlib's
`AlgEquiv.restrictNormalHom`. -/
@[simp]
theorem _root_.AlgHom.restrictNormalHom_toAlgHom [Algebra M K] [IsScalarTower F M K]
    [Normal F M] :
    (IsScalarTower.toAlgHom F M K).restrictNormalHom = AlgEquiv.restrictNormalHom M :=
  MonoidHom.ext fun σ ↦ (IsScalarTower.toAlgHom F M K).restrictNormalHom_eq_iff.2
    fun y ↦ (AlgEquiv.restrictNormal_commutes σ M y).symm

/-- For a normal `K/F`, every automorphism of `M/F` is the restriction of one of `K/F`. -/
theorem _root_.AlgHom.restrictNormalHom_surjective (f : M →ₐ[F] K) [Normal F M] [Normal F K] :
    Function.Surjective f.restrictNormalHom :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormalHom_surjective K

/-- The kernel of restriction along `f` is the subgroup fixing the image of `f` pointwise. -/
theorem _root_.AlgHom.ker_restrictNormalHom (f : M →ₐ[F] K) [Normal F M] :
    f.restrictNormalHom.ker = f.fieldRange.fixingSubgroup := by
  ext σ
  simp [f.restrictNormalHom_eq_iff]

end RestrictAlong

end TauCeti

/-! ### Restriction to an intermediate field in a tower -/

section Tower

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Normal K L]
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- **`σ` restricts to the identity on `L` exactly when it fixes `L` pointwise.** Mathlib's
`AlgEquiv.restrictNormal_eq_one_iff` says this for an `IntermediateField`, while
`AlgEquiv.restrictNormal` itself is already stated for an abstract algebra `L`, so only the
characterisation needs transporting to a tower `K ⊆ L ⊆ M`. -/
theorem AlgEquiv.restrictNormal_eq_one_iff_algebraMap (σ : M ≃ₐ[K] M) :
    σ.restrictNormal L = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  constructor
  · intro h x
    rw [← AlgEquiv.restrictNormal_commutes σ L x, h, AlgEquiv.one_apply]
  · intro h
    ext x
    have hx := AlgEquiv.restrictNormal_commutes σ L x
    rw [h x] at hx
    exact (algebraMap L M).injective hx

/-- Restriction as a group homomorphism agrees with restriction of an automorphism. -/
theorem AlgEquiv.restrictNormalHom_apply_eq_restrictNormal (σ : M ≃ₐ[K] M) :
    (AlgEquiv.restrictNormalHom L) σ = σ.restrictNormal L :=
  rfl

/-- An automorphism of `M/K` comes from an automorphism of `M/L` exactly when its restriction to
`L` is the identity. -/
theorem AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one
    (σ : M ≃ₐ[K] M) :
    σ ∈ (AlgEquiv.restrictScalarsHom (S := L) K).range ↔ σ.restrictNormal L = 1 := by
  constructor
  · rintro ⟨τ, rfl⟩
    apply (AlgEquiv.restrictNormal_eq_one_iff_algebraMap K L M _).2
    intro x
    exact τ.commutes x
  · intro h
    let τ : M ≃ₐ[L] M := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      ((AlgEquiv.restrictNormal_eq_one_iff_algebraMap K L M σ).1 h)
    exact ⟨τ, AlgEquiv.ext fun x ↦ by simp [τ]⟩

/-- The image of `Gal(M/L)` in `Gal(M/K)` under restriction of scalars is the kernel of
restriction to `L`. -/
theorem AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom :
    (AlgEquiv.restrictScalarsHom (S := L) K).range =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).ker := by
  ext σ
  rw [AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M, MonoidHom.mem_ker,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal]

/-- Multiplying by an automorphism of `M/L` does not change the restriction to `L`. -/
@[simp]
theorem AlgEquiv.restrictNormal_mul_restrictScalars (σ : M ≃ₐ[K] M) (τ : M ≃ₐ[L] M) :
    (σ * τ.restrictScalars K).restrictNormal L = σ.restrictNormal L := by
  rw [← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M, map_mul,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
    (AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M
      (τ.restrictScalars K)).1 ⟨τ, rfl⟩, mul_one]

end Tower
