/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Defs

/-!
# Restricting automorphisms along an embedding of a normal extension

Mathlib's `AlgEquiv.restrictNormalHom` restricts automorphisms of `K/F` to a normal subextension
`M/F` given by a scalar tower `F → M → K`. This file restricts along an arbitrary embedding
`f : M →ₐ[F] K` instead, which is convenient when `M` is an intermediate field sitting inside `K`
through a map other than the algebra map (for example an `IntermediateField.inclusion`).

## Main definitions and results

* `AlgHom.restrictNormalHom`: restriction `Gal(K/F) →* Gal(M/F)` along `f : M →ₐ[F] K`.
* `AlgHom.restrictNormalHom_eq_iff`: `f.restrictNormalHom σ` is the unique automorphism of `M`
  intertwined with `σ` by `f`.
* `AlgHom.restrictNormalHom_toAlgHom`: for the algebra map of a scalar tower this is
  `AlgEquiv.restrictNormalHom`.
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

/-- **Mathlib's two restriction APIs agree on elements.** `AlgEquiv.restrictNormalHom` is the
bundled `MonoidHom` built from `AlgEquiv.restrictNormal`, so applying it is definitionally the
latter. Stating the identification once lets proofs rewrite between the two rather than lean on
the `MonoidHom.mk'` wrapper unfolding, which is an artefact of the bundling and not a documented
part of the API.

Mathlib's `AlgEquiv.restrictNormalHom_apply` covers only the case where the subextension is an
`IntermediateField`; this is the abstract scalar-tower form. -/
@[simp]
theorem _root_.AlgEquiv.restrictNormalHom_eq_restrictNormal [Algebra M K] [IsScalarTower F M K]
    [Normal F M] (σ : Gal(K/F)) : AlgEquiv.restrictNormalHom M σ = σ.restrictNormal M :=
  rfl

end RestrictAlong

end TauCeti
