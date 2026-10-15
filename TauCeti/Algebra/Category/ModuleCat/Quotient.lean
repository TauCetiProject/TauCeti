/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Maps induced on presented quotients in `ModuleCat`

An object `A` of `ModuleCat R` is frequently *presented* as a quotient `X ⧸ p`, by an isomorphism
`e : A ≅ ModuleCat.of R (X ⧸ p)` together with a projection `π : ModuleCat.of R X ⟶ A` playing
the role of `Submodule.mkQ`, in the sense that `π ≫ e.hom = ModuleCat.ofHom p.mkQ`. A linear map
`f : X₁ →ₗ[R] X₂` carrying `p₁` into `p₂` then induces a map `A₁ ⟶ A₂`, namely `Submodule.mapQ`
conjugated by the two presentations.

This file records the one fact such an induced map is used through: it sends the class `π₁ x` of a
representative to the class `π₂ (f x)`, which is Mathlib's `Submodule.mapQ_mkQ` transported along
the two presentations. Since the presentations are only given up to isomorphism, this
characterisation — rather than a definitional unfolding — is how the induced map is computed.

The canonical short complex `S → M → M / S` and its short exactness are also
packaged here. Its extension class computes degree-one extensions when `M` is
projective. The abbreviation keeps the three modules and the two linear maps
available to the categorical exactness and extension APIs.

## Main statements

* `ModuleCat.comp_conj_mapQ`: the map induced by `f` on two presented quotients composed with the
  projection of the source is the projection of the target composed with `f`.
-/

public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {R : Type v} [Ring R]

/-- A map conjugated from `Submodule.mapQ p₁ p₂ f` along presentations `e₁`, `e₂` of two objects
as the quotients sends the class `π₁ x` of a representative to the class `π₂ (f x)`. This is
`Submodule.mapQ_mkQ` transported along the two presentations. -/
theorem comp_conj_mapQ {X₁ X₂ : Type u} [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂]
    [Module R X₂] {p₁ : Submodule R X₁} {p₂ : Submodule R X₂} {A₁ A₂ : ModuleCat.{u} R}
    (e₁ : A₁ ≅ ModuleCat.of R (X₁ ⧸ p₁)) (e₂ : A₂ ≅ ModuleCat.of R (X₂ ⧸ p₂))
    {π₁ : ModuleCat.of R X₁ ⟶ A₁} {π₂ : ModuleCat.of R X₂ ⟶ A₂}
    (hπ₁ : π₁ ≫ e₁.hom = ModuleCat.ofHom p₁.mkQ) (hπ₂ : π₂ ≫ e₂.hom = ModuleCat.ofHom p₂.mkQ)
    (f : X₁ →ₗ[R] X₂) (hf : p₁ ≤ p₂.comap f) :
    π₁ ≫ e₁.hom ≫ ModuleCat.ofHom (p₁.mapQ p₂ f hf) ≫ e₂.inv = ModuleCat.ofHom f ≫ π₂ := by
  rw [← cancel_mono e₂.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, reassoc_of% hπ₁, hπ₂,
    ← ModuleCat.ofHom_comp, Submodule.mapQ_mkQ]

end ModuleCat

namespace Submodule

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

/-- The canonical short complex `S → M → M / S`, with the inclusion and quotient maps. -/
abbrev quotientShortComplex (S : Submodule A M) : ShortComplex (ModuleCat.{v} A) :=
  ModuleCat.shortComplexOfCompEqZero S.subtype S.mkQ
    (LinearMap.exact_subtype_mkQ S).linearMap_comp_eq_zero

/-- The inclusion of a submodule and its quotient map form a short exact sequence. -/
theorem shortExact_quotientShortComplex (S : Submodule A M) :
    S.quotientShortComplex.ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ S)
    S.injective_subtype S.mkQ_surjective

end Submodule
