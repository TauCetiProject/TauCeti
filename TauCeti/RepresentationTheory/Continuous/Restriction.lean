/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Restriction of continuous representations

This file records basic compatibility results between continuous representations and restriction
along monoid homomorphisms.

## Main results

* `ContRepresentation.restrict_trivial`: restriction of a trivial representation is trivial on
  the nose.
* `ContRepresentation.restrictOfEqId`: restricting along a monoid homomorphism that acts as the
  identity on elements is equivalent to the original representation via the identity map.
* `ContRepresentation.Equiv.symmRestrict`: inverting an equivalence `(π.restrict φ).Equiv σ` along a
  right inverse `ψ` of `φ`.
* `TopRep.full_res`: restriction along a surjective monoid homomorphism is full; it is always
  faithful and additive.
-/

public section

universe u v w t

namespace ContRepresentation

section Restrict

variable (R : Type u) [Ring R] (G : Type v) [Monoid G] (V : Type w) [AddCommGroup V] [Module R V]
  [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- Restriction of a trivial continuous representation along a monoid homomorphism is the trivial
continuous representation of the source monoid, on the nose.

Since `TopRep.res φ (TopRep.of ρ)` is reducibly `TopRep.of (ρ.restrict φ)`, applying `TopRep.of`
to this equality gives the corresponding equality of objects of `TopRep`. -/
@[simp]
lemma restrict_trivial {H : Type*} [Monoid H] (f : H →* G) :
    (trivial R G V).restrict f = trivial R H V := (rfl)

end Restrict

section Equiv

variable {R G H V W : Type*} [Ring R] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]

/-- Restricting a continuous representation `π` along an endomorphism `φ : G →* G` that acts as the
identity on elements yields a representation canonically equivalent to `π` via the identity
continuous linear equivalence. -/
def restrictOfEqId (π : ContRepresentation R G V) {φ : G →* G} (hφ : ∀ g, φ g = g) :
    (π.restrict φ).Equiv π :=
  Equiv.mk (ContinuousLinearEquiv.refl R V) fun g ↦ by
    ext v
    simp [hφ g]

/-- Evaluating `restrictOfEqId` acts as the identity on `V`. -/
@[simp]
theorem restrictOfEqId_apply (π : ContRepresentation R G V) {φ : G →* G} (hφ : ∀ g, φ g = g)
    (v : V) : π.restrictOfEqId hφ v = v :=
  (rfl)

/-- Given monoid homomorphisms `φ : H →* G` and `ψ : G →* H` with `φ (ψ g) = g` for all `g` (for
instance, a multiplicative equivalence and its inverse) and an equivalence of continuous
`H`-representations `e : (π.restrict φ).Equiv σ`, `e.symmRestrict ψ hφψ` is the inverse equivalence
`(σ.restrict ψ).Equiv π` of continuous `G`-representations. -/
def Equiv.symmRestrict {π : ContRepresentation R G V} {σ : ContRepresentation R H W}
    {φ : H →* G} (e : (π.restrict φ).Equiv σ) (ψ : G →* H) (hφψ : ∀ g, φ (ψ g) = g) :
    (σ.restrict ψ).Equiv π :=
  Equiv.mk e.symm.toContinuousLinearEquiv fun g ↦ by
    simpa [restrict_apply, hφψ g] using e.symm.isIntertwining (ψ g)

/-- Evaluating `Equiv.symmRestrict` applies `e.symm`. -/
@[simp]
theorem Equiv.symmRestrict_apply {π : ContRepresentation R G V} {σ : ContRepresentation R H W}
    {φ : H →* G} (e : (π.restrict φ).Equiv σ) (ψ : G →* H) (hφψ : ∀ g, φ (ψ g) = g) (w : W) :
    e.symmRestrict ψ hφψ w = e.symm w :=
  (rfl)

/-- The continuous linear equivalence underlying `Equiv.symmRestrict` is `e`'s inverse. -/
@[simp]
theorem Equiv.toContinuousLinearEquiv_symmRestrict {π : ContRepresentation R G V}
    {σ : ContRepresentation R H W} {φ : H →* G} (e : (π.restrict φ).Equiv σ) (ψ : G →* H)
    (hφψ : ∀ g, φ (ψ g) = g) :
    (e.symmRestrict ψ hφψ).toContinuousLinearEquiv = e.symm.toContinuousLinearEquiv :=
  (rfl)

end Equiv

end ContRepresentation

namespace TopRep

open CategoryTheory

variable {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {H : Type t} [Monoid H]

/-- Restriction along a monoid homomorphism is faithful: it leaves the underlying continuous
linear maps unchanged. -/
instance (φ : H →* G) : (resFunctor.{u, v, t, w} (k := k) φ).Faithful where
  map_injective {_ _} f g h := by
    ext a
    exact congr(($h).hom a)

/-- Restriction along a monoid homomorphism is additive: it leaves the underlying continuous
linear maps unchanged. In particular it maps cochain complexes to cochain complexes. -/
instance (φ : H →* G) : (resFunctor.{u, v, t, w} (k := k) φ).Additive where
  map_add {_ _} _ _ := rfl

/-- Restriction along a surjective monoid homomorphism is full: a continuous linear map
intertwining the restricted actions intertwines the original ones. This is the continuous form of
`Rep.full_res`. -/
lemma full_res {φ : H →* G} (hφ : Function.Surjective φ) :
    (resFunctor.{u, v, t, w} (k := k) φ).Full where
  map_surjective {A B} f := by
    refine ⟨ConcreteCategory.ofHom (C := TopRep k G) ⟨f.hom.toContinuousLinearMap, fun g ↦ ?_⟩,
      by ext a; rfl⟩
    obtain ⟨h, rfl⟩ := hφ g
    exact f.hom.2 h

end TopRep
