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

* `TauCeti.res_trivial`: restriction of a trivial representation is trivial on the nose.
* `TopRep.full_res`: restriction along a surjective monoid homomorphism is full; it is always
  faithful.
-/

public section

namespace TauCeti

universe u v w t

variable (R : Type u) [Ring R] [TopologicalSpace R] (G : Type v) [Monoid G]
  (M : Type w) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul R M]

/-- Restriction of a trivial representation along a monoid homomorphism is the corresponding
trivial representation of the source monoid, on the nose.

For groups, `TopRep.res` is a reducible abbreviation for the left-hand side, so this lemma also
proves the corresponding equality stated with `TopRep.res` verbatim. -/
@[simp]
lemma res_trivial {H : Type*} [Monoid H] (f : H →* G) :
    TopRep.of ((ContRepresentation.trivial R G M).restrict f) =
      TopRep.of (ContRepresentation.trivial R H M) := (rfl)

end TauCeti

namespace TopRep

open CategoryTheory

variable {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {H : Type t} [Monoid H]

/-- Restriction along a monoid homomorphism is faithful: it leaves the underlying continuous
linear maps unchanged. -/
instance (φ : H →* G) : (resFunctor.{u, v, t, w} (k := k) φ).Faithful where
  map_injective {_ _} f g h := by
    ext a
    exact congr(($h).hom a)

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
