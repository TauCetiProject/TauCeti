/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Intermediate rings of a localization

Let `S` be a localization of `A` at a submonoid `M`, and let `B` be an intermediate `A`-algebra
whose map to `S` is injective, for instance an `A`-subalgebra of `S`. Then `S` is also the
localization of `B` at the image of `M`: inverting `M` in `B` changes nothing beyond `S`.
In particular, for the localization away from an element `a`, the induced map
`A_a → B_a` is bijective.

This applies to the affine charts `A[I/a] ⊆ A_a` of a blowup, which become `A_a` again after
inverting `a`.

## Main results

* `IsLocalization.isLocalization_algebraMapSubmonoid_of_injective`: `S` is the localization of
  `B` at the image of `M`.
* `IsLocalization.Away.bijective_awayMap_of_injective`: for `S` a localization away from `a`,
  the map `Localization.awayMap (algebraMap A B) a : A_a → B_a` is bijective.
-/

public section

namespace IsLocalization

variable {A B S : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring S] [Algebra A B]
  [Algebra B S] [Algebra A S] [IsScalarTower A B S]

/-- **An intermediate ring of a localization.** If `S` is a localization of `A` at `M` and the
map `B → S` from an intermediate `A`-algebra `B` is injective, then `S` is the localization of
`B` at the image of `M`. -/
theorem isLocalization_algebraMapSubmonoid_of_injective (M : Submonoid A) [IsLocalization M S]
    (h : Function.Injective (algebraMap B S)) :
    IsLocalization (Algebra.algebraMapSubmonoid B M) S where
  map_units := by
    rintro ⟨_, m, hm, rfl⟩
    simpa [← IsScalarTower.algebraMap_apply] using map_units S ⟨m, hm⟩
  surj z := by
    obtain ⟨⟨r, m⟩, hz⟩ := surj M z
    exact ⟨⟨algebraMap A B r, ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem m⟩⟩,
      by simpa [← IsScalarTower.algebraMap_apply] using hz⟩
  exists_of_eq hxy := ⟨1, by simpa using h hxy⟩

/-- **Inverting `a` in an intermediate ring of `A_a`.** If `S` is a localization of `A` away
from `a` and the map `B → S` from an intermediate `A`-algebra `B` is injective, then the induced
map `A_a → B_a` of localizations away from `a` is bijective. -/
theorem Away.bijective_awayMap_of_injective (a : A) [IsLocalization.Away a S]
    (h : Function.Injective (algebraMap B S)) :
    Function.Bijective (Localization.awayMap (algebraMap A B) a) := by
  have : IsLocalization.Away (algebraMap A B a) S := by
    simpa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      isLocalization_algebraMapSubmonoid_of_injective (Submonoid.powers a) h
  -- `A_a → B_a → S` is a map of localizations of `A` at `a`, and `B_a → S` is an isomorphism.
  let e₂ := algEquiv (Submonoid.powers (algebraMap A B a)) (Localization.Away (algebraMap A B a)) S
  have hbij := IsLocalization.bijective (Submonoid.powers a)
    ((e₂ : Localization.Away (algebraMap A B a) →+* S).comp
      (Localization.awayMap (algebraMap A B) a))
    (RingHom.ext fun r ↦ by
      simp [Localization.awayMap, Away.map, map_eq, IsScalarTower.algebraMap_apply A B S])
  exact (Function.Bijective.of_comp_iff' e₂.bijective _).mp hbij

end IsLocalization
