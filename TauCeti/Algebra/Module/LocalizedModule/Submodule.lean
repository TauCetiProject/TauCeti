/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Localizing the image of the base ring in an algebra

Let `B` be an algebra over a commutative semiring `A`, let `S` be a submonoid of `A`, and let
`A'` and `B'` be the localizations of `A` at `S` and of `B` at the image of `S`. Viewing `B → B'`
as a localization of `A`-modules, the localization `Submodule.localized'` of the image
`(1 : Submodule A B)` of `A` in `B` is the image `(1 : Submodule A' B')` of `A'` in `B'`. Together
with Mathlib's `IsLocalizedModule.toLocalizedQuotient'`, this exhibits `B' / A'` as the
localization of the `A`-module `B / A`.

## Main statements

* `Submodule.localized'_one`: the localization of the image of `A` in `B` is the image of `A'`
  in `B'`.
-/

public section

namespace Submodule

variable {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B] (S : Submonoid A)
  (A' B' : Type*) [CommSemiring A'] [CommSemiring B'] [Algebra A A'] [IsLocalization S A']
  [Algebra B B'] [IsLocalization (Algebra.algebraMapSubmonoid B S) B'] [Algebra A' B']
  [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- The localization of the image `(1 : Submodule A B)` of `A` in `B` is the image of `A'` in
`B'`, where `A'` and `B'` are the localizations of `A` at `S` and of `B` at the image of `S`. -/
@[simp]
theorem localized'_one :
    (1 : Submodule A B).localized' A' S (IsScalarTower.toAlgHom A B B').toLinearMap =
      (1 : Submodule A' B') := by
  rw [localized'_eq_span]
  refine le_antisymm (span_le.mpr ?_) ?_
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := mem_one.mp hb
    rw [AlgHom.toLinearMap_apply, AlgHom.commutes, IsScalarTower.algebraMap_apply A A' B']
    exact mem_one.mpr ⟨_, rfl⟩
  · rw [one_eq_span, span_le, Set.singleton_subset_iff]
    exact subset_span ⟨1, mem_one.mpr ⟨1, map_one _⟩, by simp⟩

end Submodule
