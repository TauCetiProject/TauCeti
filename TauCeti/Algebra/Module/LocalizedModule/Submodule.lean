/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Basic

/-!
# Submodules over a localization

This file proves two facts about submodules and localized modules:

* `IsLocalizedModule.mk'_mem_iff`: a fraction `f x / s` lies in a submodule over the localization
  exactly when `f x` does.
* `Submodule.localized'_one`: the localization of the image of `A` in an algebra `B` is the image
  of the localized base ring `A'` in the localized algebra `B'`.
-/

public section

/-- Let `A` be the localization of `R` at `S`, and `f : M → M'` a localization map at `S` into an
`A`-module. Then `f x / s` lies in an `A`-submodule `L` of `M'` exactly when `f x` does. -/
@[simp]
theorem IsLocalizedModule.mk'_mem_iff {R : Type*} [CommSemiring R] {S : Submonoid R}
    {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] [Module A M']
    [IsScalarTower R A M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] {L : Submodule A M'}
    {x : M} {s : S} : IsLocalizedModule.mk' f x s ∈ L ↔ f x ∈ L := by
  rw [← IsLocalization.smul_mem_iff (s := s), IsLocalizedModule.mk'_cancel']

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
