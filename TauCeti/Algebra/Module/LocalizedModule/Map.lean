/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localizing a localization map

Let `f : M → M'` and `f₂ : N → N'` be localizations at a submonoid `S`. If a scalar `r` acts
invertibly on `M`, it acts invertibly on `M'`, because the action of `r` on `M'` is the map
induced by the action of `r` on `M`. Consequently, if `g : M → N` is a localization at a second
submonoid `T`, then so is the induced map `M' → N'`: localizations at `S` and at `T` commute. For
the module of sections of a quasi-coherent sheaf this says that restricting from `D(s)` to
`D(s t)` is a localization away from `t`.

## Main statements

* `IsLocalizedModule.isUnit_algebraMap_of_isUnit`: invertible scalars stay invertible on a
  localization.
* `IsLocalizedModule.isLocalizedModule_map`: the map induced on localizations at `S` by a
  localization at `T` is a localization at `T`.
-/

public section

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {T : Submonoid R}
  {M M' N N' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
  [Module R M] [Module R M'] [Module R N] [Module R N']
  (f : M →ₗ[R] M') [IsLocalizedModule S f]

include S f in
/-- A scalar acting invertibly on a module acts invertibly on each of its localizations. -/
theorem isUnit_algebraMap_of_isUnit {r : R} (h : IsUnit (algebraMap R (Module.End R M) r)) :
    IsUnit (algebraMap R (Module.End R M') r) := by
  have e : algebraMap R (Module.End R M') r = map S f f (algebraMap R (Module.End R M) r) := by
    simp [Module.algebraMap_end_eq_smul_id]
  rw [Module.End.isUnit_iff] at h ⊢
  rw [e]
  exact ⟨map_injective S f f _ h.1, map_surjective S f f _ h.2⟩

/-- Localizations at two submonoids commute: if `g : M → N` is a localization at `T`, then the
map induced by `g` between localizations at `S` is again a localization at `T`. -/
theorem isLocalizedModule_map (f₂ : N →ₗ[R] N') [IsLocalizedModule S f₂] (g : M →ₗ[R] N)
    [IsLocalizedModule T g] : IsLocalizedModule T (map S f f₂ g) where
  map_units t := isUnit_algebraMap_of_isUnit S f₂ (IsLocalizedModule.map_units g t)
  surj y := by
    obtain ⟨⟨n, s⟩, rfl⟩ := mk'_surjective S f₂ y
    obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj T g n
    refine ⟨⟨mk' f m s, t⟩, ?_⟩
    simp only [Function.uncurry_apply_pair, map_mk', ← ht, Submonoid.smul_def, mk'_smul]
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨⟨m₁, s₁⟩, rfl⟩ := mk'_surjective S f x₁
    obtain ⟨⟨m₂, s₂⟩, rfl⟩ := mk'_surjective S f x₂
    simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_mk'_iff, Submonoid.smul_def] at e
    obtain ⟨c, hc⟩ := e
    simp only [← map_smul] at hc
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) hc
    refine ⟨t, ?_⟩
    simp only [Function.uncurry_apply_pair, Submonoid.smul_def, ← mk'_smul, mk'_eq_mk'_iff]
    exact ⟨c, by simpa only [Submonoid.smul_def, smul_comm (t : R)] using ht⟩

end IsLocalizedModule
