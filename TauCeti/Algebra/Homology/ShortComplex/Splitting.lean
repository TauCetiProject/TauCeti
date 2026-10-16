/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Factoring through a splitting

For a split short complex `X₁ ⟶ X₂ ⟶ X₃` with retraction `r` and section `s`, a morphism out of
`X₂` which vanishes on `X₁` factors through the projection `g` via the section `s`, and dually a
morphism into `X₂` which vanishes after `g` factors through the inclusion `f` via the retraction
`r`. Both are immediate from the identity `r ≫ f + g ≫ s = 𝟙`.

## Main results

* `CategoryTheory.ShortComplex.Splitting.g_s_comp_eq_of_f_comp_eq_zero`: if `S.f ≫ k = 0`, then
  `S.g ≫ s.s ≫ k = k`.
* `CategoryTheory.ShortComplex.Splitting.comp_r_f_eq_of_comp_g_eq_zero`: if `k ≫ S.g = 0`, then
  `k ≫ s.r ≫ S.f = k`.
* `CategoryTheory.ShortComplex.Splitting.comp_s_hom_comp_g_hom_of_comp_f_hom_eq_zero`: the first
  statement for linear maps out of a split short complex of modules into an arbitrary module.

## Implementation notes

The module version is stated for linear maps rather than as an instance of the categorical one
because its target module may live in any universe, for instance the ring itself when the modules
of the short complex live in a different universe.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex.Splitting

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {S : ShortComplex C}

/-- A morphism out of the middle term of a split short complex which vanishes on the first term
factors through the projection via the section. -/
theorem g_s_comp_eq_of_f_comp_eq_zero (s : S.Splitting) {Y : C} (k : S.X₂ ⟶ Y)
    (hk : S.f ≫ k = 0) : S.g ≫ s.s ≫ k = k := by
  rw [s.g_s_assoc, Preadditive.sub_comp, Category.id_comp, Category.assoc, hk, comp_zero,
    sub_zero]

/-- A morphism into the middle term of a split short complex which vanishes after the projection
factors through the inclusion via the retraction. -/
theorem comp_r_f_eq_of_comp_g_eq_zero (s : S.Splitting) {Y : C} (k : Y ⟶ S.X₂)
    (hk : k ≫ S.g = 0) : k ≫ s.r ≫ S.f = k := by
  rw [s.r_f, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hk, zero_comp, sub_zero]

end Preadditive

section ModuleCat

variable {R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)} {M : Type*} [AddCommGroup M]
  [Module R M]

/-- A linear map out of the middle term of a split short complex of modules which vanishes on the
first term factors through the projection via the section. -/
theorem comp_s_hom_comp_g_hom_of_comp_f_hom_eq_zero (s : S.Splitting) (ρ : S.X₂ →ₗ[R] M)
    (hρ : ρ ∘ₗ S.f.hom = 0) : (ρ ∘ₗ s.s.hom) ∘ₗ S.g.hom = ρ := by
  rw [LinearMap.comp_assoc, ← ModuleCat.hom_comp, s.g_s, ModuleCat.hom_sub, ModuleCat.hom_id,
    ModuleCat.hom_comp, LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, hρ,
    LinearMap.zero_comp, sub_zero]

end ModuleCat

end CategoryTheory.ShortComplex.Splitting
