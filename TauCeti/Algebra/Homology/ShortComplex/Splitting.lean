/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Splittings and their canonical biproduct comparisons

For a split short complex `X₁ ⟶ X₂ ⟶ X₃` with retraction `r` and section `s`, a morphism out of
`X₂` which vanishes on `X₁` factors through the projection `g` via the section `s`, and dually a
morphism into `X₂` which vanishes after `g` factors through the inclusion `f` via the retraction
`r`. Both are immediate from the identity `r ≫ f + g ≫ s = 𝟙`.
The canonical biproduct comparison sends the inclusion `f` to `biprod.inl`, and its
composition with `biprod.snd` recovers the projection `g`.
For a split short complex of homological complexes, the homology of the outer terms is a retract
of that of the middle term, so the outer terms are exact wherever the middle term is.

## Main results

* `CategoryTheory.ShortComplex.Splitting.f_isoBinaryBiproduct_hom`: the inclusion under the
  canonical biproduct comparison.
* `CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct_hom_snd`: the projection under
  the canonical biproduct comparison.

* `CategoryTheory.ShortComplex.Splitting.g_s_comp_eq_of_f_comp_eq_zero`: if `S.f ≫ k = 0`, then
  `S.g ≫ s.s ≫ k = k`.
* `CategoryTheory.ShortComplex.Splitting.comp_r_f_eq_of_comp_g_eq_zero`: if `k ≫ S.g = 0`, then
  `k ≫ s.r ≫ S.f = k`.
* `CategoryTheory.ShortComplex.Splitting.comp_s_hom_comp_g_hom_of_comp_f_hom_eq_zero`: the first
  statement for linear maps out of a split short complex of modules into an arbitrary module.
* `CategoryTheory.ShortComplex.Splitting.acyclic_X₁` and
  `CategoryTheory.ShortComplex.Splitting.acyclic_X₃`: the outer terms of a split short complex of
  homological complexes are acyclic when the middle term is.

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


variable [HasBinaryBiproduct S.X₁ S.X₃]

-- Apply before isoBinaryBiproduct_hom rewrites the comparison into biprod.lift.

/-- The inclusion of a split short complex is the first biproduct inclusion under its
canonical comparison. -/
@[reassoc (attr := simp↓), simp↓]
theorem f_isoBinaryBiproduct_hom (s : S.Splitting) :
    S.f ≫ s.isoBinaryBiproduct.hom = biprod.inl := by
  apply biprod.hom_ext <;> simp [isoBinaryBiproduct]

/-- The projection of a split short complex is the second biproduct projection under its
canonical comparison. -/
@[reassoc (attr := simp↓), simp↓]
theorem isoBinaryBiproduct_hom_snd (s : S.Splitting) :
    s.isoBinaryBiproduct.hom ≫ biprod.snd = S.g := by
  simp [isoBinaryBiproduct]

end Preadditive

section HomologicalComplex

variable {C ι : Type*} [Category C] [Preadditive C] [CategoryWithHomology C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- In a split short complex of homological complexes, the first term is exact in every degree
where the middle term is, since its homology is a retract of that of the middle term. -/
theorem exactAt_X₁ (s : S.Splitting) {i : ι} (h : S.X₂.ExactAt i) : S.X₁.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id, ← s.f_r,
    HomologicalComplex.homologyMap_comp, h.eq_of_tgt (HomologicalComplex.homologyMap S.f i) 0,
    zero_comp]

/-- In a split short complex of homological complexes, the third term is exact in every degree
where the middle term is, since its homology is a retract of that of the middle term. -/
theorem exactAt_X₃ (s : S.Splitting) {i : ι} (h : S.X₂.ExactAt i) : S.X₃.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id, ← s.s_g,
    HomologicalComplex.homologyMap_comp, h.eq_of_tgt (HomologicalComplex.homologyMap s.s i) 0,
    zero_comp]

/-- The first term of a split short complex of homological complexes is acyclic when the middle
term is. -/
theorem acyclic_X₁ (s : S.Splitting) (h : S.X₂.Acyclic) : S.X₁.Acyclic :=
  fun i ↦ s.exactAt_X₁ (h i)

/-- The third term of a split short complex of homological complexes is acyclic when the middle
term is. -/
theorem acyclic_X₃ (s : S.Splitting) (h : S.X₂.Acyclic) : S.X₃.Acyclic :=
  fun i ↦ s.exactAt_X₃ (h i)

end HomologicalComplex

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
