/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Radical morphisms as sums of composites of irreducible morphisms

A composite of irreducible morphisms between objects with local endomorphism rings
(`TauCeti.IsIrreducibleComposite`) is radical. Conversely, suppose the radical of a preadditive
category with binary biproducts is nilpotent and every object is a direct summand of a finite sum
of objects with local endomorphism rings. Then every radical morphism between two objects with local
endomorphism rings is a sum of such composites
(`TauCeti.mem_closure_isIrreducibleComposite_of_mem_jacobsonRadical`). Between objects with local
endomorphism rings (for example indecomposable modules of finite length) the radical morphisms are
the non-isomorphisms (`TauCeti.mem_jacobsonRadical_iff_not_isIso`), so every non-isomorphism between
such objects is a sum of composites of irreducible morphisms.

The proof shows by induction on `n` that every radical morphism agrees with a sum of composites of
irreducible morphisms modulo `radⁿ⁺¹`. A radical morphism outside `rad²` is irreducible
(`TauCeti.isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq`). One in
`rad²` factors through some object, which is split into objects with local endomorphism rings, and
the induction hypothesis applies to both factors.

This applies to the module category of a representation-finite algebra, where the radical is
nilpotent.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- `f` is a composite `f₁ ≫ ⋯ ≫ fₙ`, with `n ≥ 1`, of irreducible morphisms between objects with
local endomorphism rings: a path in the quiver of irreducible morphisms. -/
inductive IsIrreducibleComposite : ∀ {X Y : C}, (X ⟶ Y) → Prop
  /-- An irreducible morphism between objects with local endomorphism rings. -/
  | of {X Y : C} (hX : IsLocalRing (End X)) (hY : IsLocalRing (End Y)) {f : X ⟶ Y}
      (hf : IsIrreducibleMorphism f) : IsIrreducibleComposite f
  /-- A composite followed by one more irreducible morphism. -/
  | comp {X Y Z : C} (hZ : IsLocalRing (End Z)) {f : X ⟶ Y} {g : Y ⟶ Z}
      (hf : IsIrreducibleComposite f) (hg : IsIrreducibleMorphism g) :
      IsIrreducibleComposite (f ≫ g)

namespace IsIrreducibleComposite

/-- Composites of irreducible morphisms are closed under composition. -/
theorem comp' {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsIrreducibleComposite f)
    (hg : IsIrreducibleComposite g) : IsIrreducibleComposite (f ≫ g) := by
  induction hg with
  | of hY _ hg => exact .comp ‹_› hf hg
  | comp hW _ hg ih => simpa only [Category.assoc] using IsIrreducibleComposite.comp hW ih hg

/-- A composite of irreducible morphisms is radical. -/
theorem mem_jacobsonRadical {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleComposite f) :
    f ∈ jacobsonRadical X Y := by
  induction hf with
  | of _ _ hf => exact hf.mem_jacobsonRadical
  | comp _ _ _ ih => exact comp_mem_jacobsonRadical_right ih _

end IsIrreducibleComposite

/-- Sums of composites of irreducible morphisms are closed under composition. -/
theorem comp_mem_closure_isIrreducibleComposite {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ AddSubgroup.closure {f : X ⟶ Y | IsIrreducibleComposite f})
    (hg : g ∈ AddSubgroup.closure {g : Y ⟶ Z | IsIrreducibleComposite g}) :
    f ≫ g ∈ AddSubgroup.closure {h : X ⟶ Z | IsIrreducibleComposite h} := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    induction hg using AddSubgroup.closure_induction with
    | mem g hg => exact AddSubgroup.subset_closure (hf.comp' hg)
    | zero => simp
    | add g₁ g₂ _ _ h₁ h₂ => simpa only [Preadditive.comp_add] using add_mem h₁ h₂
    | neg g _ h => simpa only [Preadditive.comp_neg] using neg_mem h
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => simpa only [Preadditive.add_comp] using add_mem h₁ h₂
  | neg f _ h => simpa only [Preadditive.neg_comp] using neg_mem h

/-- Sums of composites of irreducible morphisms are radical. -/
theorem closure_isIrreducibleComposite_le_jacobsonRadical (X Y : C) :
    AddSubgroup.closure {f : X ⟶ Y | IsIrreducibleComposite f} ≤ jacobsonRadical X Y :=
  (AddSubgroup.closure_le _).mpr fun _ hf ↦ IsIrreducibleComposite.mem_jacobsonRadical hf

variable [Limits.HasBinaryBiproducts C]

/-- Under the hypotheses of `TauCeti.mem_closure_isIrreducibleComposite_of_mem_jacobsonRadical`,
every radical morphism between objects with local endomorphism rings agrees with a sum of
composites of irreducible morphisms modulo `radⁿ⁺¹`. -/
theorem exists_mem_closure_isIrreducibleComposite_sub_mem_pow
    (hC : ∀ Z : C, ∃ (n : ℕ) (W : Fin n → C) (a : ∀ j, Z ⟶ W j) (b : ∀ j, W j ⟶ Z),
      (∀ j, IsLocalRing (End (W j))) ∧ ∑ j, a j ≫ b j = 𝟙 Z) (n : ℕ) :
    ∀ {X Y : C} [IsLocalRing (End X)] [IsLocalRing (End Y)] {f : X ⟶ Y},
      f ∈ jacobsonRadical X Y → ∃ t ∈ AddSubgroup.closure {g : X ⟶ Y | IsIrreducibleComposite g},
        f - t ∈ (jacobsonRadicalIdeal C ^ (n + 1)).hom X Y := by
  induction n with
  | zero =>
    intro X Y _ _ f hf
    exact ⟨0, zero_mem _, by simpa using hf⟩
  | succ n ih =>
    intro X Y _ _ f hf
    by_cases hsq : f ∈ jacobsonRadicalSq X Y
    · -- Factor `f` through an object `Z` and split `Z` into objects with local endomorphism rings.
      obtain ⟨Z, g, h, hg, hh, rfl⟩ := mem_jacobsonRadicalSq_iff_exists_comp.mp hsq
      obtain ⟨m, W, a, b, hW, hab⟩ := hC Z
      have hgh : g ≫ h = ∑ j, (g ≫ a j) ≫ (b j ≫ h) := by
        have h' : g ≫ h = g ≫ (∑ j, a j ≫ b j) ≫ h := by rw [hab, Category.id_comp]
        simpa [Preadditive.sum_comp, Preadditive.comp_sum] using h'
      -- Approximate both factors at each summand.
      have key (j : Fin m) : ∃ t ∈ AddSubgroup.closure {g : X ⟶ Y | IsIrreducibleComposite g},
          (g ≫ a j) ≫ (b j ≫ h) - t ∈ (jacobsonRadicalIdeal C ^ (n + 2)).hom X Y := by
        have := hW j
        obtain ⟨t₁, ht₁, hr₁⟩ := ih (comp_mem_jacobsonRadical_right hg (a j))
        obtain ⟨t₂, ht₂, hr₂⟩ := ih (comp_mem_jacobsonRadical_left (b j) hh)
        refine ⟨t₁ ≫ t₂, comp_mem_closure_isIrreducibleComposite ht₁ ht₂, ?_⟩
        -- `(t₁ + r₁) ≫ (t₂ + r₂) - t₁ ≫ t₂ = t₁ ≫ r₂ + r₁ ≫ (b j ≫ h)`.
        have hdec : (g ≫ a j) ≫ (b j ≫ h) - t₁ ≫ t₂ =
            t₁ ≫ ((b j ≫ h) - t₂) + ((g ≫ a j) - t₁) ≫ (b j ≫ h) := by
          simp only [Preadditive.comp_sub, Preadditive.sub_comp]
          abel
        rw [hdec]
        refine add_mem ?_ ?_
        · rw [pow_succ]
          exact MorphismIdeal.comp_mem_mul
            (by simpa using closure_isIrreducibleComposite_le_jacobsonRadical X (W j) ht₁) hr₂
        · rw [pow_succ']
          exact MorphismIdeal.comp_mem_mul hr₁
            (by simpa using comp_mem_jacobsonRadical_left (b j) hh)
      choose t ht hr using key
      refine ⟨∑ j, t j, sum_mem fun j _ ↦ ht j, ?_⟩
      rw [hgh, ← Finset.sum_sub_distrib]
      exact sum_mem fun j _ ↦ hr j
    · -- A radical morphism outside `rad²` is irreducible.
      have hirr : IsIrreducibleMorphism f :=
        isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq.mpr ⟨hf, hsq⟩
      exact ⟨f, AddSubgroup.subset_closure (.of ‹_› ‹_› hirr), by simp⟩

/-- **Radical morphisms are sums of composites of irreducible morphisms.** Suppose the radical of
a preadditive category with binary biproducts is nilpotent, and every object is a direct summand of
a finite sum of objects with local endomorphism rings. Then every radical morphism between two
objects with local endomorphism rings is a sum of composites of irreducible morphisms between
objects with local endomorphism rings. -/
theorem mem_closure_isIrreducibleComposite_of_mem_jacobsonRadical
    (hC : ∀ Z : C, ∃ (n : ℕ) (W : Fin n → C) (a : ∀ j, Z ⟶ W j) (b : ∀ j, W j ⟶ Z),
      (∀ j, IsLocalRing (End (W j))) ∧ ∑ j, a j ≫ b j = 𝟙 Z)
    {N : ℕ} (hN : jacobsonRadicalIdeal C ^ N = ⊥) {X Y : C} [IsLocalRing (End X)]
    [IsLocalRing (End Y)] {f : X ⟶ Y} (hf : f ∈ jacobsonRadical X Y) :
    f ∈ AddSubgroup.closure {g : X ⟶ Y | IsIrreducibleComposite g} := by
  obtain ⟨t, ht, hr⟩ := exists_mem_closure_isIrreducibleComposite_sub_mem_pow hC N hf
  have hr : f - t ∈ (jacobsonRadicalIdeal C ^ N).hom X Y :=
    MorphismIdeal.le_def.mp (pow_le_pow_right_of_le_one' le_top N.le_succ) _ hr
  rw [hN, MorphismIdeal.mem_bot, sub_eq_zero] at hr
  exact hr ▸ ht

end TauCeti
