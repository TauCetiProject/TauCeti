/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.AlmostSplit.Irreducible.Basic
import TauCeti.CategoryTheory.AlmostSplit.Minimal
import TauCeti.CategoryTheory.Idempotents.Split

/-!
# Irreducible morphisms as components of minimal almost split morphisms

Let `M` be the target of a right minimal right almost split morphism `g : Y ⟶ M`. A morphism
`h : X ⟶ M` with `X` nonzero is irreducible exactly when there is `h' : X' ⟶ M` such that
`(h, h') : X ⊞ X' ⟶ M` is right minimal right almost split. So the irreducible morphisms into `M`
are the components of the sink map of `M`. Dually, a morphism `h : M ⟶ X` out of the source of a
left minimal left almost split morphism, with `X` nonzero, is irreducible exactly when some
`(h, h') : M ⟶ X ⊞ X'` is left minimal left almost split.

The direction from the decomposition is the restriction of a right minimal right almost split
morphism to a nonzero retract of its source
(`TauCeti.IsRightAlmostSplit.isIrreducibleMorphism_comp_of_not_isZero`). The converse factors an
irreducible `h` through `g` by a split monomorphism
(`TauCeti.IsRightAlmostSplit.exists_isSplitMono_of_isIrreducibleMorphism`) and splits off its
complement (`TauCeti.exists_isIso_biprod_desc_of_isSplitMono`), which needs idempotents to split.

## Main results

* `TauCeti.IsRightAlmostSplit.isIrreducibleMorphism_iff_exists_biprod_desc` and
  `TauCeti.IsLeftAlmostSplit.isIrreducibleMorphism_iff_exists_biprod_lift`: the irreducibility
  criterion.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section V.5.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Criterion

variable [HasBinaryBiproducts C] [IsIdempotentComplete C]

/-- **The irreducibility criterion for morphisms into the target of a sink map.** If `M` is the
target of a right minimal right almost split morphism `g`, a morphism `h : X ⟶ M` with `X`
nonzero is irreducible exactly when `(h, h') : X ⊞ X' ⟶ M` is right minimal right almost split
for some `h' : X' ⟶ M`. -/
theorem IsRightAlmostSplit.isIrreducibleMorphism_iff_exists_biprod_desc {Y M : C} {g : Y ⟶ M}
    (hg : IsRightAlmostSplit g) (hmin : ∀ u : Y ⟶ Y, u ≫ g = g → IsIso u) {X : C}
    (hX : ¬ IsZero X) (h : X ⟶ M) :
    IsIrreducibleMorphism h ↔ ∃ (X' : C) (h' : X' ⟶ M), IsRightAlmostSplit (biprod.desc h h') ∧
      ∀ u : X ⊞ X' ⟶ X ⊞ X', u ≫ biprod.desc h h' = biprod.desc h h' → IsIso u := by
  refine ⟨fun hh ↦ ?_, fun ⟨X', h', hd, hdmin⟩ ↦ by
    simpa using hd.isIrreducibleMorphism_comp_of_not_isZero hdmin hX biprod.inl⟩
  -- Factor `h` through `g` by a split monomorphism, and split off its complement.
  obtain ⟨s, hs, rfl⟩ := hg.exists_isSplitMono_of_isIrreducibleMorphism hh
  obtain ⟨X', i, hi⟩ := exists_isIso_biprod_desc_of_isSplitMono s
  have he : biprod.desc (s ≫ g) (i ≫ g) = biprod.desc s i ≫ g := by ext <;> simp
  exact ⟨X', i ≫ g, he ▸ hg.iso_comp _, he ▸ right_minimal_iso_comp hmin (biprod.desc s i)⟩

/-- **The irreducibility criterion for morphisms out of the source of a source map.** If `M` is
the source of a left minimal left almost split morphism `f`, a morphism `h : M ⟶ X` with `X`
nonzero is irreducible exactly when `(h, h') : M ⟶ X ⊞ X'` is left minimal left almost split for
some `h' : M ⟶ X'`. -/
theorem IsLeftAlmostSplit.isIrreducibleMorphism_iff_exists_biprod_lift {M Y : C} {f : M ⟶ Y}
    (hf : IsLeftAlmostSplit f) (hmin : ∀ u : Y ⟶ Y, f ≫ u = f → IsIso u) {X : C}
    (hX : ¬ IsZero X) (h : M ⟶ X) :
    IsIrreducibleMorphism h ↔ ∃ (X' : C) (h' : M ⟶ X'), IsLeftAlmostSplit (biprod.lift h h') ∧
      ∀ u : X ⊞ X' ⟶ X ⊞ X', biprod.lift h h' ≫ u = biprod.lift h h' → IsIso u := by
  refine ⟨fun hh ↦ ?_, fun ⟨X', h', hd, hdmin⟩ ↦ by
    simpa using hd.isIrreducibleMorphism_comp_of_not_isZero hdmin hX biprod.fst⟩
  -- Factor `h` through `f` by a split epimorphism, and split off its complement.
  obtain ⟨p, hp, rfl⟩ := hf.exists_isSplitEpi_of_isIrreducibleMorphism hh
  obtain ⟨X', q, hq⟩ := exists_isIso_biprod_lift_of_isSplitEpi p
  have he : biprod.lift (f ≫ p) (f ≫ q) = f ≫ biprod.lift p q := by ext <;> simp
  exact ⟨X', f ≫ q, he ▸ hf.comp_iso _, he ▸ left_minimal_comp_iso hmin (biprod.lift p q)⟩

end Criterion

end TauCeti
