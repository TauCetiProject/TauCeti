/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.AlmostSplit.Irreducible
import TauCeti.CategoryTheory.Preadditive.Indecomposable

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
complement, which needs idempotents to split.

## Main results

* `TauCeti.exists_isIso_biprod_desc_of_isSplitMono` and
  `TauCeti.exists_isIso_biprod_lift_of_isSplitEpi`: in an idempotent-complete preadditive category,
  a split monomorphism is a biproduct inclusion and a split epimorphism a biproduct projection.
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

section Complement

variable [HasBinaryBiproducts C] [IsIdempotentComplete C]

/-- **A split monomorphism is a biproduct inclusion** when idempotents split: for a split
monomorphism `s : X ⟶ Y` there is `i : X' ⟶ Y` with `(s, i) : X ⊞ X' ⟶ Y` invertible. -/
theorem exists_isIso_biprod_desc_of_isSplitMono {X Y : C} (s : X ⟶ Y) [IsSplitMono s] :
    ∃ (X' : C) (i : X' ⟶ Y), IsIso (biprod.desc s i) := by
  obtain ⟨X', i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split Y
    (𝟙 Y - retraction s ≫ s) (by simp [Preadditive.sub_comp, Preadditive.comp_sub])
  refine ⟨X', i, ?_⟩
  rw [← isoBiprodOfRetracts_inv (h₁ := IsSplitMono.id s) (h₂ := hir)
    (h := by rw [hri]; abel)]
  infer_instance

/-- **A split epimorphism is a biproduct projection** when idempotents split: for a split
epimorphism `p : Y ⟶ X` there is `q : Y ⟶ X'` with `(p, q) : Y ⟶ X ⊞ X'` invertible. -/
theorem exists_isIso_biprod_lift_of_isSplitEpi {X Y : C} (p : Y ⟶ X) [IsSplitEpi p] :
    ∃ (X' : C) (q : Y ⟶ X'), IsIso (biprod.lift p q) := by
  obtain ⟨X', i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split Y
    (𝟙 Y - p ≫ section_ p) (by simp [Preadditive.sub_comp, Preadditive.comp_sub])
  refine ⟨X', r, ?_⟩
  rw [← isoBiprodOfRetracts_hom (h₁ := IsSplitEpi.id p) (h₂ := hir)
    (h := by rw [hri]; abel)]
  infer_instance

end Complement

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
  refine ⟨X', i ≫ g, he ▸ hg.iso_comp _, fun u hu ↦ ?_⟩
  -- Right minimality is invariant under the isomorphism `biprod.desc s i`.
  rw [he] at hu
  have := hmin (inv (biprod.desc s i) ≫ u ≫ biprod.desc s i) (by simp [hu])
  have hu' : u = biprod.desc s i ≫ (inv (biprod.desc s i) ≫ u ≫ biprod.desc s i) ≫
      inv (biprod.desc s i) := by simp
  rw [hu']
  infer_instance

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
  refine ⟨X', f ≫ q, he ▸ hf.comp_iso _, fun u hu ↦ ?_⟩
  -- Left minimality is invariant under the isomorphism `biprod.lift p q`.
  rw [he, Category.assoc] at hu
  have := hmin (biprod.lift p q ≫ u ≫ inv (biprod.lift p q)) (by simp [reassoc_of% hu])
  have hu' : u = inv (biprod.lift p q) ≫ (biprod.lift p q ≫ u ≫ inv (biprod.lift p q)) ≫
      biprod.lift p q := by simp
  rw [hu']
  infer_instance

end Criterion

end TauCeti
