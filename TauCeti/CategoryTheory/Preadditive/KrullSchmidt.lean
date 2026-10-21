/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import Mathlib.RingTheory.Artinian.Module

/-!
# Decomposition into objects with local endomorphism rings

Let `C` be a linear category over a commutative Artinian ring `R` in which idempotents split and
the endomorphisms of every object are finitely generated over `R`, for instance a Hom-finite
idempotent-complete linear category over a field. Then every object `X` is a direct summand of a
finite sum of objects `W j` with local endomorphism rings
(`TauCeti.exists_isLocalRing_end_sum_comp_eq_id`), in the form of morphisms `a j : X ⟶ W j` and
`b j : W j ⟶ X` with `∑ j, a j ≫ b j = 𝟙 X`. This is the existence half of the Krull-Schmidt
theorem for such a category; stating it with morphisms needs no biproducts.

The proof splits an idempotent `e` of `X` through an object `Y`. If `0` and `1` are the only
idempotents of `End Y`, then `End Y` is local by Fitting's lemma
(`TauCeti.isLocalRing_end_of_idempotent_eq_zero_or_id`). Otherwise a nontrivial idempotent of `Y`
writes `e` as the sum of two idempotents of `X`. Each of them gives a strictly smaller submodule
`{e ≫ g}` of the `R`-module `X ⟶ X`, which is Artinian, so the splitting stops.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- Splitting the idempotent `e = r ≫ i` along an idempotent `v` of `Y` with `𝟙 Y - v ≠ 0` gives
the idempotent `r ≫ v ≫ i`, whose left multiples form a strictly smaller submodule. -/
private theorem range_leftComp_lt {X Y : C} {e : X ⟶ X} {i : Y ⟶ X} {r : X ⟶ Y}
    (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) {v : Y ⟶ Y} (hv : v ≫ v = v) (hv' : 𝟙 Y - v ≠ 0) :
    LinearMap.range (Linear.leftComp R X (r ≫ v ≫ i)) <
      LinearMap.range (Linear.leftComp R X e) := by
  refine lt_of_le_of_ne ?_ fun h ↦ hv' ?_
  · rintro _ ⟨g, rfl⟩
    exact ⟨r ≫ v ≫ i ≫ g, by simp [← hri, reassoc_of% hir]⟩
  · -- The complementary idempotent `r ≫ (𝟙 Y - v) ≫ i` is a left multiple of `e` but not of
    -- `r ≫ v ≫ i`.
    obtain ⟨g, hg⟩ : r ≫ (𝟙 Y - v) ≫ i ∈ LinearMap.range (Linear.leftComp R X (r ≫ v ≫ i)) :=
      h ▸ ⟨r ≫ (𝟙 Y - v) ≫ i, by simp [← hri, reassoc_of% hir]⟩
    have hs : 𝟙 Y - v = v ≫ i ≫ g ≫ r := by
      simpa [reassoc_of% hir, hir] using (congrArg (fun φ ↦ i ≫ φ ≫ r) hg).symm
    calc 𝟙 Y - v = (𝟙 Y - v) ≫ (𝟙 Y - v) := by simp [Preadditive.sub_comp, hv]
      _ = (𝟙 Y - v) ≫ v ≫ i ≫ g ≫ r := by rw [← hs]
      _ = 0 := by simp [Preadditive.sub_comp, reassoc_of% hv]

variable [IsArtinianRing R] [IsIdempotentComplete C] [∀ X : C, Module.Finite R (X ⟶ X)]

include R

/-- An idempotent of `X` is a sum `∑ j, a j ≫ b j` through finitely many objects with local
endomorphism rings. -/
private theorem exists_isLocalRing_end_sum_comp_eq (X : C) (e : X ⟶ X) (he : e ≫ e = e) :
    ∃ (ι : Type) (_ : Fintype ι) (W : ι → C) (a : ∀ j, X ⟶ W j) (b : ∀ j, W j ⟶ X),
      (∀ j, IsLocalRing (End (W j))) ∧ ∑ j, a j ≫ b j = e := by
  suffices H : ∀ S : Submodule R (X ⟶ X), ∀ e : X ⟶ X, e ≫ e = e →
      LinearMap.range (Linear.leftComp R X e) = S →
      ∃ (ι : Type) (_ : Fintype ι) (W : ι → C) (a : ∀ j, X ⟶ W j) (b : ∀ j, W j ⟶ X),
        (∀ j, IsLocalRing (End (W j))) ∧ ∑ j, a j ≫ b j = e from H _ e he rfl
  intro S
  induction S using WellFoundedLT.induction with
  | _ S ih =>
  rintro e he rfl
  by_cases he0 : e = 0
  · exact ⟨PEmpty, inferInstance, PEmpty.elim, fun j ↦ j.elim, fun j ↦ j.elim, fun j ↦ j.elim,
      by simp [he0]⟩
  obtain ⟨Y, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X e he
  have hY : ¬ IsZero Y := fun hY ↦ he0 (by rw [← hri, hY.eq_of_tgt r 0, zero_comp])
  by_cases hloc : ∀ u : Y ⟶ Y, u ≫ u = u → u = 0 ∨ u = 𝟙 Y
  · have := isLocalRing_end_of_idempotent_eq_zero_or_id (R := R) hY hloc
    exact ⟨PUnit, inferInstance, fun _ ↦ Y, fun _ ↦ r, fun _ ↦ i, fun _ ↦ this, by simpa using hri⟩
  push Not at hloc
  obtain ⟨u, hu, hu0, hu1⟩ := hloc
  have hu' : (𝟙 Y - u) ≫ (𝟙 Y - u) = 𝟙 Y - u := by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, hu]
  have hidem (v : Y ⟶ Y) (hv : v ≫ v = v) : (r ≫ v ≫ i) ≫ r ≫ v ≫ i = r ≫ v ≫ i := by
    simp [reassoc_of% hir, reassoc_of% hv]
  obtain ⟨ι, _, W, a, b, hW, hab⟩ := ih _ (range_leftComp_lt R hir hri hu
    (sub_ne_zero.mpr (Ne.symm hu1))) _ (hidem u hu) rfl
  obtain ⟨κ, _, W', a', b', hW', hab'⟩ := ih _ (range_leftComp_lt R hir hri hu'
    (by simpa using hu0)) _ (hidem _ hu') rfl
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim W W', Sum.rec a a', Sum.rec b b', Sum.rec hW hW', ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hab, hab', ← hri]
  simp [Preadditive.sub_comp, Preadditive.comp_sub]

/-- **Every object is a direct summand of a finite sum of objects with local endomorphism rings**,
in an idempotent-complete linear category over a commutative Artinian ring `R` in which the
endomorphisms of every object are finitely generated over `R`. The summand is recorded by morphisms
`a j : X ⟶ W j` and `b j : W j ⟶ X` with `∑ j, a j ≫ b j = 𝟙 X`. -/
theorem exists_isLocalRing_end_sum_comp_eq_id (X : C) :
    ∃ (n : ℕ) (W : Fin n → C) (a : ∀ j, X ⟶ W j) (b : ∀ j, W j ⟶ X),
      (∀ j, IsLocalRing (End (W j))) ∧ ∑ j, a j ≫ b j = 𝟙 X := by
  obtain ⟨ι, _, W, a, b, hW, hab⟩ :=
    exists_isLocalRing_end_sum_comp_eq R X (𝟙 X) (Category.id_comp _)
  let σ := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, fun j ↦ W (σ j), fun j ↦ a (σ j), fun j ↦ b (σ j), fun j ↦ hW (σ j),
    (σ.sum_comp fun j ↦ a j ≫ b j).trans hab⟩

end TauCeti
