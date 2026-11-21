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
import TauCeti.CategoryTheory.Linear.Idempotent
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import Mathlib.RingTheory.Artinian.Module

/-!
# Decomposition into objects with local endomorphism rings

Let `C` be a linear category over a commutative Artinian ring `R` in which idempotents split, for
instance a Hom-finite idempotent-complete linear category over a field. Then every object `X` whose
endomorphisms are finitely generated over `R` is a direct summand of a finite sum of objects `W j`
with local endomorphism rings
(`TauCeti.exists_isLocalRing_end_sum_comp_eq_id`), in the form of morphisms `a j : X ⟶ W j` and
`b j : W j ⟶ X` with `∑ j, a j ≫ b j = 𝟙 X`. This is the existence half of the Krull-Schmidt
theorem for such a category; stating it with morphisms needs no biproducts.

The proof splits an idempotent `e` of `X` through an object `Y`. If `0` and `1` are the only
idempotents of `End Y`, then `End Y` is local by Fitting's lemma
(`TauCeti.isLocalRing_end_of_idempotent_eq_zero_or_id`). Otherwise a nontrivial idempotent of `Y`
writes `e` as the sum of two idempotents of `X` below `e`. Each of them has a strictly smaller
submodule of left multiples in the Artinian `R`-module `X ⟶ X`
(`TauCeti.range_leftComp_lt_range_leftComp`), so the splitting stops.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable (R : Type*) [CommRing R] [IsArtinianRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [IsIdempotentComplete C]

/-- An idempotent of `X` is a sum `∑ j, a j ≫ b j` through finitely many objects with local
endomorphism rings. -/
private theorem exists_isLocalRing_end_sum_comp_eq (X : C) [Module.Finite R (X ⟶ X)] (e : X ⟶ X)
    (he : e ≫ e = e) :
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
  -- `Y ⟶ Y` is a quotient of `X ⟶ X`, by `h ↦ i ≫ h ≫ r`.
  have : Module.Finite R (Y ⟶ Y) :=
    Module.Finite.of_surjective ((Linear.leftComp R Y i).comp (Linear.rightComp R X r))
      fun g ↦ ⟨r ≫ g ≫ i, by simp [reassoc_of% hir, hir]⟩
  by_cases hloc : ∀ u : Y ⟶ Y, u ≫ u = u → u = 0 ∨ u = 𝟙 Y
  · have := isLocalRing_end_of_idempotent_eq_zero_or_id (R := R) hY hloc
    exact ⟨PUnit, inferInstance, fun _ ↦ Y, fun _ ↦ r, fun _ ↦ i, fun _ ↦ this, by simpa using hri⟩
  push Not at hloc
  obtain ⟨u, hu, hu0, hu1⟩ := hloc
  have hu' : (𝟙 Y - u) ≫ (𝟙 Y - u) = 𝟙 Y - u := by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, hu]
  -- An idempotent `v ≠ 𝟙 Y` of `Y` gives an idempotent of `X` strictly below `e`.
  have hidem (v : Y ⟶ Y) (hv : v ≫ v = v) : (r ≫ v ≫ i) ≫ r ≫ v ≫ i = r ≫ v ≫ i := by
    simp [reassoc_of% hir, reassoc_of% hv]
  have hlt (v : Y ⟶ Y) (hv : v ≫ v = v) (hv1 : v ≠ 𝟙 Y) :
      LinearMap.range (Linear.leftComp R X (r ≫ v ≫ i)) <
        LinearMap.range (Linear.leftComp R X e) :=
    range_leftComp_lt_range_leftComp R (hidem v hv) (by simp [← hri, reassoc_of% hir])
      (by simp [← hri, reassoc_of% hir]) fun h ↦ hv1 (by
        simpa [reassoc_of% hir, hir, ← hri] using congrArg (fun φ ↦ i ≫ φ ≫ r) h)
  obtain ⟨ι, _, W, a, b, hW, hab⟩ := ih _ (hlt u hu hu1) _ (hidem u hu) rfl
  obtain ⟨κ, _, W', a', b', hW', hab'⟩ :=
    ih _ (hlt _ hu' fun h ↦ hu0 (sub_eq_self.mp h)) _ (hidem _ hu') rfl
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim W W', Sum.rec a a', Sum.rec b b', Sum.rec hW hW', ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hab, hab', ← hri]
  simp [Preadditive.sub_comp, Preadditive.comp_sub]

/-- **Every object is a direct summand of a finite sum of objects with local endomorphism rings**,
in an idempotent-complete linear category over a commutative Artinian ring `R`, when the
endomorphisms of the object are finitely generated over `R`. The summand is recorded by morphisms
`a j : X ⟶ W j` and `b j : W j ⟶ X` with `∑ j, a j ≫ b j = 𝟙 X`. -/
theorem exists_isLocalRing_end_sum_comp_eq_id (X : C) [Module.Finite R (X ⟶ X)] :
    ∃ (n : ℕ) (W : Fin n → C) (a : ∀ j, X ⟶ W j) (b : ∀ j, W j ⟶ X),
      (∀ j, IsLocalRing (End (W j))) ∧ ∑ j, a j ≫ b j = 𝟙 X := by
  obtain ⟨ι, _, W, a, b, hW, hab⟩ :=
    exists_isLocalRing_end_sum_comp_eq R X (𝟙 X) (Category.id_comp _)
  let σ := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, fun j ↦ W (σ j), fun j ↦ a (σ j), fun j ↦ b (σ j), fun j ↦ hW (σ j),
    (σ.sum_comp fun j ↦ a j ≫ b j).trans hab⟩

end TauCeti
