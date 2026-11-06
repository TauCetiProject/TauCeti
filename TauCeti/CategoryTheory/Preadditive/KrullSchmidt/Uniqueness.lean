/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Logic.Equiv.Option
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Uniqueness of decompositions into objects with local endomorphism rings

In a preadditive category with finite biproducts, two decompositions `⨁ i, X i ≅ ⨁ j, Y j` of the
same object into objects with local endomorphism rings agree up to a bijection of the summands:
there is `σ : ι ≃ κ` with `X i ≅ Y (σ i)` for every `i`. This is the Krull-Remak-Schmidt-Azumaya
theorem in its categorical form. It needs no hypothesis on the category beyond finite biproducts;
in a Krull-Schmidt category it gives the uniqueness of the decomposition of every object.

The proof is the exchange argument. Write `⨁ X = X i₀ ⊞ X'`. The identity of `X i₀` is the sum over
`j` of its composites through `Y j`, and `End (X i₀)` is local, so one composite is invertible; then
`X i₀` is a retract of `Y j`, and since `End (Y j)` is local and so has no nontrivial idempotents,
`X i₀ ≅ Y j`. The summand `X i₀` of `⨁ Y` then has two complements, `X'` and the biproduct of the
`Y j'` with `j' ≠ j`, which are therefore isomorphic, and induction on the number of summands
finishes the proof.

## Main results

* `TauCeti.exists_equiv_iso_of_biproduct_iso_of_isLocalRing`: uniqueness of decompositions into
  objects with local endomorphism rings.

For finite-length modules the same statement, with indecomposable summands, is
`TauCeti.exists_equiv_iso_of_biproduct_iso` (and `TauCeti.exists_equiv_iso_of_iso_biproduct`),
proved there through external direct sums; indecomposable modules of finite length have local
endomorphism rings by Fitting's lemma.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Theorem 4.2 and Corollary 4.3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Two complements of the same summand are isomorphic: if `i₁ : A ⟶ Z` has the complements
`i₂ : A' ⟶ Z` and `j : B ⟶ Z`, in biproduct decompositions `Z = A ⊕ A'` and `Z = A ⊕ B`, then
`A' ≅ B`. -/
private def complementIso {Z A A' B : C} {i₁ : A ⟶ Z} {r₁ r₁' : Z ⟶ A} {i₂ : A' ⟶ Z}
    {r₂ : Z ⟶ A'} {j : B ⟶ Z} {s : Z ⟶ B} (hi₂ : i₂ ≫ r₂ = 𝟙 A') (h₁₂ : i₁ ≫ r₂ = 0)
    (htot : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 Z) (hj : j ≫ s = 𝟙 B) (h₁s : i₁ ≫ s = 0)
    (htot' : r₁' ≫ i₁ + s ≫ j = 𝟙 Z) : A' ≅ B where
  hom := i₂ ≫ s
  inv := j ≫ r₂
  hom_inv_id := by
    have h : s ≫ j = 𝟙 Z - r₁' ≫ i₁ := by rw [← htot']; abel
    simp only [Category.assoc]
    rw [← Category.assoc s, h, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
      Category.assoc, h₁₂, comp_zero, comp_zero, sub_zero, hi₂]
  inv_hom_id := by
    have h : r₂ ≫ i₂ = 𝟙 Z - r₁ ≫ i₁ := by rw [← htot]; abel
    simp only [Category.assoc]
    rw [← Category.assoc r₂, h, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
      Category.assoc, h₁s, comp_zero, comp_zero, sub_zero, hj]

/-- Replacing a summand: in a decomposition `Z = P ⊕ Y'`, given by `ι₀, π₀, J, T`, a map
`f : A ⟶ Z` whose composite with `π₀` is invertible is the inclusion of a summand with the same
complement `Y'`, with projection `T - π₀ ≫ inv (f ≫ π₀) ≫ f ≫ T` onto `Y'`. -/
private theorem replace_summand {Z P Y' A : C} {ι₀ : P ⟶ Z} {π₀ : Z ⟶ P} {J : Y' ⟶ Z}
    {T : Z ⟶ Y'} (hJ : J ≫ T = 𝟙 Y') (hJπ : J ≫ π₀ = 0) (htot : π₀ ≫ ι₀ + T ≫ J = 𝟙 Z)
    (f : A ⟶ Z) [IsIso (f ≫ π₀)] :
    f ≫ (T - π₀ ≫ inv (f ≫ π₀) ≫ f ≫ T) = 0 ∧ J ≫ (T - π₀ ≫ inv (f ≫ π₀) ≫ f ≫ T) = 𝟙 Y' ∧
      (π₀ ≫ inv (f ≫ π₀)) ≫ f + (T - π₀ ≫ inv (f ≫ π₀) ≫ f ≫ T) ≫ J = 𝟙 Z := by
  refine ⟨by rw [Preadditive.comp_sub, ← Category.assoc f π₀, IsIso.hom_inv_id_assoc, sub_self],
    by simp [hJ, reassoc_of% hJπ], ?_⟩
  have h : 𝟙 Z - T ≫ J = π₀ ≫ ι₀ := by rw [← htot]; abel
  have h' : π₀ ≫ inv (f ≫ π₀) ≫ f ≫ π₀ ≫ ι₀ = π₀ ≫ ι₀ := by
    rw [← Category.assoc f π₀ ι₀, IsIso.inv_hom_id_assoc]
  calc (π₀ ≫ inv (f ≫ π₀)) ≫ f + (T - π₀ ≫ inv (f ≫ π₀) ≫ f ≫ T) ≫ J
      = π₀ ≫ inv (f ≫ π₀) ≫ f ≫ (𝟙 Z - T ≫ J) + T ≫ J := by
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id, Category.assoc]
        abel
    _ = 𝟙 Z := by rw [h, h', htot]

variable [HasFiniteBiproducts C]

/-- The biproduct decomposition `⨁ Y = Y j ⊕ ⨁_{j' ≠ j} Y j'`. -/
private theorem biproduct_total_subtype {κ : Type w} [Finite κ] (Y : κ → C)
    (j : κ) : biproduct.π Y j ≫ biproduct.ι Y j +
      biproduct.toSubtype Y (· ≠ j) ≫ biproduct.fromSubtype Y (· ≠ j) = 𝟙 (⨁ Y) := by
  classical
  ext a b
  by_cases hab : b = a
  · subst hab
    by_cases hb : b = j
    · subst hb
      simp
    · simp [biproduct.ι_π_ne_assoc _ hb, hb]
  · by_cases hb : b = j
    · subst hb
      simp [biproduct.ι_π_ne _ hab, biproduct.ι_π_ne_assoc _ hab]
    · simp [biproduct.ι_π_ne_assoc _ hb, biproduct.ι_π_ne_assoc _ hab, biproduct.ι_π_ne _ hab]

/-- **The exchange step.** If `⨁ Y = A ⊕ A'`, given by `i₁, r₁, i₂, r₂`, with `End A` and all
`End (Y j)` local, then `A ≅ Y j` for some `j`, and `A'` is isomorphic to the biproduct of the
other summands. -/
private theorem exchange {κ : Type w} [Finite κ] (Y : κ → C)
    (hY : ∀ j, IsLocalRing (End (Y j))) {A A' : C} [IsLocalRing (End A)] {i₁ : A ⟶ ⨁ Y}
    {r₁ : ⨁ Y ⟶ A} {i₂ : A' ⟶ ⨁ Y} {r₂ : ⨁ Y ⟶ A'} (hi₁ : i₁ ≫ r₁ = 𝟙 A)
    (hi₂ : i₂ ≫ r₂ = 𝟙 A') (h₁₂ : i₁ ≫ r₂ = 0) (htot : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 (⨁ Y)) :
    ∃ j, Nonempty (A ≅ Y j) ∧ Nonempty (A' ≅ ⨁ Subtype.restrict (· ≠ j) Y) := by
  classical
  have := Fintype.ofFinite κ
  -- The identity of `A` is the sum of its composites through the `Y j`; one is invertible.
  have hsum : ∑ j, End.of (i₁ ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ r₁) = 1 := by
    ext
    simp only [End.sum_asHom, End.one_asHom]
    have h : ∑ j, i₁ ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ r₁ =
        i₁ ≫ (∑ j, biproduct.π Y j ≫ biproduct.ι Y j) ≫ r₁ := by
      rw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    rw [h, biproduct.total, Category.id_comp, hi₁]
  obtain ⟨j, -, hj⟩ := IsLocalRing.exists_of_isUnit_sum (hsum ▸ isUnit_one : IsUnit (∑ j, _))
  have := hY j
  have hu : IsIso (i₁ ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ r₁) := (isUnit_iff_isIso _).1 hj
  -- `A` is a retract of `Y j`, and `End (Y j)` has no nontrivial idempotents.
  set a := i₁ ≫ biproduct.π Y j with ha
  set b := biproduct.ι Y j ≫ r₁ ≫ inv (i₁ ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ r₁) with hb
  have hab : a ≫ b = 𝟙 A := by
    have h := IsIso.hom_inv_id (i₁ ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ r₁)
    simpa only [ha, hb, Category.assoc] using h
  have hba : b ≫ a = 𝟙 (Y j) := by
    have hidem : IsIdempotentElem (End.of (b ≫ a)) := by
      ext
      simp [reassoc_of% hab]
    rcases IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing hidem with h0 | h1
    · have h : 𝟙 A = 0 := by
        have := congrArg (fun φ : End (Y j) ↦ a ≫ φ.asHom ≫ b) h0
        simpa [reassoc_of% hab, hab] using this
      exact absurd (End.ext h.symm) (zero_ne_one (α := End A))
    · simpa using congrArg End.asHom h1
  refine ⟨j, ⟨⟨a, b, hab, hba⟩⟩, ⟨?_⟩⟩
  -- `i₁` is a summand with complements `A'` and `⨁_{j' ≠ j} Y j'`.
  have : IsIso (i₁ ≫ biproduct.π Y j) := ⟨⟨b, hab, hba⟩⟩
  obtain ⟨h₁s, hJ, htot'⟩ := replace_summand (ι₀ := biproduct.ι Y j)
    (biproduct.fromSubtype_toSubtype Y (· ≠ j)) (by ext; simp [biproduct.fromSubtype_π])
    (biproduct_total_subtype Y j) i₁
  exact complementIso hi₂ h₁₂ htot hJ h₁s htot'

/-- The biproduct decomposition `⨁ X = X i₀ ⊕ ⨁_{i ≠ i₀} X i`, transported along `e : ⨁ X ≅ Z`. -/
private theorem biproduct_decomposition_iso {ι : Type w} [Finite ι] (X : ι → C)
    (i₀ : ι) {Z : C} (e : ⨁ X ≅ Z) :
    (biproduct.ι X i₀ ≫ e.hom) ≫ e.inv ≫ biproduct.π X i₀ = 𝟙 _ ∧
      (biproduct.fromSubtype X (· ≠ i₀) ≫ e.hom) ≫ e.inv ≫ biproduct.toSubtype X (· ≠ i₀) = 𝟙 _ ∧
      (biproduct.ι X i₀ ≫ e.hom) ≫ e.inv ≫ biproduct.toSubtype X (· ≠ i₀) = 0 ∧
      (e.inv ≫ biproduct.π X i₀) ≫ biproduct.ι X i₀ ≫ e.hom +
        (e.inv ≫ biproduct.toSubtype X (· ≠ i₀)) ≫ biproduct.fromSubtype X (· ≠ i₀) ≫ e.hom =
          𝟙 Z := by
  classical
  refine ⟨by simp, by simp [biproduct.fromSubtype_toSubtype], by ext; simp [biproduct.ι_toSubtype],
    ?_⟩
  have h := biproduct_total_subtype X i₀
  simp only [Category.assoc]
  rw [← Preadditive.comp_add, ← Category.assoc (biproduct.π X i₀),
    ← Category.assoc (biproduct.toSubtype X _), ← Preadditive.add_comp, h]
  simp

/-- A biproduct over an empty index type is zero. -/
private theorem isZero_biproduct_of_isEmpty {ι : Type w} [IsEmpty ι] (X : ι → C) :
    IsZero (⨁ X) :=
  (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i ↦ isEmptyElim i)

private theorem exists_equiv_iso_aux (n : ℕ) : ∀ {ι : Type w} {κ : Type w'} [Fintype ι]
    [Finite κ] (X : ι → C) (Y : κ → C), Fintype.card ι = n → (∀ i, IsLocalRing (End (X i))) →
    (∀ j, IsLocalRing (End (Y j))) → (⨁ X ≅ ⨁ Y) → ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≅ Y (σ i)) := by
  classical
  induction n with
  | zero =>
    intro ι κ _ _ X Y hn _ hY e
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    -- Every `Y j` is a retract of the zero object `⨁ X`, and is nonzero.
    have : IsEmpty κ := ⟨fun j ↦ by
      have := hY j
      have hz := (isZero_biproduct_of_isEmpty X).of_iso e.symm
      have h : 𝟙 (Y j) = 0 := by
        rw [← biproduct.ι_π_self Y j, hz.eq_of_tgt (biproduct.ι Y j) 0, zero_comp]
      exact zero_ne_one (α := End (Y j)) (End.ext h.symm)⟩
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i ↦ isEmptyElim i⟩
  | succ n ih =>
    intro ι κ _ _ X Y hn hX hY e
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by lia)
    have := hX i₀
    obtain ⟨hi₁, hi₂, h₁₂, htot⟩ := biproduct_decomposition_iso X i₀ e
    obtain ⟨j₀, ⟨φ₀⟩, ⟨φ'⟩⟩ := exchange Y hY hi₁ hi₂ h₁₂ htot
    obtain ⟨σ', hσ'⟩ := ih (Subtype.restrict (· ≠ i₀) X) (Subtype.restrict (· ≠ j₀) Y)
      (by simp [Fintype.card_subtype_compl, hn]) (fun i ↦ hX i.1) (fun j ↦ hY j.1) φ'
    refine ⟨(Equiv.optionSubtypeNe i₀).symm.trans ((Equiv.optionCongr σ').trans
      (Equiv.optionSubtypeNe j₀)), fun i ↦ ?_⟩
    by_cases hi : i = i₀
    · subst hi
      simpa [Equiv.optionSubtypeNe_symm_self] using ⟨φ₀⟩
    · simpa [Equiv.optionSubtypeNe_symm_of_ne hi] using hσ' ⟨i, hi⟩

/-- **Uniqueness of decompositions into objects with local endomorphism rings**: two
decompositions `⨁ X ≅ ⨁ Y` of the same object into objects with local endomorphism rings match up
to a bijection of the summands. No hypothesis on the category beyond finite biproducts is needed;
in a Krull-Schmidt category this is the uniqueness of the decomposition of every object. -/
theorem exists_equiv_iso_of_biproduct_iso_of_isLocalRing {ι : Type w} {κ : Type w'} [Finite ι]
    [Finite κ]
    (X : ι → C) (Y : κ → C) (hX : ∀ i, IsLocalRing (End (X i)))
    (hY : ∀ j, IsLocalRing (End (Y j))) (e : ⨁ X ≅ ⨁ Y) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≅ Y (σ i)) := by
  have := Fintype.ofFinite ι
  exact exists_equiv_iso_aux _ X Y rfl hX hY e

end TauCeti
