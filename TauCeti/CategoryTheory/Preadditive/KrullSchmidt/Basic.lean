/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.CategoryTheory.Preadditive.Endomorphism
import TauCeti.CategoryTheory.Idempotents.Split
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Krull-Schmidt categories

A preadditive category with finite biproducts is **Krull-Schmidt** when every object is isomorphic
to a finite biproduct of objects with local endomorphism rings.

## Main definitions

* `TauCeti.IsKrullSchmidt`: Krull-Schmidt categories.

## Main results

* `TauCeti.isIdempotentComplete_of_isKrullSchmidt`: a Krull-Schmidt category is idempotent
  complete.
* `TauCeti.IsKrullSchmidt.indecomposable_iff_isLocalRing_end`: in a Krull-Schmidt category, an
  object is indecomposable exactly when its endomorphism ring is local.
* `CategoryTheory.Equivalence.isKrullSchmidt`: the Krull-Schmidt property is invariant under
  equivalence of categories.

## Implementation notes

Idempotent completeness is proved by peeling off one summand at a time. Let `e` be an idempotent
of `X = P ⊞ X'` with `End P` local. The component `c` of `e` on `P` is invertible, or `1 - c` is.
In the first case `ι_P ≫ e` exhibits `P` as a summand of the image of `e`, split off by an
idempotent `q` below `e`; in the second, `ι_P ≫ (1 - e)` exhibits `P` inside the image of `1 - e`.
Either way the idempotent that remains, `e - q` or `e`, kills a copy of `P` whose projection to `P`
is invertible. Replacing `P` by that copy gives a new decomposition `X = P ⊞ X'` in which the
remaining idempotent is carried by `X'`, where it splits by induction on the number of summands.

`TauCeti.exists_isLocalRing_end_sum_comp_eq_id`, in
`TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Decomposition`, provides decompositions into
objects with local endomorphism rings in Hom-finite idempotent-complete linear categories over a
commutative Artinian ring.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Section 4.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Split

/-- An idempotent `e` of `X` *splits* when `e = r ≫ i` for a retraction `r : X ⟶ Y` of a section
`i : Y ⟶ X`, that is with `i ≫ r = 𝟙 Y`. -/
private def Splits {X : C} (e : X ⟶ X) : Prop :=
  ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e

/-- **The splitting step.** Let `X = P ⊞ X'` be a biproduct decomposition, given by `i₀, r₀, j, s`,
in which every idempotent of `X'` splits. If an idempotent `g` of `X` kills a map `α : P ⟶ X` whose
composite with the projection to `P` is invertible, then `g` splits. -/
private theorem splits_of_comp_eq_zero {X P X' : C} {i₀ : P ⟶ X} {r₀ : X ⟶ P} {j : X' ⟶ X}
    {s : X ⟶ X'} (hj : j ≫ s = 𝟙 X') (hjr : j ≫ r₀ = 0)
    (htot : r₀ ≫ i₀ + s ≫ j = 𝟙 X) (hX' : ∀ d : X' ⟶ X', d ≫ d = d → Splits d)
    {α : P ⟶ X} [IsIso (α ≫ r₀)] {g : X ⟶ X} (hg : g ≫ g = g) (hαg : α ≫ g = 0) :
    Splits g := by
  -- A new projection `s'` onto `X'`, vanishing on `α`, gives the decomposition `X = α(P) ⊞ X'`.
  set s' := s - r₀ ≫ inv (α ≫ r₀) ≫ α ≫ s with hs'
  have hjs' : j ≫ s' = 𝟙 X' := by
    rw [hs', Preadditive.comp_sub, hj, reassoc_of% hjr, zero_comp, sub_zero]
  have htot' : r₀ ≫ inv (α ≫ r₀) ≫ α + s' ≫ j = 𝟙 X := by
    have h : 𝟙 X - s ≫ j = r₀ ≫ i₀ := by rw [← htot]; abel
    have h' : r₀ ≫ inv (α ≫ r₀) ≫ α ≫ r₀ ≫ i₀ = r₀ ≫ i₀ := by
      rw [← Category.assoc α r₀ i₀, IsIso.inv_hom_id_assoc]
    calc r₀ ≫ inv (α ≫ r₀) ≫ α + s' ≫ j
        = r₀ ≫ inv (α ≫ r₀) ≫ α ≫ (𝟙 X - s ≫ j) + s ≫ j := by
          simp only [hs', Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id,
            Category.assoc]
          abel
      _ = 𝟙 X := by rw [h, h', htot]
  -- `g` vanishes on `α(P)`, so it is carried by `X'`.
  have hg' : g = s' ≫ j ≫ g := by
    conv_lhs => rw [← Category.id_comp g, ← htot']
    simp only [Preadditive.add_comp, Category.assoc, hαg, comp_zero, zero_add]
  set h := j ≫ g with hhdef
  have hh : h ≫ s' ≫ h = h := by
    calc (j ≫ g) ≫ s' ≫ (j ≫ g) = j ≫ (g ≫ (s' ≫ j ≫ g)) := by simp only [Category.assoc]
      _ = j ≫ g := by rw [← hg', hg]
  obtain ⟨W, i, r, hir, hri⟩ := hX' (h ≫ s') (by simp [reassoc_of% hh])
  refine ⟨W, i ≫ h, s' ≫ r, ?_, ?_⟩
  · calc (i ≫ h) ≫ s' ≫ r = i ≫ (r ≫ i) ≫ r := by simp [hri]
      _ = 𝟙 W := by simp [hir]
  · calc (s' ≫ r) ≫ i ≫ h = s' ≫ h ≫ s' ≫ h := by simp [reassoc_of% hri]
      _ = g := by rw [hh, ← hg']

/-- **Peeling off a summand with local endomorphism ring.** Let `X = P ⊞ X'` with `End P` local, and
suppose every idempotent of `X'` splits. Then every idempotent of `X` splits. -/
private theorem splits_of_isLocalRing [HasBinaryBiproducts C] {X P X' : C} {i₀ : P ⟶ X}
    {r₀ : X ⟶ P} {j : X' ⟶ X} {s : X ⟶ X'} (hi₀ : i₀ ≫ r₀ = 𝟙 P) (hj : j ≫ s = 𝟙 X')
    (hjr : j ≫ r₀ = 0) (htot : r₀ ≫ i₀ + s ≫ j = 𝟙 X) [IsLocalRing (End P)]
    (hX' : ∀ d : X' ⟶ X', d ≫ d = d → Splits d) {e : X ⟶ X} (he : e ≫ e = e) : Splits e := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (End.of (i₀ ≫ e ≫ r₀)) with hc | hc
  · -- `P` is a summand of the image of `e`, split off by `q = β ≫ α`.
    have : IsIso (i₀ ≫ e ≫ r₀) := (isUnit_iff_isIso _).1 hc
    set α := i₀ ≫ e with hα
    set β := e ≫ r₀ ≫ inv (i₀ ≫ e ≫ r₀) with hβ
    have : IsIso (α ≫ r₀) := by simpa [hα] using this
    have hinv : i₀ ≫ e ≫ r₀ ≫ inv (i₀ ≫ e ≫ r₀) = 𝟙 P := by
      have h := IsIso.hom_inv_id (i₀ ≫ e ≫ r₀)
      rwa [Category.assoc, Category.assoc] at h
    have hαβ : α ≫ β = 𝟙 P := by simp [hα, hβ, reassoc_of% he, hinv]
    have hαe : α ≫ e = α := by simp [hα, he]
    have heβ : e ≫ β = β := by simp [hβ, reassoc_of% he]
    have hq : Splits (β ≫ α) := ⟨P, α, β, hαβ, rfl⟩
    have hg : (e - β ≫ α) ≫ (e - β ≫ α) = e - β ≫ α := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, he, Category.assoc, hαe,
        reassoc_of% heβ, reassoc_of% hαβ]
      abel
    have hsplit := splits_of_comp_eq_zero hj hjr htot hX' hg (α := α)
      (by simp only [Preadditive.comp_sub, hαe, reassoc_of% hαβ, sub_self])
    simpa [Splits] using exists_split_add_of_comp_eq_zero hq hsplit
      (by simp only [Preadditive.comp_sub, Category.assoc, hαe, reassoc_of% hαβ, sub_self])
      (by simp only [Preadditive.sub_comp, Category.assoc, reassoc_of% heβ, reassoc_of% hαβ,
        sub_self])
  · -- `P` sits inside the image of `1 - e`, which `e` kills.
    have : IsIso ((i₀ ≫ (𝟙 X - e)) ≫ r₀) := by
      refine (isUnit_iff_isIso (End.of _)).1 ?_
      convert hc using 1
      ext
      simp [hi₀]
    exact splits_of_comp_eq_zero hj hjr htot hX' he (α := i₀ ≫ (𝟙 X - e)) (by simp [he])

variable [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- Every idempotent of a finite biproduct of objects with local endomorphism rings splits. -/
private theorem splits_of_biproduct (n : ℕ) : ∀ {ι : Type} [Fintype ι]
    (P : ι → C), Fintype.card ι = n → (∀ i, IsLocalRing (End (P i))) →
    ∀ e : ⨁ P ⟶ ⨁ P, e ≫ e = e → Splits e := by
  classical
  induction n with
  | zero =>
    intro ι _ P hn _ e _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    have hz : IsZero (⨁ P) :=
      (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i ↦ isEmptyElim i)
    exact ⟨⨁ P, 𝟙 _, 𝟙 _, by simp, hz.eq_of_src _ _⟩
  | succ n ih =>
    intro ι _ P hn hP e he
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by lia)
    have := hP i₀
    let p : ι → Prop := (· ≠ i₀)
    refine splits_of_isLocalRing (i₀ := biproduct.ι P i₀) (r₀ := biproduct.π P i₀)
      (j := biproduct.fromSubtype P p) (s := biproduct.toSubtype P p) (by simp)
      (biproduct.fromSubtype_toSubtype P p) ?_ ?_ (fun d hd ↦ ?_) he
    · ext; simp [biproduct.fromSubtype_π, p]
    · ext a b
      by_cases hab : b = a
      · subst hab
        by_cases hb : b = i₀
        · subst hb
          simp [p]
        · simp [biproduct.ι_π_ne_assoc _ hb, hb, p]
      · by_cases hb : b = i₀
        · subst hb
          simp [biproduct.ι_π_ne _ hab, biproduct.ι_π_ne_assoc _ hab, p]
        · simp [biproduct.ι_π_ne_assoc _ hb, biproduct.ι_π_ne_assoc _ hab, biproduct.ι_π_ne _ hab,
            p]
    · exact ih (Subtype.restrict p P) (by simp [Fintype.card_subtype_compl, hn, p])
        (fun i ↦ hP i.1) d hd

end Split

variable (C)

/-- **A Krull-Schmidt category**: every object is isomorphic to a finite biproduct of objects with
local endomorphism rings. -/
class IsKrullSchmidt [HasFiniteBiproducts C] : Prop where
  /-- Every object is isomorphic to a finite biproduct of objects with local endomorphism rings. -/
  exists_iso_biproduct (X : C) :
    ∃ (n : ℕ) (P : Fin n → C), (∀ i, IsLocalRing (End (P i))) ∧ Nonempty (X ≅ ⨁ P)

variable {C} [HasFiniteBiproducts C]

/-- **A Krull-Schmidt category is idempotent complete.** -/
instance isIdempotentComplete_of_isKrullSchmidt [IsKrullSchmidt C] : IsIdempotentComplete C where
  idempotents_split X p hp := by
    obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
    obtain ⟨Y, i, r, hir, hri⟩ := splits_of_biproduct n P (Fintype.card_fin n) hP
      (φ.inv ≫ p ≫ φ.hom) (by simp [reassoc_of% hp])
    refine ⟨Y, i ≫ φ.inv, φ.hom ≫ r, by simp [hir], ?_⟩
    simp [reassoc_of% hri]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- **In a Krull-Schmidt category, an object is indecomposable exactly when its endomorphism ring
is local.** The converse direction holds in any preadditive category with binary biproducts
(`TauCeti.indecomposable_of_isLocalRing_end`). -/
theorem IsKrullSchmidt.indecomposable_iff_isLocalRing_end [IsKrullSchmidt C] (X : C) :
    Indecomposable X ↔ IsLocalRing (End X) := by
  refine ⟨fun hX ↦ ?_, fun _ ↦ indecomposable_of_isLocalRing_end⟩
  obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
  -- Each summand gives a nonzero idempotent of `X`, which must be the identity.
  have he (i : Fin n) : φ.hom ≫ biproduct.π P i ≫ biproduct.ι P i ≫ φ.inv = 𝟙 X := by
    have := hP i
    refine (idempotent_eq_zero_or_id_of_indecomposable hX (by simp)).resolve_left fun h0 ↦ ?_
    have h1 : 𝟙 (P i) = 0 := by
      simpa using congrArg (fun f ↦ biproduct.ι P i ≫ φ.inv ≫ f ≫ φ.hom ≫ biproduct.π P i) h0
    exact zero_ne_one (α := End (P i)) (End.ext h1.symm)
  obtain ⟨i⟩ : Nonempty (Fin n) := by
    by_contra h
    have : IsEmpty (Fin n) := not_nonempty_iff.1 h
    exact hX.1 (((IsZero.iff_id_eq_zero _).2
      (biproduct.hom_ext' _ _ fun i ↦ isEmptyElim i)).of_iso φ)
  have := hP i
  let ψ : X ≅ P i := ⟨φ.hom ≫ biproduct.π P i, biproduct.ι P i ≫ φ.inv, by simpa using he i,
    by simp⟩
  have : Nontrivial (End X) := ψ.endRingEquiv.toEquiv.nontrivial
  exact IsLocalRing.of_surjective' ψ.symm.endRingEquiv.toRingHom ψ.symm.endRingEquiv.surjective

/-- **The Krull-Schmidt property is invariant under equivalence of categories.** -/
theorem _root_.CategoryTheory.Equivalence.isKrullSchmidt {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    [IsKrullSchmidt C] (e : C ≌ D) : IsKrullSchmidt D where
  exists_iso_biproduct Y := by
    have : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
    obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct (e.inverse.obj Y)
    refine ⟨n, fun i ↦ e.functor.obj (P i), fun i ↦ ?_,
      ⟨(e.counitIso.app Y).symm ≪≫ e.functor.mapIso φ ≪≫ e.functor.mapBiproduct P⟩⟩
    have := hP i
    have : Nontrivial (End (e.functor.obj (P i))) :=
      ⟨⟨0, 1, fun h ↦ zero_ne_one (α := End (P i)) (End.ext (e.functor.map_injective (by
        simpa using congrArg End.asHom h)))⟩⟩
    exact IsLocalRing.of_surjective' _ (e.functor.mapEndRingHom_surjective (P i))

end TauCeti
