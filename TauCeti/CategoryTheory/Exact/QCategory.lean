/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.HomotopyCategory
public import TauCeti.CategoryTheory.Exact.BaseChange
public import TauCeti.CategoryTheory.Exact.Split
public import Mathlib.CategoryTheory.Bicategory.Span.Basic
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Quillen's category `Q(E)` of an exact category

Let `E` be an exact structure on an additive category `C`. Quillen's category `Q(E)` has the
objects of `C`. A morphism `X ⟶ Y` of `Q(E)` is represented by a span `X ↞ M ↣ Y` whose left leg
is a deflation and whose right leg is an inflation, and two spans represent the same morphism
when an isomorphism of their middle objects commutes with both legs. The composite of
`X ↞ M ↣ Y` and `Y ↞ N ↣ Z` is `X ↞ M ×_Y N ↣ Z`: the projection `M ×_Y N ⟶ M` is a base change
of the deflation `N ↠ Y`, and the projection `M ×_Y N ⟶ N` is a base change of the inflation
`M ↣ Y` along that deflation, so both composite legs are again admissible.

We construct `Q(E)` as the homotopy category of Mathlib's bicategory of spans
`CategoryTheory.Span.SpanBicat C E.deflations E.inflations`, so that the category laws come from the
associators and unitors of that bicategory. The classifying space of `Q(E)` is the space whose
loop space is the algebraic K-theory of `E`.

## Main definitions

* `TauCeti.ExactStructure.QCategory E`: Quillen's category `Q(E)`.
* `TauCeti.ExactStructure.QCategory.homMk`: the morphism represented by an admissible span.
* `TauCeti.ExactStructure.QCategory.ofInflation`: the morphism `X ⟶ Y` attached to an inflation
  `X ↣ Y`.
* `TauCeti.ExactStructure.QCategory.ofDeflation`: the morphism `Y ⟶ X` attached to a deflation
  `X ↠ Y`, which reverses its direction.
* `TauCeti.ExactStructure.QCategory.ofIso`: the isomorphism of `Q(E)` attached to an isomorphism
  of `C`.
* `TauCeti.ExactStructure.QCategory.fromZeroEquiv`: morphisms `0 ⟶ Y` in `Q(E)` are the
  admissible subobjects of `Y`.

## Main statements

* `TauCeti.ExactStructure.QCategory.homMk_eq_homMk_iff`: two spans represent the same morphism
  exactly when their middle objects are isomorphic compatibly with both legs.
* `TauCeti.ExactStructure.QCategory.homMk_comp_homMk`: composition is computed by any pullback.
* `TauCeti.ExactStructure.QCategory.ofDeflation_comp_ofInflation`: every morphism factors as a
  reversed deflation followed by an inflation; by `homMk_eq_homMk_iff` the factorization is unique
  up to an isomorphism of the middle object compatible with both legs.
* `TauCeti.ExactStructure.QCategory.ofInflation_comp_ofDeflation`: an inflation followed by a
  reversed deflation is the reversed base-changed deflation followed by the base-changed
  inflation.
* `TauCeti.ExactStructure.QCategory.ofInflation_inj` and
  `TauCeti.ExactStructure.QCategory.ofDeflation_inj`: inflations and reversed deflations embed
  faithfully into `Q(E)`.
* `TauCeti.ExactStructure.QCategory.isIso_iff_exists_iso`: the isomorphisms of `Q(E)` are exactly
  those coming from isomorphisms of `C`.

## References

* Daniel Quillen, *Higher algebraic K-theory: I*, in *Algebraic K-theory I*, Lecture Notes in
  Mathematics **341** (1973), 85--147, §2.
* Charles A. Weibel, *The K-book: an introduction to algebraic K-theory*, Graduate Studies in
  Mathematics **145** (2013), Chapter IV, Definition 6.1 and §6.1.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Propositions 2.15 and 2.16.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

/-- **Quillen's category `Q(E)`** of an exact category. Its objects are those of `C`, and its
morphisms `X ⟶ Y` are the spans `X ↞ M ↣ Y` with a deflation on the left and an inflation on
the right, up to isomorphism of `M` compatible with both legs. It is the homotopy category of the
bicategory of such spans. -/
abbrev QCategory : Type u :=
  Bicategory.HomotopyCategory (Span.SpanBicat C E.deflations E.inflations)

namespace QCategory

variable {E}

/-- The object of `Q(E)` attached to an object of `C`. -/
abbrev mk (X : C) : E.QCategory :=
  ⟨⟨X⟩⟩

/-- The morphism `X ⟶ Y` of `Q(E)` represented by a span `X ↞ M ↣ Y` whose left leg is a
deflation and whose right leg is an inflation. -/
noncomputable def homMk {X Y M : C} (p : M ⟶ X) (i : M ⟶ Y) (hp : E.IsDeflation p)
    (hi : E.IsInflation i) : (mk X : E.QCategory) ⟶ mk Y :=
  Bicategory.HomotopyCategory.homMk (Span.SpanBicat.mkHom p i hp hi)

/-- Every morphism of `Q(E)` is represented by an admissible span. -/
theorem exists_eq_homMk {X Y : C} (f : (mk X : E.QCategory) ⟶ mk Y) :
    ∃ (M : C) (p : M ⟶ X) (i : M ⟶ Y) (hp : E.IsDeflation p) (hi : E.IsInflation i),
      f = homMk p i hp hi := by
  obtain ⟨S, rfl⟩ := Bicategory.HomotopyCategory.homMk_surjective f
  exact ⟨S.apex, S.l, S.r, S.wl, S.wr, rfl⟩

/-- Two admissible spans represent the same morphism of `Q(E)` exactly when an isomorphism of
their middle objects commutes with both legs. -/
theorem homMk_eq_homMk_iff {X Y M M' : C} {p : M ⟶ X} {i : M ⟶ Y} {p' : M' ⟶ X}
    {i' : M' ⟶ Y} (hp : E.IsDeflation p) (hi : E.IsInflation i) (hp' : E.IsDeflation p')
    (hi' : E.IsInflation i') :
    homMk p i hp hi = homMk p' i' hp' hi' ↔ ∃ e : M ≅ M', e.hom ≫ p' = p ∧ e.hom ≫ i' = i := by
  rw [homMk, homMk, Bicategory.HomotopyCategory.homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨Span.SpanBicat.apexIso e, e.hom.hom_l, e.hom.hom_r⟩
  · rintro ⟨e, hl, hr⟩
    exact ⟨Span.SpanBicat.mkIso₂ e hl hr⟩

/-- The identity of `Q(E)` is represented by the span of identities. -/
@[simp]
theorem homMk_id_id (X : C) :
    homMk (𝟙 X) (𝟙 X) (E.isDeflation_id X) (E.isInflation_id X) = 𝟙 (mk X : E.QCategory) :=
  Bicategory.HomotopyCategory.homMk_id _

/-- **Composition in `Q(E)`.** The composite of the spans `X ↞ M ↣ Y` and `Y ↞ N ↣ Z` is
`X ↞ P ↣ Z` for any pullback `P` of `M ↣ Y ↞ N`. -/
theorem homMk_comp_homMk {X Y Z M N P : C} {p : M ⟶ X} {i : M ⟶ Y} {q : N ⟶ Y} {j : N ⟶ Z}
    (hp : E.IsDeflation p) (hi : E.IsInflation i) (hq : E.IsDeflation q) (hj : E.IsInflation j)
    {c : P ⟶ N} {a : P ⟶ M} (sq : IsPullback c a q i) :
    homMk p i hp hi ≫ homMk q j hq hj =
      homMk (a ≫ p) (c ≫ j)
        (E.isDeflation_comp _ _ (E.isStableUnderBaseChange_deflations.of_isPullback sq hq) hp)
        (E.isInflation_comp _ _ (E.isInflation_of_isPullback sq.flip hi hq) hj) := by
  rw [homMk, homMk, ← Bicategory.HomotopyCategory.homMk_comp, homMk]
  refine Bicategory.HomotopyCategory.homMk_eq_homMk (Span.SpanBicat.mkIso₂
    ((IsPullback.of_isLimit (Span.SpanBicat.isLimitCompPullbackCone _ _)).isoIsPullback _ _
      sq.flip) ?_ ?_)
  · simp [Span.SpanBicat.comp_l]
  · simp [Span.SpanBicat.comp_r]

/-- The morphism `X ⟶ Y` of `Q(E)` attached to an inflation `i : X ↣ Y`, represented by the span
`X ↞ X ↣ Y`. -/
noncomputable def ofInflation {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i) :
    (mk X : E.QCategory) ⟶ mk Y :=
  homMk (𝟙 X) i (E.isDeflation_id X) hi

/-- The morphism `Y ⟶ X` of `Q(E)` attached to a deflation `p : X ↠ Y`, represented by the span
`Y ↞ X ↣ X`. It goes in the direction opposite to `p`. -/
noncomputable def ofDeflation {X Y : C} (p : X ⟶ Y) (hp : E.IsDeflation p) :
    (mk Y : E.QCategory) ⟶ mk X :=
  homMk p (𝟙 X) hp (E.isInflation_id X)

@[simp]
theorem ofInflation_id (X : C) : ofInflation (𝟙 X) (E.isInflation_id X) = 𝟙 (mk X) :=
  homMk_id_id X

@[simp]
theorem ofDeflation_id (X : C) : ofDeflation (𝟙 X) (E.isDeflation_id X) = 𝟙 (mk X) :=
  homMk_id_id X

/-- Distinct inflations give distinct morphisms of `Q(E)`. -/
theorem ofInflation_inj {X Y : C} {i i' : X ⟶ Y} (hi : E.IsInflation i) (hi' : E.IsInflation i') :
    ofInflation i hi = ofInflation i' hi' ↔ i = i' := by
  rw [ofInflation, ofInflation, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, he, rfl⟩
    have he' : e.hom = 𝟙 X := by simpa using he
    simp [he']
  · rintro rfl
    exact ⟨Iso.refl X, by simp, by simp⟩

/-- Distinct deflations give distinct morphisms of `Q(E)`. -/
theorem ofDeflation_inj {X Y : C} {p p' : X ⟶ Y} (hp : E.IsDeflation p) (hp' : E.IsDeflation p') :
    ofDeflation p hp = ofDeflation p' hp' ↔ p = p' := by
  rw [ofDeflation, ofDeflation, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, rfl, he⟩
    have he' : e.hom = 𝟙 X := by simpa using he
    simp [he']
  · rintro rfl
    exact ⟨Iso.refl X, by simp, by simp⟩

/-- `ofInflation` is compatible with composition. -/
@[simp]
theorem ofInflation_comp {X Y Z : C} (i : X ⟶ Y) (j : Y ⟶ Z) (hi : E.IsInflation i)
    (hj : E.IsInflation j) :
    ofInflation (i ≫ j) (E.isInflation_comp i j hi hj) = ofInflation i hi ≫ ofInflation j hj := by
  rw [ofInflation, ofInflation, ofInflation,
    homMk_comp_homMk _ _ _ _ (IsPullback.of_id_snd (f := i))]
  simp

/-- `ofDeflation` reverses composition. -/
@[simp]
theorem ofDeflation_comp {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) (hp : E.IsDeflation p)
    (hq : E.IsDeflation q) :
    ofDeflation (p ≫ q) (E.isDeflation_comp p q hp hq) = ofDeflation q hq ≫ ofDeflation p hp := by
  rw [ofDeflation, ofDeflation, ofDeflation,
    homMk_comp_homMk _ _ _ _ (IsPullback.of_id_fst (f := p))]
  simp

/-- **Normal form of a morphism of `Q(E)`.** The morphism represented by `X ↞ M ↣ Y` is the
reversed deflation `X ⟶ M` followed by the inflation `M ⟶ Y`. Together with
`homMk_eq_homMk_iff` and `exists_eq_homMk`, every morphism of `Q(E)` factors in this way, uniquely
up to an isomorphism of the middle object. -/
@[reassoc (attr := simp)]
theorem ofDeflation_comp_ofInflation {X Y M : C} (p : M ⟶ X) (i : M ⟶ Y) (hp : E.IsDeflation p)
    (hi : E.IsInflation i) :
    ofDeflation p hp ≫ ofInflation i hi = homMk p i hp hi := by
  rw [ofDeflation, ofInflation, homMk_comp_homMk _ _ _ _ (IsPullback.of_id_fst (f := 𝟙 M))]
  simp

/-- A reversed deflation followed by the morphism of a span is the morphism of the span whose
deflation leg is the composite deflation. -/
@[reassoc (attr := simp)]
theorem ofDeflation_comp_homMk {X X' Y M : C} (q : X' ⟶ X) (p : M ⟶ X') (i : M ⟶ Y)
    (hq : E.IsDeflation q) (hp : E.IsDeflation p) (hi : E.IsInflation i) :
    ofDeflation q hq ≫ homMk p i hp hi = homMk (p ≫ q) i (E.isDeflation_comp p q hp hq) hi := by
  rw [ofDeflation, homMk_comp_homMk _ _ _ _ (IsPullback.of_id_fst (f := p))]
  simp

/-- The morphism of a span followed by an inflation is the morphism of the span whose inflation
leg is the composite inflation. -/
@[reassoc (attr := simp)]
theorem homMk_comp_ofInflation {X Y Y' M : C} (p : M ⟶ X) (i : M ⟶ Y) (j : Y ⟶ Y')
    (hp : E.IsDeflation p) (hi : E.IsInflation i) (hj : E.IsInflation j) :
    homMk p i hp hi ≫ ofInflation j hj = homMk p (i ≫ j) hp (E.isInflation_comp i j hi hj) := by
  rw [ofInflation, homMk_comp_homMk _ _ _ _ (IsPullback.of_id_snd (f := i))]
  simp

/-- **The basic relation in `Q(E)`.** For a pullback square of an inflation `i` along a
deflation `q`, the inflation `i` followed by the reversed deflation `q` is the reversed base
change of `q` followed by the base change of `i`. -/
@[reassoc]
theorem ofInflation_comp_ofDeflation {Y M N P : C} {i : M ⟶ Y} {q : N ⟶ Y} {c : P ⟶ N}
    {a : P ⟶ M} (hi : E.IsInflation i) (hq : E.IsDeflation q) (sq : IsPullback c a q i) :
    ofInflation i hi ≫ ofDeflation q hq =
      ofDeflation a (E.isStableUnderBaseChange_deflations.of_isPullback sq hq) ≫
        ofInflation c (E.isInflation_of_isPullback sq.flip hi hq) := by
  rw [ofInflation, ofDeflation, homMk_comp_homMk _ _ _ _ sq, ofDeflation_comp_ofInflation]
  simp

/-- A span represents the identity of `Q(E)` exactly when its two legs are one and the same
isomorphism. -/
theorem homMk_eq_id_iff {X M : C} {p i : M ⟶ X} (hp : E.IsDeflation p) (hi : E.IsInflation i) :
    homMk p i hp hi = 𝟙 (mk X) ↔ IsIso p ∧ p = i := by
  rw [← homMk_id_id, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, hl, hr⟩
    simp only [Category.comp_id] at hl hr
    subst hl hr
    exact ⟨inferInstance, rfl⟩
  · rintro ⟨_, rfl⟩
    exact ⟨asIso p, by simp, by simp⟩

/-- For an isomorphism `e` of `C`, the inflation `e.hom` followed by the inflation `e.inv` is the
identity of `Q(E)`. -/
@[reassoc (attr := simp)]
theorem ofInflation_hom_inv_id {X Y : C} (e : X ≅ Y) (h : E.IsInflation e.hom)
    (h' : E.IsInflation e.inv) : ofInflation e.hom h ≫ ofInflation e.inv h' = 𝟙 (mk X) := by
  simp [← ofInflation_comp]

/-- For an isomorphism `e` of `C`, the inflation `e.inv` followed by the inflation `e.hom` is the
identity of `Q(E)`. -/
@[reassoc (attr := simp)]
theorem ofInflation_inv_hom_id {X Y : C} (e : X ≅ Y) (h : E.IsInflation e.inv)
    (h' : E.IsInflation e.hom) : ofInflation e.inv h ≫ ofInflation e.hom h' = 𝟙 (mk Y) := by
  simp [← ofInflation_comp]

/-- The isomorphism of `Q(E)` attached to an isomorphism of `C`. -/
noncomputable def ofIso {X Y : C} (e : X ≅ Y) : (mk X : E.QCategory) ≅ mk Y where
  hom := ofInflation e.hom (E.inflations.of_isIso _)
  inv := ofInflation e.inv (E.inflations.of_isIso _)
  hom_inv_id := ofInflation_hom_inv_id e _ _
  inv_hom_id := ofInflation_inv_hom_id e _ _

@[simp]
theorem ofIso_hom {X Y : C} (e : X ≅ Y) :
    (ofIso e : (mk X : E.QCategory) ≅ mk Y).hom = ofInflation e.hom (E.inflations.of_isIso _) :=
  (rfl)

@[simp]
theorem ofIso_inv {X Y : C} (e : X ≅ Y) :
    (ofIso e : (mk X : E.QCategory) ≅ mk Y).inv = ofInflation e.inv (E.inflations.of_isIso _) :=
  (rfl)

/-- For an isomorphism `e` of `C`, the reversed deflation `e.hom` is the inverse of
`ofIso e`. -/
@[simp]
theorem ofDeflation_hom {X Y : C} (e : X ≅ Y) :
    ofDeflation e.hom (E.deflations.of_isIso _) = (ofIso e).inv := by
  rw [ofDeflation, ofIso_inv, ofInflation, homMk_eq_homMk_iff]
  exact ⟨e, by simp, by simp⟩

/-- For an isomorphism `e` of `C`, the reversed deflation `e.inv` is `ofIso e`. -/
@[simp]
theorem ofDeflation_inv {X Y : C} (e : X ≅ Y) :
    ofDeflation e.inv (E.deflations.of_isIso _) = (ofIso e).hom := by
  rw [ofDeflation, ofIso_hom, ofInflation, homMk_eq_homMk_iff]
  exact ⟨e.symm, by simp, by simp⟩

/-- If the composite of two spans is the identity, the inflation leg of the second span is an
isomorphism. -/
private theorem isIso_of_homMk_comp_homMk_eq_id {X Y M N : C} {p : M ⟶ X} {i : M ⟶ Y}
    {q : N ⟶ Y} {j : N ⟶ X} (hp : E.IsDeflation p) (hi : E.IsInflation i) (hq : E.IsDeflation q)
    (hj : E.IsInflation j) (h : homMk p i hp hi ≫ homMk q j hq hj = 𝟙 (mk X)) : IsIso j := by
  have : HasPullback q i := E.hasPullbacks_deflations.hasPullback i hq
  rw [homMk_comp_homMk _ _ _ _ (IsPullback.of_hasPullback q i), homMk_eq_id_iff] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [h₂] at h₁
  have : Mono j := ConflationClass.IsInflation.mono hj
  have : IsSplitEpi j := IsSplitEpi.mk' ⟨inv (pullback.fst q i ≫ j) ≫ pullback.fst q i, by simp⟩
  exact isIso_of_mono_of_isSplitEpi j

/-- A span whose inflation leg is an isomorphism represents a reversed deflation. -/
private theorem homMk_eq_ofDeflation {X Y M : C} {p : M ⟶ X} {i : M ⟶ Y} (hp : E.IsDeflation p)
    (hi : E.IsInflation i) [IsIso i] :
    homMk p i hp hi =
      ofDeflation (inv i ≫ p) (E.isDeflation_comp _ _ (E.deflations.of_isIso _) hp) := by
  rw [ofDeflation, homMk_eq_homMk_iff]
  exact ⟨asIso i, by simp, by simp⟩

/-- **The isomorphisms of `Q(E)` are those of `C`.** A morphism of `Q(E)` is an isomorphism
exactly when it is `ofIso e` for an isomorphism `e` of `C`. -/
theorem isIso_iff_exists_iso {X Y : C} (f : (mk X : E.QCategory) ⟶ mk Y) :
    IsIso f ↔ ∃ e : X ≅ Y, f = (ofIso e).hom := by
  refine ⟨fun hf => ?_, fun ⟨e, he⟩ => he ▸ inferInstance⟩
  obtain ⟨M, p, i, hp, hi, rfl⟩ := exists_eq_homMk f
  obtain ⟨N, q, j, hq, hj, hg⟩ := exists_eq_homMk (inv (homMk p i hp hi))
  have h₁ := IsIso.hom_inv_id (homMk p i hp hi)
  have h₂ := IsIso.inv_hom_id (homMk p i hp hi)
  rw [hg] at h₁ h₂
  have : IsIso j := isIso_of_homMk_comp_homMk_eq_id hp hi hq hj h₁
  have : IsIso i := isIso_of_homMk_comp_homMk_eq_id hq hj hp hi h₂
  rw [homMk_eq_ofDeflation, homMk_eq_ofDeflation, ← ofDeflation_comp, ofDeflation,
    homMk_eq_id_iff] at h₂
  -- The reversed deflation `a = inv i ≫ p : Y ⟶ X` is an epimorphism with a retraction.
  have : Epi (inv i ≫ p) :=
    ConflationClass.IsDeflation.epi (E.isDeflation_comp _ _ (E.deflations.of_isIso _) hp)
  have : IsIso ((inv i ≫ p) ≫ inv j ≫ q) := h₂.1
  have : IsSplitMono (inv i ≫ p) := IsSplitMono.mk' ⟨(inv j ≫ q) ≫ inv ((inv i ≫ p) ≫ inv j ≫ q),
    by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have : IsIso (inv i ≫ p) := isIso_of_epi_of_isSplitMono _
  refine ⟨(asIso (inv i ≫ p)).symm, ?_⟩
  rw [homMk_eq_ofDeflation]
  exact (ofDeflation_hom (asIso (inv i ≫ p))).trans (by simp)

/-- **Morphisms out of the zero object of `Q(E)` are admissible subobjects.** A span
`0 ↞ M ↣ Y` is determined up to isomorphism by the subobject of `Y` represented by its inflation
leg. -/
noncomputable def fromZeroEquiv (Y : C) :
    ((mk 0 : E.QCategory) ⟶ mk Y) ≃ {P : Subobject Y // E.IsInflation P.arrow} where
  toFun f := Quotient.lift
    (fun S => haveI := ConflationClass.IsInflation.mono S.wr
      ⟨Subobject.mk S.r, by
        rw [← Subobject.underlyingIso_hom_comp_eq_mk]
        exact (E.inflations.cancel_left_of_respectsIso _ _).2 S.wr⟩)
    (fun S S' h => by
      obtain ⟨e⟩ := h
      have := ConflationClass.IsInflation.mono S.wr
      have := ConflationClass.IsInflation.mono S'.wr
      exact Subtype.ext (Subobject.mk_eq_mk_of_comm _ _ (Span.SpanBicat.apexIso e) e.hom.hom_r))
    (Bicategory.HomotopyCategory.homEquiv _ _ f)
  invFun P := homMk 0 P.val.arrow (E.isDeflation_zero _) P.property
  left_inv f := by
    obtain ⟨S, rfl⟩ := Bicategory.HomotopyCategory.homMk_surjective f
    have := ConflationClass.IsInflation.mono S.wr
    dsimp only
    rw [Bicategory.HomotopyCategory.homEquiv_homMk, Quotient.lift_mk]
    exact Bicategory.HomotopyCategory.homMk_eq_homMk
      (Span.SpanBicat.mkIso₂ (Subobject.underlyingIso S.r) ((isZero_zero C).eq_of_tgt _ _)
        (by simp))
  right_inv P := by
    obtain ⟨P, hP⟩ := P
    dsimp only
    rw [homMk, Bicategory.HomotopyCategory.homEquiv_homMk, Quotient.lift_mk]
    exact Subtype.ext (Subobject.mk_arrow P)

/-- The admissible subobject attached to the morphism `0 ⟶ Y` represented by `0 ↞ M ↣ Y` is the
subobject represented by the inflation `M ↣ Y`. -/
@[simp]
theorem fromZeroEquiv_homMk {Y M : C} (p : M ⟶ 0) (i : M ⟶ Y) (hp : E.IsDeflation p)
    (hi : E.IsInflation i) :
    (fromZeroEquiv Y (homMk p i hp hi) : Subobject Y) =
      haveI := ConflationClass.IsInflation.mono hi
      Subobject.mk i := by
  dsimp only [fromZeroEquiv, Equiv.coe_fn_mk]
  rw [homMk, Bicategory.HomotopyCategory.homEquiv_homMk, Quotient.lift_mk]

@[simp]
theorem fromZeroEquiv_symm_apply {Y : C} (P : {P : Subobject Y // E.IsInflation P.arrow}) :
    (fromZeroEquiv Y).symm P = homMk 0 P.val.arrow (E.isDeflation_zero _) P.property :=
  (rfl)

/-- The two morphisms `0 ⟶ Y` of `Q(E)` given by the zero subobject `0 ↣ Y` and by the whole
subobject `Y ↣ Y` agree only when `Y` is a zero object. -/
theorem ofInflation_zero_eq_ofDeflation_zero_iff (Y : C) :
    ofInflation (0 : 0 ⟶ Y) (E.isInflation_zero Y) = ofDeflation (0 : Y ⟶ 0) (E.isDeflation_zero Y)
      ↔ IsZero Y := by
  rw [ofInflation, ofDeflation, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, -, he⟩
    simpa [IsZero.iff_id_eq_zero] using congrArg (e.inv ≫ ·) he
  · intro hY
    exact ⟨(isZero_zero C).iso hY, (isZero_zero C).eq_of_src _ _, hY.eq_of_tgt _ _⟩

end QCategory

end ExactStructure

end TauCeti
