/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Bicartesian
public import Mathlib.CategoryTheory.Bicategory.Span.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Quillen's Q-category of an exact category

For an exact structure `E` on an additive category `C`, Quillen's Q-category `E.QuillenQ` has the
same objects as `C`, and its morphisms `X ⟶ Y` are isomorphism classes of admissible spans
`X ↞ M ↣ Y`, where the left leg is a deflation and the right leg is an inflation. Composition of
admissible spans is given by pullback over the middle object, which exists and remains admissible
by deflation base change and Bühler's Proposition 2.15
(`TauCeti.ExactStructure.isInflation_of_isPullback_of_isDeflation`).

We build `E.QuillenQ` directly as the isomorphism-class quotient of Mathlib's bicategory of spans
`CategoryTheory.Span.SpanBicat C E.deflations E.inflations`, inheriting well-definedness of
composition, unit laws, and associativity from the bicategory's whiskering, unitors, and
associator. When `C` is a small category, `E.QuillenQ` is automatically a small category in the
same universe.

## Main definitions

* `TauCeti.ExactStructure.QuillenQ`: the Q-category `Q(E)` attached to an exact structure `E`.
* `TauCeti.ExactStructure.QuillenQ.homMk` and `TauCeti.ExactStructure.QuillenQ.homLift`: the
  quotient map sending an admissible span `Span E.deflations E.inflations X Y` to its morphism in
  `E.QuillenQ`, and its universal descent map.
* `TauCeti.ExactStructure.QuillenQ.ofInflation` and
  `TauCeti.ExactStructure.QuillenQ.ofDeflation`: the covariant arrow attached to an inflation and
  the contravariant arrow attached to a deflation.
* `TauCeti.ExactStructure.QuillenQ.ofIso`, `TauCeti.ExactStructure.QuillenQ.isoEquiv`, and
  `TauCeti.ExactStructure.QuillenQ.autEquiv`: the identification of isomorphisms (and
  automorphisms) in `E.QuillenQ` with those in `C`.
* `TauCeti.ExactStructure.QuillenQ.homFromIsZeroEquivSubobject`: the bijection between morphisms
  out of a zero object in `E.QuillenQ` and admissible subobjects of the target.

## Main results

* `TauCeti.ExactStructure.QuillenQ.homMk_comp_of_isPullback`: span composition computed via an
  arbitrary pullback square.
* `TauCeti.ExactStructure.QuillenQ.homMk_eq_ofDeflation_comp_ofInflation`,
  `TauCeti.ExactStructure.QuillenQ.exists_ofDeflation_comp_ofInflation`, and
  `TauCeti.ExactStructure.QuillenQ.ofDeflation_comp_ofInflation_eq_iff_existsUnique`: every
  Q-morphism factors as a reversed deflation followed by an inflation, uniquely up to a unique
  isomorphism of the middle object.
* `TauCeti.ExactStructure.QuillenQ.ofInflation_comp_ofDeflation_of_isPullback` and
  `TauCeti.ExactStructure.QuillenQ.ofInflation_comp_ofDeflation_of_isPushout`: the interchange
  laws for admissible pullback and pushout squares.
* `TauCeti.ExactStructure.QuillenQ.isIso_homMk_iff`: an admissible span defines an isomorphism in
  `E.QuillenQ` if and only if both of its legs are isomorphisms in `C`.
* `TauCeti.ExactStructure.QuillenQ.ofInflation_zero_eq_ofDeflation_zero_iff`: the zero and whole
  admissible subobject arrows `Z ⟶ Y` out of a zero object agree if and only if `Y` is zero.

## References

* Daniel Quillen, *Higher algebraic K-theory: I*, Algebraic K-theory, I: Higher K-theories
  (Battelle Memorial Inst., Seattle, 1972), Lecture Notes in Math. **341**, Springer (1973),
  Section 2, pp. 99–104.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter IV, Section 6.1.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>, Propositions 2.15–2.16 and Remark 2.17.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- Quillen's Q-category `Q(E)` attached to an exact structure `E`. Its objects are the objects of
`C`, and its morphisms `X ⟶ Y` are isomorphism classes of admissible spans `X ↞ M ↣ Y` with left
leg a deflation and right leg an inflation. -/
@[ext]
structure QuillenQ (E : ExactStructure C) : Type u where
  /-- The underlying object of `C`. -/
  as : C

namespace QuillenQ

variable {E : ExactStructure C}

noncomputable instance : Inhabited E.QuillenQ :=
  ⟨⟨0⟩⟩

/-- There is at most one morphism between two admissible spans with the same endpoints. -/
theorem subsingleton_spanHom {X Y : C} (S₁ S₂ : Span E.deflations E.inflations X Y) :
    Subsingleton (S₁ ⟶ S₂) := by
  refine ⟨fun f g ↦ ?_⟩
  have : Mono S₂.r := ConflationClass.IsInflation.mono S₂.wr
  ext
  exact (cancel_mono S₂.r).mp (f.hom_r.trans g.hom_r.symm)

noncomputable instance : Category.{max u v} E.QuillenQ where
  Hom X Y := Quotient (isIsomorphicSetoid (Span E.deflations E.inflations X.as Y.as))
  id X := Quotient.mk (isIsomorphicSetoid _) (Span.id X.as)
  comp {X Y Z} :=
    Quotient.lift₂
      (fun S₁ S₂ ↦ Quotient.mk (isIsomorphicSetoid _) (Span.comp S₁ S₂))
      (fun S₁ S₂ S₁' S₂' ⟨e₁⟩ ⟨e₂⟩ ↦ Quotient.sound
        ⟨@Bicategory.whiskerRightIso (Span.SpanBicat C E.deflations E.inflations) _
            ⟨X.as⟩ ⟨Y.as⟩ ⟨Z.as⟩ S₁ S₁' e₁ S₂ ≪≫
          @Bicategory.whiskerLeftIso (Span.SpanBicat C E.deflations E.inflations) _
            ⟨X.as⟩ ⟨Y.as⟩ ⟨Z.as⟩ S₁' S₂ S₂' e₂⟩)
  id_comp {X Y} f :=
    Quotient.inductionOn f fun S ↦
      Quotient.sound ⟨@Span.SpanBicat.leftUnitor C _ E.deflations E.inflations
        _ _ _ _ _ _ _ ⟨X.as⟩ ⟨Y.as⟩ S⟩
  comp_id {X Y} f :=
    Quotient.inductionOn f fun S ↦
      Quotient.sound ⟨@Span.SpanBicat.rightUnitor C _ E.deflations E.inflations
        _ _ _ _ _ _ _ ⟨X.as⟩ ⟨Y.as⟩ S⟩
  assoc {W X Y Z} f g h :=
    Quotient.inductionOn₃ f g h fun S₁ S₂ S₃ ↦
      Quotient.sound ⟨@Span.SpanBicat.associator C _ E.deflations E.inflations
        _ _ _ _ _ _ _ ⟨W.as⟩ ⟨X.as⟩ ⟨Y.as⟩ ⟨Z.as⟩ S₁ S₂ S₃⟩

/-- The morphism in `E.QuillenQ` represented by an admissible span `X ↞ M ↣ Y`. -/
def homMk {X Y : C} (S : Span E.deflations E.inflations X Y) :
    (⟨X⟩ : E.QuillenQ) ⟶ ⟨Y⟩ :=
  Quotient.mk (isIsomorphicSetoid _) S

/-- Two admissible spans represent the same morphism in `E.QuillenQ` if and only if they are
isomorphic as spans. -/
theorem homMk_eq_iff {X Y : C} {S₁ S₂ : Span E.deflations E.inflations X Y} :
    homMk S₁ = homMk S₂ ↔ Nonempty (S₁ ≅ S₂) :=
  Quotient.eq (r := isIsomorphicSetoid _)

/-- Induction principle on morphisms in `E.QuillenQ`: every morphism is represented by an
admissible span. -/
@[elab_as_elim]
theorem hom_induction {X Y : E.QuillenQ} {motive : (X ⟶ Y) → Prop}
    (h : ∀ S : Span E.deflations E.inflations X.as Y.as, motive (homMk S)) (f : X ⟶ Y) :
    motive f :=
  Quotient.inductionOn f h

/-- Descend a function on admissible spans to morphisms in `E.QuillenQ` when it respects span
isomorphisms. -/
def homLift {X Y : E.QuillenQ} {α : Sort*}
    (f : Span E.deflations E.inflations X.as Y.as → α)
    (hf : ∀ S₁ S₂ : Span E.deflations E.inflations X.as Y.as, Nonempty (S₁ ≅ S₂) → f S₁ = f S₂) :
    (X ⟶ Y) → α :=
  Quotient.lift f fun S₁ S₂ h ↦ hf S₁ S₂ h

@[simp]
theorem homLift_homMk {X Y : E.QuillenQ} {α : Sort*}
    (f : Span E.deflations E.inflations X.as Y.as → α)
    (hf : ∀ S₁ S₂ : Span E.deflations E.inflations X.as Y.as, Nonempty (S₁ ≅ S₂) → f S₁ = f S₂)
    (S : Span E.deflations E.inflations X.as Y.as) :
    homLift f hf (homMk S) = f S :=
  (rfl)

/-- Every morphism in `E.QuillenQ` is represented by an admissible span. -/
theorem homMk_surjective {X Y : C} :
    Function.Surjective (homMk (E := E) (X := X) (Y := Y)) :=
  fun f ↦ Quot.exists_rep f

/-- The identity span represents the identity morphism in `E.QuillenQ`. -/
@[simp]
theorem homMk_id (X : C) :
    homMk (Span.id (Wₗ := E.deflations) (Wᵣ := E.inflations) X) = 𝟙 (⟨X⟩ : E.QuillenQ) :=
  (rfl)

/-- Composition in `E.QuillenQ` is represented by `CategoryTheory.Span.comp`. -/
@[simp]
theorem homMk_comp {X Y Z : C}
    (S₁ : Span E.deflations E.inflations X Y) (S₂ : Span E.deflations E.inflations Y Z) :
    homMk S₁ ≫ homMk S₂ = homMk (S₁.comp S₂) :=
  (rfl)

/-- Composition of two admissible spans computed using an arbitrary pullback square of `S₁.r` and
`S₂.l`. -/
theorem homMk_comp_of_isPullback {X Y Z P : C}
    (S₁ : Span E.deflations E.inflations X Y) (S₂ : Span E.deflations E.inflations Y Z)
    {f : P ⟶ S₁.apex} {g : P ⟶ S₂.apex} (hsq : IsPullback f g S₁.r S₂.l) :
    homMk S₁ ≫ homMk S₂ =
      homMk ⟨P, f ≫ S₁.l, g ≫ S₂.r,
        E.isDeflation_comp f S₁.l
          (E.isStableUnderBaseChange_deflations.of_isPullback hsq.flip S₂.wl) S₁.wl,
        E.isInflation_comp g S₂.r
          (E.isInflation_of_isPullback_of_isDeflation S₂.wl S₁.wr hsq.flip) S₂.wr⟩ := by
  rw [homMk_comp, homMk_eq_iff]
  exact ⟨(Span.mkIso hsq.isoPullback
    (by simp [Span.comp, hsq.isoPullback_hom_fst_assoc])
    (by simp [Span.comp, hsq.isoPullback_hom_snd_assoc])).symm⟩

/-! ### Distinguished morphisms: inflations and reversed deflations -/

/-- The covariant morphism in `E.QuillenQ` attached to an inflation `i : X ↣ Y`, represented by the
span `X ↞ X ↣ Y` with left leg `𝟙 X`. -/
def ofInflation {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i) :
    (⟨X⟩ : E.QuillenQ) ⟶ ⟨Y⟩ :=
  homMk ⟨X, 𝟙 X, i, E.isDeflation_id X, hi⟩

/-- The contravariant morphism in `E.QuillenQ` attached to a deflation `p : Y ↠ X`, represented by
the span `X ↞ Y ↣ Y` with right leg `𝟙 Y`. -/
def ofDeflation {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p) :
    (⟨X⟩ : E.QuillenQ) ⟶ ⟨Y⟩ :=
  homMk ⟨Y, p, 𝟙 Y, hp, E.isInflation_id Y⟩

/-- `ofInflation i hi` is represented by the span `X ↞ X ↣ Y` with left leg `𝟙 X`. -/
theorem ofInflation_eq_homMk {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i) :
    ofInflation i hi = homMk ⟨X, 𝟙 X, i, E.isDeflation_id X, hi⟩ :=
  (rfl)

/-- `ofDeflation p hp` is represented by the span `X ↞ Y ↣ Y` with right leg `𝟙 Y`. -/
theorem ofDeflation_eq_homMk {X Y : C} (p : Y ⟶ X) (hp : E.IsDeflation p) :
    ofDeflation p hp = homMk ⟨Y, p, 𝟙 Y, hp, E.isInflation_id Y⟩ :=
  (rfl)

/-- The identity inflation induces the identity morphism in `E.QuillenQ`. -/
@[simp]
theorem ofInflation_id (X : C) :
    ofInflation (𝟙 X) (E.isInflation_id X) = 𝟙 (⟨X⟩ : E.QuillenQ) :=
  (rfl)

/-- The identity deflation induces the identity morphism in `E.QuillenQ`. -/
@[simp]
theorem ofDeflation_id (X : C) :
    ofDeflation (𝟙 X) (E.isDeflation_id X) = 𝟙 (⟨X⟩ : E.QuillenQ) :=
  (rfl)

/-- `ofInflation` is covariant with respect to composition of inflations. -/
@[reassoc (attr := simp)]
theorem ofInflation_comp {X Y Z : C} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : E.IsInflation i) (hj : E.IsInflation j) :
    ofInflation i hi ≫ ofInflation j hj =
      ofInflation (i ≫ j) (E.isInflation_comp i j hi hj) := by
  dsimp only [ofInflation]
  rw [homMk_comp_of_isPullback _ _ (IsPullback.of_id_fst (f := i))]
  simp only [Category.id_comp]

/-- `ofDeflation` is contravariant with respect to composition of deflations. -/
@[reassoc (attr := simp)]
theorem ofDeflation_comp {X Y Z : C} {p : Y ⟶ X} {q : Z ⟶ Y}
    (hp : E.IsDeflation p) (hq : E.IsDeflation q) :
    ofDeflation p hp ≫ ofDeflation q hq =
      ofDeflation (q ≫ p) (E.isDeflation_comp q p hq hp) := by
  dsimp only [ofDeflation]
  rw [homMk_comp_of_isPullback _ _ (IsPullback.of_id_snd (f := q))]
  simp only [Category.id_comp]

/-- Two inflations with the same endpoints induce the same morphism in `E.QuillenQ` if and only if
they are equal. -/
theorem ofInflation_inj {X Y : C} {i₁ i₂ : X ⟶ Y}
    (hi₁ : E.IsInflation i₁) (hi₂ : E.IsInflation i₂) :
    ofInflation i₁ hi₁ = ofInflation i₂ hi₂ ↔ i₁ = i₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  obtain ⟨e⟩ := homMk_eq_iff.mp h
  have hl : e.hom.hom = 𝟙 X := by simpa using e.hom.hom_l
  have hr : e.hom.hom ≫ i₂ = i₁ := e.hom.hom_r
  rw [hl, Category.id_comp] at hr
  exact hr.symm

/-- Two deflations with the same endpoints induce the same morphism in `E.QuillenQ` if and only if
they are equal. -/
theorem ofDeflation_inj {X Y : C} {p₁ p₂ : Y ⟶ X}
    (hp₁ : E.IsDeflation p₁) (hp₂ : E.IsDeflation p₂) :
    ofDeflation p₁ hp₁ = ofDeflation p₂ hp₂ ↔ p₁ = p₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  obtain ⟨e⟩ := homMk_eq_iff.mp h
  have hr : e.hom.hom = 𝟙 Y := by simpa using e.hom.hom_r
  have hl : e.hom.hom ≫ p₂ = p₁ := e.hom.hom_l
  rw [hr, Category.id_comp] at hl
  exact hl.symm

/-- For an isomorphism `e : X ≅ Y`, the reversed deflation `ofDeflation e.hom` equals the inflation
arrow of its inverse `ofInflation e.inv`. -/
theorem ofDeflation_eq_ofInflation_inv {X Y : C} (e : X ≅ Y) :
    ofDeflation e.hom (E.deflations.of_isIso e.hom) =
      ofInflation e.inv (E.inflations.of_isIso e.inv) := by
  rw [ofDeflation, ofInflation, homMk_eq_iff]
  exact ⟨Span.mkIso e (by simp) (by simp)⟩

/-- For an isomorphism `e : X ≅ Y`, the inflation arrow `ofInflation e.hom` equals the reversed
deflation of its inverse `ofDeflation e.inv`. -/
theorem ofInflation_eq_ofDeflation_inv {X Y : C} (e : X ≅ Y) :
    ofInflation e.hom (E.inflations.of_isIso e.hom) =
      ofDeflation e.inv (E.deflations.of_isIso e.inv) :=
  (ofDeflation_eq_ofInflation_inv e.symm).symm

/-! ### Normal form and admissible square interchange -/

/-- Every admissible span factors in `E.QuillenQ` as the reversed deflation of its left leg
followed by the inflation of its right leg. -/
theorem homMk_eq_ofDeflation_comp_ofInflation {X Y : C}
    (S : Span E.deflations E.inflations X Y) :
    homMk S = ofDeflation S.l S.wl ≫ ofInflation S.r S.wr := by
  dsimp only [ofDeflation, ofInflation]
  rw [homMk_comp_of_isPullback _ _ (IsPullback.of_id_fst (f := 𝟙 S.apex))]
  simp only [Category.id_comp]

/-- Every morphism in `E.QuillenQ` factors as a reversed deflation followed by an inflation. -/
theorem exists_ofDeflation_comp_ofInflation {X Y : C} (f : (⟨X⟩ : E.QuillenQ) ⟶ ⟨Y⟩) :
    ∃ (M : C) (p : M ⟶ X) (i : M ⟶ Y) (hp : E.IsDeflation p) (hi : E.IsInflation i),
      f = ofDeflation p hp ≫ ofInflation i hi := by
  obtain ⟨S, rfl⟩ := homMk_surjective f
  exact ⟨S.apex, S.l, S.r, S.wl, S.wr, homMk_eq_ofDeflation_comp_ofInflation S⟩

/-- Two normal-form composites `ofDeflation p₁ ≫ ofInflation i₁` and
`ofDeflation p₂ ≫ ofInflation i₂` are equal in `E.QuillenQ` if and only if there is an
isomorphism between their middle objects commuting with both legs. -/
theorem ofDeflation_comp_ofInflation_eq_iff {X Y M₁ M₂ : C}
    {p₁ : M₁ ⟶ X} {i₁ : M₁ ⟶ Y} (hp₁ : E.IsDeflation p₁) (hi₁ : E.IsInflation i₁)
    {p₂ : M₂ ⟶ X} {i₂ : M₂ ⟶ Y} (hp₂ : E.IsDeflation p₂) (hi₂ : E.IsInflation i₂) :
    ofDeflation p₁ hp₁ ≫ ofInflation i₁ hi₁ = ofDeflation p₂ hp₂ ≫ ofInflation i₂ hi₂ ↔
      ∃ e : M₁ ≅ M₂, e.hom ≫ p₂ = p₁ ∧ e.hom ≫ i₂ = i₁ := by
  rw [← homMk_eq_ofDeflation_comp_ofInflation ⟨M₁, p₁, i₁, hp₁, hi₁⟩,
    ← homMk_eq_ofDeflation_comp_ofInflation ⟨M₂, p₂, i₂, hp₂, hi₂⟩, homMk_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨Span.SpanBicat.apexIso (Wₗ := E.deflations) (Wᵣ := E.inflations) (X := ⟨X⟩) (Y := ⟨Y⟩) e,
      e.hom.hom_l, e.hom.hom_r⟩
  · rintro ⟨e, hl, hr⟩
    exact ⟨Span.mkIso e hl hr⟩

/-- Two normal-form composites are equal in `E.QuillenQ` if and only if there is a unique
isomorphism between their middle objects commuting with both legs. -/
theorem ofDeflation_comp_ofInflation_eq_iff_existsUnique {X Y M₁ M₂ : C}
    {p₁ : M₁ ⟶ X} {i₁ : M₁ ⟶ Y} (hp₁ : E.IsDeflation p₁) (hi₁ : E.IsInflation i₁)
    {p₂ : M₂ ⟶ X} {i₂ : M₂ ⟶ Y} (hp₂ : E.IsDeflation p₂) (hi₂ : E.IsInflation i₂) :
    ofDeflation p₁ hp₁ ≫ ofInflation i₁ hi₁ = ofDeflation p₂ hp₂ ≫ ofInflation i₂ hi₂ ↔
      ∃! e : M₁ ≅ M₂, e.hom ≫ p₂ = p₁ ∧ e.hom ≫ i₂ = i₁ := by
  rw [ofDeflation_comp_ofInflation_eq_iff]
  constructor
  · rintro ⟨e, hl, hr⟩
    refine ⟨e, ⟨hl, hr⟩, fun e' ⟨_, hr'⟩ ↦ ?_⟩
    have : Mono i₂ := ConflationClass.IsInflation.mono hi₂
    exact Iso.ext ((cancel_mono i₂).mp (hr'.trans hr.symm))
  · rintro ⟨e, h, -⟩
    exact ⟨e, h⟩

/-- **Admissible pullback-square interchange.** For a pullback square with an inflation `i` on the
right and a deflation `p` on the bottom, the composite `ofInflation i ≫ ofDeflation p` equals
`ofDeflation p' ≫ ofInflation i'` in `E.QuillenQ`. -/
theorem ofInflation_comp_ofDeflation_of_isPullback {P X Y Z : C}
    {p' : P ⟶ X} {i' : P ⟶ Z} {i : X ⟶ Y} {p : Z ⟶ Y}
    (hi : E.IsInflation i) (hp : E.IsDeflation p) (hsq : IsPullback p' i' i p) :
    ofInflation i hi ≫ ofDeflation p hp =
      ofDeflation p' (E.isStableUnderBaseChange_deflations.of_isPullback hsq.flip hp) ≫
        ofInflation i' (E.isInflation_of_isPullback_of_isDeflation hp hi hsq.flip) := by
  dsimp only [ofInflation, ofDeflation]
  rw [homMk_comp_of_isPullback _ _ hsq]
  simp only [Category.comp_id]
  exact homMk_eq_ofDeflation_comp_ofInflation _

/-- **Admissible pushout-square interchange.** For a pushout square with a deflation `p'` on the
top and an inflation `i'` on the left, `ofInflation i ≫ ofDeflation p` equals
`ofDeflation p' ≫ ofInflation i'` in `E.QuillenQ`. -/
theorem ofInflation_comp_ofDeflation_of_isPushout {P X Y Z : C}
    {p' : P ⟶ X} {i' : P ⟶ Z} {i : X ⟶ Y} {p : Z ⟶ Y}
    (hp' : E.IsDeflation p') (hi' : E.IsInflation i') (hsq : IsPushout p' i' i p) :
    ofInflation i (E.isStableUnderCobaseChange_inflations.of_isPushout hsq hi') ≫
      ofDeflation p (E.isDeflation_of_isPushout_of_isInflation hi' hp' hsq.flip) =
      ofDeflation p' hp' ≫ ofInflation i' hi' :=
  ofInflation_comp_ofDeflation_of_isPullback _ _
    (E.isPullback_of_isPushout_of_isInflation hi' hsq.flip).flip

/-! ### Isomorphisms in `Q(E)` -/

/-- The isomorphism in `E.QuillenQ` induced by an isomorphism in `C`, given covariantly by
`ofInflation`. -/
def ofIso {X Y : C} (e : X ≅ Y) : (⟨X⟩ : E.QuillenQ) ≅ ⟨Y⟩ where
  hom := ofInflation e.hom (E.inflations.of_isIso e.hom)
  inv := ofInflation e.inv (E.inflations.of_isIso e.inv)
  hom_inv_id := by simp
  inv_hom_id := by simp

@[simp]
theorem ofIso_hom {X Y : C} (e : X ≅ Y) :
    (ofIso (E := E) e).hom = ofInflation e.hom (E.inflations.of_isIso e.hom) :=
  (rfl)

@[simp]
theorem ofIso_inv {X Y : C} (e : X ≅ Y) :
    (ofIso (E := E) e).inv = ofInflation e.inv (E.inflations.of_isIso e.inv) :=
  (rfl)

@[simp]
theorem ofIso_refl (X : C) : ofIso (E := E) (Iso.refl X) = Iso.refl (⟨X⟩ : E.QuillenQ) := by
  ext
  simp

@[simp]
theorem ofIso_trans {X Y Z : C} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) :
    ofIso (E := E) (e₁ ≪≫ e₂) = ofIso e₁ ≪≫ ofIso e₂ := by
  ext
  simp

@[simp]
theorem ofIso_symm {X Y : C} (e : X ≅ Y) :
    ofIso (E := E) e.symm = (ofIso e).symm := by
  ext
  simp

/-- `ofIso` is injective on isomorphisms in `C`. -/
theorem ofIso_injective {X Y : C} : Function.Injective (ofIso (E := E) (X := X) (Y := Y)) := by
  intro e₁ e₂ h
  apply Iso.ext
  exact (ofInflation_inj (E.inflations.of_isIso e₁.hom) (E.inflations.of_isIso e₂.hom)).mp
    (congrArg Iso.hom h)

/-- A commuting square between inflations and isomorphisms commutes in `E.QuillenQ`. -/
theorem ofInflation_comp_ofIso {X₁ X₂ Y₁ Y₂ : C} {i₁ : X₁ ⟶ Y₁} {i₂ : X₂ ⟶ Y₂}
    (hi₁ : E.IsInflation i₁) (hi₂ : E.IsInflation i₂) (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂)
    (h : i₁ ≫ eY.hom = eX.hom ≫ i₂) :
    ofInflation i₁ hi₁ ≫ (ofIso eY).hom = (ofIso eX).hom ≫ ofInflation i₂ hi₂ := by
  simp only [ofIso_hom, ofInflation_comp]
  exact (ofInflation_inj _ _).mpr h

/-- A commuting square between deflations and isomorphisms commutes with reversed deflations in
`E.QuillenQ`. -/
theorem ofDeflation_comp_ofIso {X₁ X₂ Y₁ Y₂ : C} {p₁ : Y₁ ⟶ X₁} {p₂ : Y₂ ⟶ X₂}
    (hp₁ : E.IsDeflation p₁) (hp₂ : E.IsDeflation p₂) (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂)
    (h : p₁ ≫ eX.hom = eY.hom ≫ p₂) :
    ofDeflation p₁ hp₁ ≫ (ofIso eY).hom = (ofIso eX).hom ≫ ofDeflation p₂ hp₂ := by
  rw [ofIso_hom, ofIso_hom]
  exact (ofInflation_comp_ofDeflation_of_isPullback
    (E.inflations.of_isIso eX.hom) hp₂ (IsPullback.of_vert_isIso ⟨h⟩)).symm

/-- If the composite of two admissible spans `S` and `T` is the identity in `E.QuillenQ`, then the
left leg of `S` and the right leg of `T` are isomorphisms in `C`. -/
private theorem isIso_left_and_right_of_comp_eq_id {X Y : C}
    (S : Span E.deflations E.inflations X Y) (T : Span E.deflations E.inflations Y X)
    (h : homMk S ≫ homMk T = 𝟙 (⟨X⟩ : E.QuillenQ)) :
    IsIso S.l ∧ IsIso T.r := by
  rw [homMk_comp, ← homMk_id, homMk_eq_iff] at h
  obtain ⟨e⟩ := h
  let α : pullback S.r T.l ≅ X :=
    Span.SpanBicat.apexIso (Wₗ := E.deflations) (Wᵣ := E.inflations) (X := ⟨X⟩) (Y := ⟨X⟩) e
  have hfst_l : pullback.fst S.r T.l ≫ S.l = α.hom := by
    simpa [α, Span.comp] using e.hom.hom_l.symm
  have hsnd_r : pullback.snd S.r T.l ≫ T.r = α.hom := by
    simpa [α, Span.comp] using e.hom.hom_r.symm
  have : Epi (pullback.fst S.r T.l) := ConflationClass.IsDeflation.epi
    (E.isStableUnderBaseChange_deflations.of_isPullback
      (IsPullback.of_hasPullback S.r T.l).flip T.wl)
  have : IsSplitMono (pullback.fst S.r T.l) :=
    ⟨⟨S.l ≫ α.inv, by rw [← Category.assoc, hfst_l, α.hom_inv_id]⟩⟩
  have : IsIso (pullback.fst S.r T.l) := isIso_of_epi_of_isSplitMono _
  have : IsIso (pullback.fst S.r T.l ≫ S.l) := hfst_l ▸ inferInstance
  have hSl : IsIso S.l := IsIso.of_isIso_comp_left (pullback.fst S.r T.l) S.l
  have : Mono T.r := ConflationClass.IsInflation.mono T.wr
  have : IsSplitEpi T.r :=
    ⟨⟨α.inv ≫ pullback.snd S.r T.l, by rw [Category.assoc, hsnd_r, α.inv_hom_id]⟩⟩
  exact ⟨hSl, isIso_of_mono_of_isSplitEpi T.r⟩

/-- An admissible span represents an isomorphism in `E.QuillenQ` if and only if both of its legs
are isomorphisms in `C`. -/
theorem isIso_homMk_iff {X Y : C} (S : Span E.deflations E.inflations X Y) :
    IsIso (homMk S) ↔ IsIso S.l ∧ IsIso S.r := by
  constructor
  · intro h
    obtain ⟨T, hT⟩ := homMk_surjective (inv (homMk S))
    have hST : homMk S ≫ homMk T = 𝟙 (⟨X⟩ : E.QuillenQ) := by rw [hT]; exact IsIso.hom_inv_id _
    have hTS : homMk T ≫ homMk S = 𝟙 (⟨Y⟩ : E.QuillenQ) := by rw [hT]; exact IsIso.inv_hom_id _
    exact ⟨(isIso_left_and_right_of_comp_eq_id S T hST).1,
      (isIso_left_and_right_of_comp_eq_id T S hTS).2⟩
  · rintro ⟨hl, hr⟩
    have hS : homMk S = (ofIso (E := E) ((asIso S.l).symm ≪≫ asIso S.r)).hom := by
      rw [ofIso_hom, ofInflation, homMk_eq_iff]
      exact ⟨Span.mkIso (asIso S.l) (by simp) (by simp)⟩
    rw [hS]
    infer_instance

/-- **Isomorphisms in `Q(E)` are precisely isomorphisms in `C`.** -/
noncomputable def isoEquiv (E : ExactStructure C) (X Y : C) :
    (X ≅ Y) ≃ ((⟨X⟩ : E.QuillenQ) ≅ ⟨Y⟩) :=
  Equiv.ofBijective (ofIso (E := E))
    ⟨ofIso_injective, fun e ↦ by
      obtain ⟨S, hS⟩ := homMk_surjective e.hom
      have hIso : IsIso (homMk S) := hS ▸ inferInstance
      obtain ⟨hl, hr⟩ := (isIso_homMk_iff S).mp hIso
      refine ⟨(asIso S.l).symm ≪≫ asIso S.r, Iso.ext ?_⟩
      rw [← hS, ofIso_hom, ofInflation, homMk_eq_iff]
      exact ⟨Span.mkIso (asIso S.l).symm (by simp) (by simp)⟩⟩

@[simp]
theorem isoEquiv_apply (E : ExactStructure C) {X Y : C} (e : X ≅ Y) :
    isoEquiv E X Y e = ofIso e :=
  (rfl)

/-- **Automorphisms in `Q(E)` are canonically isomorphic as a group to automorphisms in `C`.** -/
noncomputable def autEquiv (E : ExactStructure C) (X : C) :
    Aut X ≃* Aut (⟨X⟩ : E.QuillenQ) where
  toFun e := Aut.of (ofIso e.asIso)
  invFun e := Aut.of ((isoEquiv E X X).symm e.asIso)
  left_inv e := by
    cases e with
    | of e => exact congrArg Aut.of ((isoEquiv E X X).symm_apply_apply e)
  right_inv e := by
    cases e with
    | of e => exact congrArg Aut.of ((isoEquiv E X X).apply_symm_apply e)
  map_mul' e₁ e₂ := by
    apply congrArg Aut.of
    simp

@[simp]
theorem autEquiv_apply_asIso (E : ExactStructure C) {X : C} (e : Aut X) :
    (autEquiv E X e).asIso = ofIso e.asIso :=
  (rfl)

/-! ### Morphisms from a zero object and admissible subobjects -/

/-- **Morphisms from a zero object in `Q(E)` correspond bijectively to admissible subobjects of
the target.** -/
noncomputable def homFromIsZeroEquivSubobject (E : ExactStructure C) {Z : C} (hZ : IsZero Z)
    (Y : C) :
    ((⟨Z⟩ : E.QuillenQ) ⟶ ⟨Y⟩) ≃ { s : Subobject Y // E.IsInflation s.arrow } where
  toFun :=
    homLift
      (fun S : Span E.deflations E.inflations Z Y ↦
        letI : Mono S.r := ConflationClass.IsInflation.mono S.wr
        ⟨Subobject.mk S.r, by
          rw [← Subobject.underlyingIso_hom_comp_eq_mk S.r]
          exact E.inflations.comp_mem _ _ (E.inflations.of_isIso _) S.wr⟩)
      (fun S₁ S₂ ⟨e⟩ ↦ by
        have : Mono S₁.r := ConflationClass.IsInflation.mono S₁.wr
        have : Mono S₂.r := ConflationClass.IsInflation.mono S₂.wr
        apply Subtype.ext
        exact Subobject.mk_eq_mk_of_comm S₁.r S₂.r
          (Span.SpanBicat.apexIso (Wₗ := E.deflations) (Wᵣ := E.inflations)
            (X := ⟨Z⟩) (Y := ⟨Y⟩) e) e.hom.hom_r)
  invFun s :=
    homMk ⟨(s.1 : C), (0 : (s.1 : C) ⟶ Z), s.1.arrow, E.isDeflation_of_isZero_tgt hZ 0, s.2⟩
  left_inv f := by
    refine hom_induction (fun S ↦ ?_) f
    have : Mono S.r := ConflationClass.IsInflation.mono S.wr
    dsimp only
    rw [homLift_homMk, homMk_eq_iff]
    exact ⟨Span.mkIso (Subobject.underlyingIso S.r) (hZ.eq_of_tgt _ _)
      (Subobject.underlyingIso_hom_comp_eq_mk S.r)⟩
  right_inv s := by
    apply Subtype.ext
    exact Subobject.mk_arrow s.1

@[simp]
theorem homFromIsZeroEquivSubobject_homMk_val (E : ExactStructure C) {Z : C} (hZ : IsZero Z)
    {Y : C} (S : Span E.deflations E.inflations Z Y) :
    (homFromIsZeroEquivSubobject E hZ Y (homMk S)).1 =
      @Subobject.mk _ _ _ _ S.r (ConflationClass.IsInflation.mono S.wr) :=
  (rfl)

@[simp]
theorem homFromIsZeroEquivSubobject_symm_apply (E : ExactStructure C) {Z : C} (hZ : IsZero Z)
    {Y : C} (s : { s : Subobject Y // E.IsInflation s.arrow }) :
    (homFromIsZeroEquivSubobject E hZ Y).symm s =
      ofDeflation (0 : (s.1 : C) ⟶ Z) (E.isDeflation_of_isZero_tgt hZ 0) ≫
        ofInflation s.1.arrow s.2 :=
  homMk_eq_ofDeflation_comp_ofInflation _

/-- Under `homFromIsZeroEquivSubobject`, the inflation arrow `0 ↣ Y` corresponds to the zero
subobject `⊥`. -/
@[simp]
theorem homFromIsZeroEquivSubobject_ofInflation_zero (E : ExactStructure C) {Z : C}
    (hZ : IsZero Z) (Y : C) :
    (homFromIsZeroEquivSubobject E hZ Y
      (ofInflation (0 : Z ⟶ Y) (E.isInflation_of_isZero_src hZ 0))).1 = ⊥ := by
  have : Mono (0 : Z ⟶ Y) := ConflationClass.IsInflation.mono (E.isInflation_of_isZero_src hZ 0)
  rw [ofInflation, homFromIsZeroEquivSubobject_homMk_val]
  exact Subobject.mk_eq_bot_iff_zero.mpr rfl

/-- Under `homFromIsZeroEquivSubobject`, the reversed deflation `Y ↠ 0` corresponds to the whole
subobject `⊤`. -/
@[simp]
theorem homFromIsZeroEquivSubobject_ofDeflation_zero (E : ExactStructure C) {Z : C}
    (hZ : IsZero Z) (Y : C) :
    (homFromIsZeroEquivSubobject E hZ Y
      (ofDeflation (0 : Y ⟶ Z) (E.isDeflation_of_isZero_tgt hZ 0))).1 = ⊤ := by
  rw [ofDeflation, homFromIsZeroEquivSubobject_homMk_val]
  exact Subobject.mk_eq_top_of_isIso (𝟙 Y)

/-- The zero subobject arrow `0 ↞ 0 ↣ Y` and the whole subobject arrow `0 ↞ Y ↣ Y` agree in
`E.QuillenQ` if and only if `Y` is a zero object. -/
theorem ofInflation_zero_eq_ofDeflation_zero_iff (E : ExactStructure C) {Z : C}
    (hZ : IsZero Z) (Y : C) :
    ofInflation (0 : Z ⟶ Y) (E.isInflation_of_isZero_src hZ 0) =
      ofDeflation (0 : Y ⟶ Z) (E.isDeflation_of_isZero_tgt hZ 0) ↔ IsZero Y := by
  rw [ofInflation, ofDeflation, homMk_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact hZ.of_iso (Span.SpanBicat.apexIso (Wₗ := E.deflations) (Wᵣ := E.inflations)
      (X := ⟨Z⟩) (Y := ⟨Y⟩) e).symm
  · intro hY
    exact ⟨Span.mkIso (hZ.iso hY) (hZ.eq_of_src _ _) (hY.eq_of_tgt _ _)⟩

end QuillenQ

end TauCeti.ExactStructure
