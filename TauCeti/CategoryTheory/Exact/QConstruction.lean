/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Truncation
public import TauCeti.CategoryTheory.Exact.BaseChange
public import TauCeti.CategoryTheory.Exact.Split
public import Mathlib.CategoryTheory.Bicategory.Span.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Quillen's Q-construction of an exact category

For an exact structure `E` on `C`, Quillen's category `Q(E)` has the objects of `C`. A morphism
`X ⟶ Y` is a span `X ↞ M ↣ Y` whose left leg is a deflation and whose right leg is an inflation,
taken up to an isomorphism of `M` compatible with both legs. The composite of `X ↞ M ↣ Y` and
`Y ↞ N ↣ Z` is the outer span of the pullback `M ×_Y N`: its projection to `M` is a deflation
because deflations are stable under base change, and its projection to `N` is an inflation
because inflations are stable under base change along deflations.

We obtain `Q(E)` as the 1-truncation of Mathlib's bicategory `CategoryTheory.Span.SpanBicat` of
spans whose left legs are deflations and whose right legs are inflations. The classifying space
of `Q(E)` is the space whose loop space is the algebraic K-theory of `E`.

## Main definitions

* `TauCeti.ExactStructure.QConstruction E`: Quillen's category `Q(E)`.
* `TauCeti.ExactStructure.QConstruction.obj`: the object of `C` underlying an object of `Q(E)`.
* `TauCeti.ExactStructure.QConstruction.homMk`: the Q-morphism represented by a span.
* `TauCeti.ExactStructure.QConstruction.homLift`: a function on spans invariant under
  isomorphism of their middle objects, descended to Q-morphisms.
* `TauCeti.ExactStructure.QConstruction.ofInflation`: the Q-morphism `X ⟶ Y` of an inflation
  `X ↣ Y`.
* `TauCeti.ExactStructure.QConstruction.ofDeflation`: the reversed Q-morphism `Y ⟶ X` of a
  deflation `X ↞ Y`.
* `TauCeti.ExactStructure.QConstruction.ofIso`: the isomorphism of the Q-construction attached to
  an isomorphism of `C`.
* `TauCeti.ExactStructure.QConstruction.homFromZeroEquiv`: Q-morphisms out of the zero object
  are the admissible subobjects of the target.

## Main results

* `TauCeti.ExactStructure.QConstruction.homMk_eq_homMk_iff`: two spans represent the same
  Q-morphism exactly when they are isomorphic.
* `TauCeti.ExactStructure.QConstruction.homMk_comp_homMk`: composition is computed by any
  pullback of the inner legs.
* `TauCeti.ExactStructure.QConstruction.ofDeflation_comp_ofInflation`: every Q-morphism factors
  as a reversed deflation followed by an inflation; with `homMk_eq_homMk_iff` this normal form is
  unique up to isomorphism of its middle object.
* `TauCeti.ExactStructure.QConstruction.ofInflation_comp_ofDeflation`: an inflation followed by a
  reversed deflation is rewritten in normal form along a pullback square.
* `TauCeti.ExactStructure.QConstruction.ofInflation_inj` and
  `TauCeti.ExactStructure.QConstruction.ofDeflation_inj`: inflations and reversed deflations embed
  faithfully into the Q-construction.
* `TauCeti.ExactStructure.QConstruction.isIso_homMk_iff`: a Q-morphism is invertible exactly when
  both legs of its span are isomorphisms of `C`.
* `TauCeti.ExactStructure.QConstruction.isIso_iff_exists_iso`: the isomorphisms of the
  Q-construction are exactly those `ofIso e` coming from isomorphisms `e` of `C`.

## References

* Daniel Quillen, *Higher algebraic K-theory: I*, in *Algebraic K-theory I*, Lecture Notes in
  Mathematics **341** (1973), 85--147, §2.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter IV,
  Definition 6.1 and the remarks 6.1.1--6.1.2.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Propositions 2.15 and 2.16.
* The span bicategory `CategoryTheory.Span.SpanBicat` used here is Robin Carlier's
  formalization in Mathlib, `Mathlib/CategoryTheory/Bicategory/Span/Basic.lean`.
-/

public section

namespace TauCeti

open _root_.CategoryTheory Limits Bicategory Span TauCeti.CategoryTheory.Bicategory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

/-- **Quillen's Q-construction** of an exact category. Its objects are those of `C`, and its
morphisms `X ⟶ Y` are the isomorphism classes of spans `X ↞ M ↣ Y` whose left leg is a
deflation and whose right leg is an inflation. -/
def QConstruction : Type u :=
  Truncation (SpanBicat C E.deflations E.inflations)

namespace QConstruction

/-- The category structure on the Q-construction, in which spans compose by pullback. -/
noncomputable instance : Category.{max u v} E.QConstruction :=
  inferInstanceAs (Category (Truncation (SpanBicat C E.deflations E.inflations)))

/-- The object of the Q-construction attached to an object of `C`. -/
noncomputable def mk (X : C) : E.QConstruction :=
  ⟨⟨X⟩⟩

variable {E} in
/-- The object of `C` underlying an object of the Q-construction. -/
noncomputable def obj (Z : E.QConstruction) : C :=
  Z.as.of

/-- The object of `C` underlying `mk E X` is `X`. -/
@[simp]
theorem obj_mk (X : C) : (mk E X).obj = X :=
  (rfl)

/-- Every object of the Q-construction is `mk E` of its underlying object. -/
@[simp]
theorem mk_obj (Z : E.QConstruction) : mk E Z.obj = Z :=
  (rfl)

/-- Induction principle for objects of the Q-construction: a property holding for every object
coming from `C` holds for every object. -/
@[elab_as_elim]
theorem obj_induction {motive : E.QConstruction → Prop} (h : ∀ X : C, motive (mk E X))
    (Z : E.QConstruction) : motive Z :=
  mk_obj E Z ▸ h Z.obj

/-- Every object of the Q-construction comes from an object of `C`. -/
theorem mk_surjective : Function.Surjective (mk E) :=
  fun Z => ⟨Z.obj, mk_obj E Z⟩

/-- Distinct objects of `C` give distinct objects of the Q-construction. -/
theorem mk_injective : Function.Injective (mk E) :=
  fun _ _ h => by simpa using congrArg obj h

variable {E}

/-- The Q-morphism `X ⟶ Y` represented by a span `X ↞ M ↣ Y`, whose left leg `p` is a deflation
and whose right leg `i` is an inflation. -/
noncomputable def homMk {X Y M : C} (p : M ⟶ X) (hp : E.IsDeflation p) (i : M ⟶ Y)
    (hi : E.IsInflation i) : mk E X ⟶ mk E Y :=
  Truncation.homMk (SpanBicat.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) p i hp hi)

/-- Every Q-morphism is represented by a span. -/
theorem homMk_surjective {X Y : C} (f : mk E X ⟶ mk E Y) :
    ∃ (M : C) (p : M ⟶ X) (hp : E.IsDeflation p) (i : M ⟶ Y) (hi : E.IsInflation i),
      homMk p hp i hi = f := by
  obtain ⟨S, rfl⟩ := Truncation.homMk_surjective f
  exact ⟨S.apex, S.l, S.wl, S.r, S.wr, (rfl)⟩

/-- Induction principle for Q-morphisms: a property holding for the Q-morphism of every span holds
for every Q-morphism. -/
@[elab_as_elim]
theorem hom_induction {X Y : C} {motive : (mk E X ⟶ mk E Y) → Prop}
    (h : ∀ (M : C) (p : M ⟶ X) (hp : E.IsDeflation p) (i : M ⟶ Y) (hi : E.IsInflation i),
      motive (homMk p hp i hi))
    (f : mk E X ⟶ mk E Y) : motive f := by
  obtain ⟨M, p, hp, i, hi, rfl⟩ := homMk_surjective f
  exact h M p hp i hi

/-- A function on spans `X ↞ M ↣ Y` that takes the same value on spans related by an isomorphism
of their middle objects compatible with both legs descends to the Q-morphisms `X ⟶ Y`. -/
noncomputable def homLift {X Y : C} {α : Sort*}
    (F : ∀ (M : C) (p : M ⟶ X), E.IsDeflation p → ∀ i : M ⟶ Y, E.IsInflation i → α)
    (hF : ∀ ⦃M M' : C⦄ (e : M ≅ M') ⦃p : M ⟶ X⦄ (hp : E.IsDeflation p) ⦃i : M ⟶ Y⦄
      (hi : E.IsInflation i) ⦃p' : M' ⟶ X⦄ (hp' : E.IsDeflation p') ⦃i' : M' ⟶ Y⦄
      (hi' : E.IsInflation i'), e.hom ≫ p' = p → e.hom ≫ i' = i →
        F M p hp i hi = F M' p' hp' i' hi') :
    (mk E X ⟶ mk E Y) → α :=
  Truncation.homLift (a := (⟨X⟩ : SpanBicat C E.deflations E.inflations)) (b := ⟨Y⟩)
    (fun S => F S.apex S.l S.wl S.r S.wr)
    fun _ _ e => hF (SpanBicat.apexIso e) _ _ _ _ e.hom.hom_l e.hom.hom_r

/-- Evaluating a function descended with `homLift` on the Q-morphism of a span returns its value
on that span. -/
@[simp]
theorem homLift_homMk {X Y M : C} {α : Sort*}
    (F : ∀ (M : C) (p : M ⟶ X), E.IsDeflation p → ∀ i : M ⟶ Y, E.IsInflation i → α)
    (hF : ∀ ⦃M M' : C⦄ (e : M ≅ M') ⦃p : M ⟶ X⦄ (hp : E.IsDeflation p) ⦃i : M ⟶ Y⦄
      (hi : E.IsInflation i) ⦃p' : M' ⟶ X⦄ (hp' : E.IsDeflation p') ⦃i' : M' ⟶ Y⦄
      (hi' : E.IsInflation i'), e.hom ≫ p' = p → e.hom ≫ i' = i →
        F M p hp i hi = F M' p' hp' i' hi')
    (p : M ⟶ X) (hp : E.IsDeflation p) (i : M ⟶ Y) (hi : E.IsInflation i) :
    homLift F hF (homMk p hp i hi) = F M p hp i hi :=
  Truncation.homLift_homMk _ _ _

/-- Two spans represent the same Q-morphism exactly when there is an isomorphism of their middle
objects compatible with both legs. -/
theorem homMk_eq_homMk_iff {X Y M M' : C} {p : M ⟶ X} {hp : E.IsDeflation p} {i : M ⟶ Y}
    {hi : E.IsInflation i} {p' : M' ⟶ X} {hp' : E.IsDeflation p'} {i' : M' ⟶ Y}
    {hi' : E.IsInflation i'} :
    homMk p hp i hi = homMk p' hp' i' hi' ↔ ∃ e : M ≅ M', e.hom ≫ p' = p ∧ e.hom ≫ i' = i := by
  refine Truncation.homMk_eq_homMk_iff.trans ⟨fun ⟨e⟩ => ?_, fun ⟨e, hl, hr⟩ => ?_⟩
  · exact ⟨SpanBicat.apexIso e, e.hom.hom_l, e.hom.hom_r⟩
  · exact ⟨SpanBicat.mkIso₂ e hl hr⟩

/-- The identity Q-morphism is represented by the span of two identities. -/
theorem homMk_id (X : C) :
    homMk (𝟙 X) (E.isDeflation_id X) (𝟙 X) (E.isInflation_id X) = 𝟙 (mk E X) :=
  Truncation.homMk_id (B := SpanBicat C E.deflations E.inflations) ⟨X⟩

/-- A span whose two legs are the same isomorphism represents an identity Q-morphism. -/
@[simp]
theorem homMk_self {X M : C} (e : M ⟶ X) [IsIso e] {hp : E.IsDeflation e}
    {hi : E.IsInflation e} : homMk e hp e hi = 𝟙 (mk E X) := by
  rw [← homMk_id, homMk_eq_homMk_iff]
  exact ⟨asIso e, by simp, by simp⟩

/-- **Composition in the Q-construction.** The composite of `X ↞ M ↣ Y` and `Y ↞ N ↣ Z` is
represented by the outer span of any pullback `P` of `M ↣ Y ↞ N`. -/
@[reassoc]
theorem homMk_comp_homMk {X Y Z M N P : C} {p : M ⟶ X} (hp : E.IsDeflation p) {i : M ⟶ Y}
    (hi : E.IsInflation i) {q : N ⟶ Y} (hq : E.IsDeflation q) {j : N ⟶ Z}
    (hj : E.IsInflation j) {a : P ⟶ M} {b : P ⟶ N} (sq : IsPullback a b i q) :
    homMk p hp i hi ≫ homMk q hq j hj =
      homMk (a ≫ p) (E.isDeflation_comp a p
          (E.isStableUnderBaseChange_deflations.of_isPullback sq.flip hq) hp)
        (b ≫ j) (E.isInflation_comp b j (E.isInflation_of_isPullback sq.flip hi hq) hj) := by
  let S₁ : (⟨X⟩ : SpanBicat C E.deflations E.inflations) ⟶ ⟨Y⟩ := SpanBicat.mkHom p i hp hi
  let S₂ : (⟨Y⟩ : SpanBicat C E.deflations E.inflations) ⟶ ⟨Z⟩ := SpanBicat.mkHom q j hq hj
  refine (Truncation.homMk_comp S₁ S₂).symm.trans (Truncation.homMk_eq_of_iso ?_)
  refine SpanBicat.mkIso₂
    { hom := sq.lift (SpanBicat.πₗ S₁ S₂) (SpanBicat.πᵣ S₁ S₂) (SpanBicat.comp_comm S₁ S₂)
      inv := SpanBicat.compLiftApex (S₁ := S₁) (S₂ := S₂) a b sq.w
      hom_inv_id := SpanBicat.comp_hom_ext_apex (by simp) (by simp)
      inv_hom_id := sq.hom_ext (by simp) (by simp) } ?_ ?_
  · simp [S₁]
  · simp [S₂]

/-- The Q-morphism `X ⟶ Y` of an inflation `i : X ↣ Y`, represented by the span `X ↞ X ↣ Y`. -/
noncomputable def ofInflation {X Y : C} (i : X ⟶ Y) (hi : E.IsInflation i) : mk E X ⟶ mk E Y :=
  homMk (𝟙 X) (E.isDeflation_id X) i hi

/-- The reversed Q-morphism `Y ⟶ X` of a deflation `p : X ↠ Y`, represented by the span
`Y ↞ X ↣ X`. -/
noncomputable def ofDeflation {X Y : C} (p : X ⟶ Y) (hp : E.IsDeflation p) : mk E Y ⟶ mk E X :=
  homMk p hp (𝟙 X) (E.isInflation_id X)

/-- The Q-morphism of the identity inflation is the identity. -/
@[simp]
theorem ofInflation_id (X : C) : ofInflation (𝟙 X) (E.isInflation_id X) = 𝟙 (mk E X) :=
  homMk_id X

/-- The reversed Q-morphism of the identity deflation is the identity. -/
@[simp]
theorem ofDeflation_id (X : C) : ofDeflation (𝟙 X) (E.isDeflation_id X) = 𝟙 (mk E X) :=
  homMk_id X

/-- The Q-morphism of a composite of inflations is the composite of their Q-morphisms. -/
@[simp]
theorem ofInflation_comp {X Y Z : C} {i : X ⟶ Y} (hi : E.IsInflation i) {j : Y ⟶ Z}
    (hj : E.IsInflation j) :
    ofInflation (i ≫ j) (E.isInflation_comp i j hi hj) = ofInflation i hi ≫ ofInflation j hj := by
  rw [ofInflation, ofInflation, ofInflation, homMk_comp_homMk _ _ _ _ (IsPullback.id_horiz i)]
  simp

/-- The reversed Q-morphism of a composite of deflations is the composite of their reversed
Q-morphisms, in the opposite order. -/
@[simp]
theorem ofDeflation_comp {X Y Z : C} {p : X ⟶ Y} (hp : E.IsDeflation p) {q : Y ⟶ Z}
    (hq : E.IsDeflation q) :
    ofDeflation (p ≫ q) (E.isDeflation_comp p q hp hq) = ofDeflation q hq ≫ ofDeflation p hp := by
  rw [ofDeflation, ofDeflation, ofDeflation, homMk_comp_homMk _ _ _ _ (IsPullback.id_vert p)]
  simp

/-- **Normal form of a Q-morphism.** The Q-morphism of a span `X ↞ M ↣ Y` is the reversed
deflation `X ⟶ M` followed by the inflation `M ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem ofDeflation_comp_ofInflation {X Y M : C} {p : M ⟶ X} (hp : E.IsDeflation p)
    {i : M ⟶ Y} (hi : E.IsInflation i) : ofDeflation p hp ≫ ofInflation i hi = homMk p hp i hi := by
  rw [ofDeflation, ofInflation, homMk_comp_homMk _ _ _ _ (IsPullback.id_vert (𝟙 M))]
  simp

/-- An inflation followed by a reversed deflation is the reversed deflation followed by the
inflation of any pullback square of the two. -/
@[reassoc]
theorem ofInflation_comp_ofDeflation {X Y N P : C} {i : X ⟶ Y} (hi : E.IsInflation i)
    {q : N ⟶ Y} (hq : E.IsDeflation q) {a : P ⟶ X} {b : P ⟶ N} (sq : IsPullback a b i q) :
    ofInflation i hi ≫ ofDeflation q hq =
      ofDeflation a (E.isStableUnderBaseChange_deflations.of_isPullback sq.flip hq) ≫
        ofInflation b (E.isInflation_of_isPullback sq.flip hi hq) := by
  rw [ofInflation, ofDeflation, homMk_comp_homMk _ _ _ _ sq, ofDeflation_comp_ofInflation]
  simp

/-- A span whose deflation leg is an identity represents the Q-morphism of its inflation leg. -/
@[simp]
theorem homMk_id_left {X Y : C} (hp : E.IsDeflation (𝟙 X)) (i : X ⟶ Y) (hi : E.IsInflation i) :
    homMk (𝟙 X) hp i hi = ofInflation i hi :=
  (rfl)

/-- A span whose inflation leg is an identity represents the reversed Q-morphism of its deflation
leg. -/
@[simp]
theorem homMk_id_right {X Y : C} (p : X ⟶ Y) (hp : E.IsDeflation p) (hi : E.IsInflation (𝟙 X)) :
    homMk p hp (𝟙 X) hi = ofDeflation p hp :=
  (rfl)

/-- Distinct inflations give distinct Q-morphisms. -/
@[simp]
theorem ofInflation_inj {X Y : C} {i i' : X ⟶ Y} {hi : E.IsInflation i}
    {hi' : E.IsInflation i'} : ofInflation i hi = ofInflation i' hi' ↔ i = i' := by
  rw [ofInflation, ofInflation, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, he, rfl⟩
    have he' : e.hom = 𝟙 X := by simpa using he
    simp [he']
  · rintro rfl
    exact ⟨Iso.refl X, by simp, by simp⟩

/-- Distinct deflations give distinct reversed Q-morphisms. -/
@[simp]
theorem ofDeflation_inj {X Y : C} {p p' : X ⟶ Y} {hp : E.IsDeflation p}
    {hp' : E.IsDeflation p'} : ofDeflation p hp = ofDeflation p' hp' ↔ p = p' := by
  rw [ofDeflation, ofDeflation, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, rfl, he⟩
    have he' : e.hom = 𝟙 X := by simpa using he
    simp [he']
  · rintro rfl
    exact ⟨Iso.refl X, by simp, by simp⟩

/-- A reversed deflation followed by the Q-morphism of a span is the Q-morphism of the span whose
deflation leg is the composite deflation. -/
@[reassoc (attr := simp)]
theorem ofDeflation_comp_homMk {X X' Y M : C} {q : X' ⟶ X} (hq : E.IsDeflation q) {p : M ⟶ X'}
    (hp : E.IsDeflation p) {i : M ⟶ Y} (hi : E.IsInflation i) :
    ofDeflation q hq ≫ homMk p hp i hi = homMk (p ≫ q) (E.isDeflation_comp p q hp hq) i hi := by
  rw [ofDeflation, homMk_comp_homMk _ _ _ _ (IsPullback.id_vert p)]
  simp

/-- The Q-morphism of a span followed by an inflation is the Q-morphism of the span whose
inflation leg is the composite inflation. -/
@[reassoc (attr := simp)]
theorem homMk_comp_ofInflation {X Y Y' M : C} {p : M ⟶ X} (hp : E.IsDeflation p) {i : M ⟶ Y}
    (hi : E.IsInflation i) {j : Y ⟶ Y'} (hj : E.IsInflation j) :
    homMk p hp i hi ≫ ofInflation j hj = homMk p hp (i ≫ j) (E.isInflation_comp i j hi hj) := by
  rw [ofInflation, homMk_comp_homMk _ _ _ _ (IsPullback.id_horiz i)]
  simp

/-- A span represents an identity Q-morphism exactly when its two legs are one and the same
isomorphism. -/
theorem homMk_eq_id_iff {X M : C} {p i : M ⟶ X} {hp : E.IsDeflation p} {hi : E.IsInflation i} :
    homMk p hp i hi = 𝟙 (mk E X) ↔ IsIso p ∧ p = i := by
  rw [← homMk_id, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, hl, hr⟩
    simp only [Category.comp_id] at hl hr
    subst hl hr
    exact ⟨inferInstance, rfl⟩
  · rintro ⟨_, rfl⟩
    exact ⟨asIso p, by simp, by simp⟩

/-- If the Q-morphism of an inflation `i` has a section `f`, that is `f ≫ ofInflation i = 𝟙`,
then `i` is an isomorphism. -/
private theorem isIso_of_comp_ofInflation_eq_id {X Y : C} {i : X ⟶ Y} (hi : E.IsInflation i)
    {f : mk E Y ⟶ mk E X} (hf : f ≫ ofInflation i hi = 𝟙 _) : IsIso i := by
  obtain ⟨N, p, hp, j, hj, rfl⟩ := homMk_surjective f
  rw [ofInflation, homMk_comp_homMk _ _ _ _ (IsPullback.id_horiz j), ← homMk_id,
    homMk_eq_homMk_iff] at hf
  obtain ⟨e, -, he⟩ := hf
  have := hi.mono
  have : IsSplitEpi i := ⟨⟨{ section_ := e.inv ≫ j, id := by simp [← he] }⟩⟩
  exact isIso_of_mono_of_isSplitEpi i

/-- If the reversed Q-morphism of a deflation `p` has a retraction `f`, that is
`ofDeflation p ≫ f = 𝟙`, then `p` is an isomorphism. -/
private theorem isIso_of_ofDeflation_comp_eq_id {X Y : C} {p : X ⟶ Y} (hp : E.IsDeflation p)
    {f : mk E X ⟶ mk E Y} (hf : ofDeflation p hp ≫ f = 𝟙 _) : IsIso p := by
  obtain ⟨N, q, hq, j, hj, rfl⟩ := homMk_surjective f
  rw [ofDeflation, homMk_comp_homMk _ _ _ _ (IsPullback.id_vert q), ← homMk_id,
    homMk_eq_homMk_iff] at hf
  obtain ⟨e, he, -⟩ := hf
  rw [Category.comp_id] at he
  have := hq.epi
  have : IsSplitMono q :=
    ⟨⟨{ retraction := p ≫ e.inv, id := by rw [← Category.assoc, ← he, Iso.hom_inv_id] }⟩⟩
  have := isIso_of_epi_of_isSplitMono q
  have : IsIso (q ≫ p) := he ▸ inferInstance
  exact IsIso.of_isIso_comp_left q p

/-- **Isomorphisms of the Q-construction come from isomorphisms of `C`.** The Q-morphism of a
span is invertible exactly when both legs of the span are isomorphisms. -/
@[simp]
theorem isIso_homMk_iff {X Y M : C} {p : M ⟶ X} {hp : E.IsDeflation p} {i : M ⟶ Y}
    {hi : E.IsInflation i} : IsIso (homMk p hp i hi) ↔ IsIso p ∧ IsIso i := by
  constructor
  · intro h
    rw [← ofDeflation_comp_ofInflation] at h
    exact ⟨isIso_of_ofDeflation_comp_eq_id hp
      (f := ofInflation i hi ≫ inv (ofDeflation p hp ≫ ofInflation i hi))
      (by rw [← Category.assoc, IsIso.hom_inv_id]),
      isIso_of_comp_ofInflation_eq_id hi
      (f := inv (ofDeflation p hp ≫ ofInflation i hi) ≫ ofDeflation p hp)
      (by rw [Category.assoc, IsIso.inv_hom_id])⟩
  · rintro ⟨_, _⟩
    have hi' : E.IsInflation p := E.inflations.of_isIso p
    have hp' : E.IsDeflation i := E.deflations.of_isIso i
    refine ⟨homMk i hp' p hi', ?_, ?_⟩
    · rw [homMk_comp_homMk _ _ _ _ (IsPullback.of_horiz_isIso (fst := 𝟙 M) (snd := 𝟙 M) ⟨rfl⟩)]
      simp
    · rw [homMk_comp_homMk _ _ _ _ (IsPullback.of_horiz_isIso (fst := 𝟙 M) (snd := 𝟙 M) ⟨rfl⟩)]
      simp

/-- The Q-morphism of an inflation is invertible exactly when the inflation is. -/
@[simp]
theorem isIso_ofInflation_iff {X Y : C} {i : X ⟶ Y} {hi : E.IsInflation i} :
    IsIso (ofInflation i hi) ↔ IsIso i :=
  isIso_homMk_iff.trans ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩

/-- The reversed Q-morphism of a deflation is invertible exactly when the deflation is. -/
@[simp]
theorem isIso_ofDeflation_iff {X Y : C} {p : X ⟶ Y} {hp : E.IsDeflation p} :
    IsIso (ofDeflation p hp) ↔ IsIso p :=
  isIso_homMk_iff.trans ⟨fun h => h.1, fun h => ⟨h, inferInstance⟩⟩

/-- The isomorphism of the Q-construction attached to an isomorphism `e` of `C`: the Q-morphism
of the inflation `e.hom`, with inverse the Q-morphism of the inflation `e.inv`. -/
noncomputable def ofIso {X Y : C} (e : X ≅ Y) : mk E X ≅ mk E Y where
  hom := ofInflation e.hom (E.inflations.of_isIso _)
  inv := ofInflation e.inv (E.inflations.of_isIso _)
  hom_inv_id := by simp [← ofInflation_comp]
  inv_hom_id := by simp [← ofInflation_comp]

@[simp]
theorem ofIso_hom {X Y : C} (e : X ≅ Y) :
    (ofIso e : mk E X ≅ mk E Y).hom = ofInflation e.hom (E.inflations.of_isIso _) :=
  (rfl)

@[simp]
theorem ofIso_inv {X Y : C} (e : X ≅ Y) :
    (ofIso e : mk E X ≅ mk E Y).inv = ofInflation e.inv (E.inflations.of_isIso _) :=
  (rfl)

/-- `ofIso` sends the identity isomorphism to the identity. -/
@[simp]
theorem ofIso_refl (X : C) : ofIso (Iso.refl X) = Iso.refl (mk E X) := by
  ext
  exact ofInflation_id X

/-- `ofIso` is compatible with composition of isomorphisms. -/
@[simp]
theorem ofIso_trans {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z) :
    ofIso (e ≪≫ f) = (ofIso e ≪≫ ofIso f : mk E X ≅ mk E Z) := by
  ext
  exact ofInflation_comp _ _

/-- `ofIso` is compatible with inverses of isomorphisms. -/
@[simp]
theorem ofIso_symm {X Y : C} (e : X ≅ Y) :
    ofIso e.symm = (ofIso e : mk E X ≅ mk E Y).symm := by
  ext
  simp

/-- For an isomorphism `e` of `C`, the reversed deflation `e.hom` is the inverse of `ofIso e`. -/
@[simp]
theorem ofDeflation_hom {X Y : C} (e : X ≅ Y) :
    ofDeflation e.hom (E.deflations.of_isIso _) = (ofIso e : mk E X ≅ mk E Y).inv := by
  rw [ofDeflation, ofIso_inv, ofInflation, homMk_eq_homMk_iff]
  exact ⟨e, by simp, by simp⟩

/-- For an isomorphism `e` of `C`, the reversed deflation `e.inv` is `ofIso e`. -/
@[simp]
theorem ofDeflation_inv {X Y : C} (e : X ≅ Y) :
    ofDeflation e.inv (E.deflations.of_isIso _) = (ofIso e : mk E X ≅ mk E Y).hom := by
  rw [ofDeflation, ofIso_hom, ofInflation, homMk_eq_homMk_iff]
  exact ⟨e.symm, by simp, by simp⟩

/-- **The isomorphisms of the Q-construction are those of `C`.** A Q-morphism is an isomorphism
exactly when it is `ofIso e` for an isomorphism `e` of `C`. -/
theorem isIso_iff_exists_iso {X Y : C} (f : mk E X ⟶ mk E Y) :
    IsIso f ↔ ∃ e : X ≅ Y, f = (ofIso e).hom := by
  refine ⟨fun hf => ?_, fun ⟨e, he⟩ => he ▸ inferInstance⟩
  obtain ⟨M, p, hp, i, hi, rfl⟩ := homMk_surjective f
  obtain ⟨_, _⟩ := isIso_homMk_iff.1 hf
  refine ⟨asIso (inv p ≫ i), ?_⟩
  rw [ofIso_hom, ofInflation, homMk_eq_homMk_iff]
  exact ⟨asIso p, by simp, by simp⟩

open ZeroObject

/-- The admissible subobject of `Y` attached to a Q-morphism `0 ⟶ Y`: the image of the right
leg of any span representing it. -/
private noncomputable def toAdmissibleSubobject {Y : C} :
    (mk E 0 ⟶ mk E Y) → {P : Subobject Y // E.IsInflation P.arrow} :=
  homLift
    (fun _ _ _ i hi =>
      have := hi.mono
      ⟨Subobject.mk i, by
        rw [← Subobject.underlyingIso_hom_comp_eq_mk]
        exact E.isInflation_comp _ _ (E.inflations.of_isIso _) hi⟩)
    fun _ _ e _ _ _ hi _ _ _ hi' _ he => by
      have := hi.mono
      have := hi'.mono
      exact Subtype.ext (Subobject.mk_eq_mk_of_comm _ _ e he)

private theorem toAdmissibleSubobject_homMk {Y M : C} {p : M ⟶ 0} {hp : E.IsDeflation p}
    {i : M ⟶ Y} {hi : E.IsInflation i} :
    haveI := hi.mono
    (toAdmissibleSubobject (homMk p hp i hi) : Subobject Y) = Subobject.mk i := by
  rw [toAdmissibleSubobject, homLift_homMk]

/-- **Q-morphisms out of zero are admissible subobjects.** A Q-morphism `0 ⟶ Y` is the same as a
subobject of `Y` whose inclusion is an inflation: the span `0 ↞ M ↣ Y` corresponds to the
subobject `M ↣ Y`. -/
noncomputable def homFromZeroEquiv (Y : C) :
    (mk E 0 ⟶ mk E Y) ≃ {P : Subobject Y // E.IsInflation P.arrow} where
  toFun := toAdmissibleSubobject
  invFun P :=
    homMk (0 : (P.val : C) ⟶ 0) (E.isDeflation_zero _) P.val.arrow P.property
  left_inv f := by
    obtain ⟨M, p, hp, i, hi, rfl⟩ := homMk_surjective f
    have := hi.mono
    refine homMk_eq_homMk_iff.2 ⟨eqToIso (congrArg Subobject.underlying.obj
      toAdmissibleSubobject_homMk) ≪≫ Subobject.underlyingIso i, ?_, ?_⟩
    · exact (isZero_zero C).eq_of_tgt _ _
    · rw [Iso.trans_hom, eqToIso.hom, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
      exact Subobject.arrow_congr _ _ toAdmissibleSubobject_homMk
  right_inv P := Subtype.ext <| by
    rw [toAdmissibleSubobject_homMk]
    exact Subobject.mk_arrow P.val

/-- The equivalence `homFromZeroEquiv` sends the Q-morphism of a span `0 ↞ M ↣ Y` to the
subobject of `Y` cut out by its inflation leg `M ↣ Y`. -/
@[simp]
theorem homFromZeroEquiv_homMk {Y M : C} {p : M ⟶ 0} {hp : E.IsDeflation p} {i : M ⟶ Y}
    {hi : E.IsInflation i} :
    haveI := hi.mono
    (homFromZeroEquiv Y (homMk p hp i hi) : Subobject Y) = Subobject.mk i :=
  toAdmissibleSubobject_homMk

/-- The inverse of `homFromZeroEquiv` sends an admissible subobject `P ↣ Y` to the Q-morphism of
the span `0 ↞ P ↣ Y`. -/
@[simp]
theorem homFromZeroEquiv_symm_apply {Y : C} (P : {P : Subobject Y // E.IsInflation P.arrow}) :
    (homFromZeroEquiv Y).symm P =
      homMk (0 : (P.val : C) ⟶ 0) (E.isDeflation_zero _) P.val.arrow
        P.property :=
  (rfl)

/-- `homFromZeroEquiv` sends the Q-morphism of an inflation `0 ↣ Y` to the zero subobject `⊥` of
`Y`. -/
@[simp]
theorem homFromZeroEquiv_ofInflation {Y : C} {i : 0 ⟶ Y} {hi : E.IsInflation i} :
    (homFromZeroEquiv Y (ofInflation i hi) : Subobject Y) = ⊥ :=
  haveI := hi.mono
  homFromZeroEquiv_homMk.trans (Subobject.mk_eq_bot_iff_zero.2 ((isZero_zero C).eq_of_src _ _))

/-- `homFromZeroEquiv` sends the reversed Q-morphism of a deflation `Y ↠ 0` to the whole
subobject `⊤` of `Y`. -/
@[simp]
theorem homFromZeroEquiv_ofDeflation {Y : C} {p : Y ⟶ 0} {hp : E.IsDeflation p} :
    (homFromZeroEquiv Y (ofDeflation p hp) : Subobject Y) = ⊤ :=
  homFromZeroEquiv_homMk.trans (Subobject.top_eq_id Y).symm

/-- The two Q-morphisms `0 ⟶ Y` given by the zero subobject `0 ↣ Y` and by the whole subobject
`Y ↣ Y` agree only when `Y` is a zero object. -/
theorem ofInflation_zero_eq_ofDeflation_zero_iff (Y : C) :
    ofInflation (0 : 0 ⟶ Y) (E.isInflation_zero Y) = ofDeflation (0 : Y ⟶ 0) (E.isDeflation_zero Y)
      ↔ IsZero Y := by
  rw [ofInflation, ofDeflation, homMk_eq_homMk_iff]
  constructor
  · rintro ⟨e, -, he⟩
    simpa [IsZero.iff_id_eq_zero] using congrArg (e.inv ≫ ·) he
  · intro hY
    exact ⟨(isZero_zero C).iso hY, (isZero_zero C).eq_of_src _ _, hY.eq_of_tgt _ _⟩

end QConstruction

end ExactStructure

end TauCeti
