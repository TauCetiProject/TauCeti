/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Internal equivalence relations through their points

A pair of parallel morphisms `p₁ p₂ : R ⟶ X` admitting a pullback of `p₂` and `p₁` is an internal
equivalence relation (`CategoryTheory.IsEquivalenceRelation`) exactly when it is jointly monic
and, for every object `T`, the relation on `T ⟶ X` relating `r ≫ p₁` to `r ≫ p₂` for `r : T ⟶ R`
is an equivalence relation (Stacks, Definition 39.3.1 (022P), for schemes).

## Main results

* `TauCeti.CategoryTheory.Rel.ofPairHom p₁ p₂ T`: the relation on `T ⟶ X` given by `p₁` and `p₂`,
  characterized by `TauCeti.CategoryTheory.Rel.ofPairHom_iff`.
* `CategoryTheory.EquivalenceRelation.equivalence_ofPairHom`: an internal equivalence relation
  induces an equivalence relation on `T ⟶ X` for every `T`.
* `TauCeti.CategoryTheory.isEquivalenceRelation_iff`: if the pullback of `p₂` and `p₁` exists,
  then `p₁, p₂` is an internal equivalence relation if and only if it is jointly monic and
  `Rel.ofPairHom p₁ p₂ T` is an equivalence for every `T`.
* `CategoryTheory.IsEquivalenceRelation.refl`, `.symm`, `.trans`: chosen reflexivity, symmetry
  and transitivity morphisms of an internal equivalence relation, with their laws.
* `CategoryTheory.IsEquivalenceRelation.swap`: exchanging the projections of an internal
  equivalence relation gives an internal equivalence relation.
* `CategoryTheory.IsKernelPair.isEquivalenceRelation`: a kernel pair is an internal equivalence
  relation, and `CategoryTheory.IsEquivalenceRelation.id`: so is the diagonal.
* `TauCeti.CategoryTheory.restrictRel f p₁ p₂`: the restriction `R ×_{X × X} (Y × Y)` of a pair
  `p₁ p₂ : R ⟶ X` along `f : Y ⟶ X`, with projections `restrictRel.fst` and `restrictRel.snd`.
  It relates `a` to `b` exactly when `p₁, p₂` relates `f a` to `f b`
  (`TauCeti.CategoryTheory.restrictRel.ofPairHom_iff`).
* `CategoryTheory.IsEquivalenceRelation.restrictRel`: the restriction of an internal equivalence
  relation is an internal equivalence relation (Stacks, Lemma 39.3.2 (02V8), for schemes), and
  `CategoryTheory.IsKernelPair.restrictRel`: restricting the kernel pair of `φ` along `f` gives
  the kernel pair of `f ≫ φ`.

## References

* [Stacks Project, Definition 39.3.1](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Lemma 39.3.2](https://stacks.math.columbia.edu/tag/02V8)
* [Stacks Project, Definition 39.3.3](https://stacks.math.columbia.edu/tag/02V9)
-/

public section

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory Limits

variable {C : Type*} [Category* C] {R X : C}

/-- The relation on morphisms `T ⟶ X` given by a pair `p₁ p₂ : R ⟶ X`: `a` is related to `b` when
`a = r ≫ p₁` and `b = r ≫ p₂` for some `r : T ⟶ R`. -/
def Rel.ofPairHom (p₁ p₂ : R ⟶ X) (T : C) (a b : T ⟶ X) : Prop :=
  ∃ r : T ⟶ R, r ≫ p₁ = a ∧ r ≫ p₂ = b

variable {p₁ p₂ : R ⟶ X}

/-- `a` and `b` are related by `Rel.ofPairHom p₁ p₂ T` when `a = r ≫ p₁` and `b = r ≫ p₂` for some
`r : T ⟶ R`. -/
theorem Rel.ofPairHom_iff {T : C} {a b : T ⟶ X} :
    Rel.ofPairHom p₁ p₂ T a b ↔ ∃ r : T ⟶ R, r ≫ p₁ = a ∧ r ≫ p₂ = b := (Iff.rfl)

end TauCeti.CategoryTheory

namespace CategoryTheory

open Limits TauCeti.CategoryTheory

variable {C : Type*} [Category* C] {R X : C} {p₁ p₂ : R ⟶ X}

/-- The relation on morphisms `T ⟶ X` given by an internal equivalence relation is an equivalence
relation. -/
theorem EquivalenceRelation.equivalence_ofPairHom (e : EquivalenceRelation p₁ p₂) (T : C) :
    _root_.Equivalence (Rel.ofPairHom p₁ p₂ T) where
  refl a := ⟨a ≫ e.r, by simp [e.reflexivity₁], by simp [e.reflexivity₂]⟩
  symm := fun ⟨r, h₁, h₂⟩ ↦ ⟨r ≫ e.s, by simp [e.symmetry₁, h₂], by simp [e.symmetry₂, h₁]⟩
  trans := fun ⟨r, h₁, h₂⟩ ⟨r', h₁', h₂'⟩ ↦
    ⟨PullbackCone.IsLimit.lift e.isLimit r r' (h₂.trans h₁'.symm) ≫ e.t,
      by simp [e.transitivity₁, h₁], by simp [e.transitivity₂, h₂']⟩

end CategoryTheory

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory Limits

variable {C : Type*} [Category* C] {R X : C} {p₁ p₂ : R ⟶ X}

/-- A pair of parallel morphisms `p₁ p₂ : R ⟶ X` with a pullback of `p₂` and `p₁` is an internal
equivalence relation if and only if it is jointly monic and, for every `T`, the induced relation
on `T ⟶ X` is an equivalence relation. -/
theorem isEquivalenceRelation_iff [HasPullback p₂ p₁] :
    IsEquivalenceRelation p₁ p₂ ↔
      JointlyMono₂ p₁ p₂ ∧ ∀ T : C, _root_.Equivalence (Rel.ofPairHom p₁ p₂ T) := by
  refine ⟨fun ⟨⟨e⟩⟩ ↦ ⟨e.toJointlyMono₂, e.equivalence_ofPairHom⟩, fun ⟨hm, h⟩ ↦ ?_⟩
  obtain ⟨r, hr₁, hr₂⟩ := (h X).refl (𝟙 X)
  obtain ⟨s, hs₁, hs₂⟩ := (h R).symm ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
  obtain ⟨t, ht₁, ht₂⟩ := (h (pullback p₂ p₁)).trans
    ⟨pullback.fst p₂ p₁, rfl, rfl⟩ ⟨pullback.snd p₂ p₁, pullback.condition.symm, rfl⟩
  exact ⟨⟨{ toJointlyMono₂ := hm
            r := r
            s := s
            c := PullbackCone.mk _ _ pullback.condition
            isLimit := pullbackIsPullback p₂ p₁
            t := t
            reflexivity₁ := hr₁
            reflexivity₂ := hr₂
            symmetry₁ := hs₁
            symmetry₂ := hs₂
            transitivity₁ := ht₁
            transitivity₂ := ht₂ }⟩⟩

end TauCeti.CategoryTheory

namespace CategoryTheory

open Limits TauCeti.CategoryTheory

variable {C : Type*} [Category* C] {R X : C} {p₁ p₂ : R ⟶ X}

/-- The projections of an internal equivalence relation are jointly monic. -/
instance IsEquivalenceRelation.jointlyMono₂ [h : IsEquivalenceRelation p₁ p₂] :
    JointlyMono₂ p₁ p₂ :=
  h.nonempty_equivalenceRelation.some.toJointlyMono₂

/-- The pullback of the second projection of an internal equivalence relation and the first
exists. -/
instance IsEquivalenceRelation.hasPullback_symm [h : IsEquivalenceRelation p₁ p₂] :
    HasPullback p₂ p₁ :=
  let e := h.nonempty_equivalenceRelation.some
  HasLimit.mk ⟨e.c, e.isLimit⟩

/-- The pullback of the first projection of an internal equivalence relation and the second
exists. -/
instance IsEquivalenceRelation.hasPullback [IsEquivalenceRelation p₁ p₂] : HasPullback p₁ p₂ :=
  hasPullback_symmetry p₂ p₁

/-- The diagonal `𝟙 X, 𝟙 X` is an internal equivalence relation. -/
instance IsEquivalenceRelation.id (X : C) : IsEquivalenceRelation (𝟙 X) (𝟙 X) :=
  (IsKernelPair.equivalenceRelation (𝟙 X) (𝟙 X) (𝟙 X) (PullbackCone.isLimitMkIdId (𝟙 X))
    (IsKernelPair.id_of_mono (𝟙 X))).isEquivalenceRelation

/-- A kernel pair `p₁, p₂` of `f` admitting a pullback of `p₂` and `p₁` is an internal equivalence
relation. -/
theorem IsKernelPair.isEquivalenceRelation {Y : C} {f : X ⟶ Y} (hk : IsKernelPair f p₁ p₂)
    [HasPullback p₂ p₁] : IsEquivalenceRelation p₁ p₂ :=
  (IsKernelPair.equivalenceRelation f p₁ p₂ (pullbackIsPullback p₂ p₁) hk).isEquivalenceRelation

namespace IsEquivalenceRelation

/-- A chosen internal equivalence relation structure. -/
private noncomputable def equivalenceRelation (h : IsEquivalenceRelation p₁ p₂) :
    EquivalenceRelation p₁ p₂ :=
  h.nonempty_equivalenceRelation.some

/-- The relation on morphisms `T ⟶ X` given by an internal equivalence relation is an equivalence
relation. -/
theorem equivalence_ofPairHom (h : IsEquivalenceRelation p₁ p₂) (T : C) :
    _root_.Equivalence (Rel.ofPairHom p₁ p₂ T) :=
  h.equivalenceRelation.equivalence_ofPairHom T

/-- Morphisms into the total space of an internal equivalence relation agree when their composites
with both projections agree. -/
theorem hom_ext (_ : IsEquivalenceRelation p₁ p₂) {T : C} {f g : T ⟶ R} (h₁ : f ≫ p₁ = g ≫ p₁)
    (h₂ : f ≫ p₂ = g ≫ p₂) : f = g :=
  JointlyMono₂.right_cancellation f g h₁ h₂

/-- Exchanging the two projections of an internal equivalence relation gives an internal
equivalence relation. -/
theorem swap (h : IsEquivalenceRelation p₁ p₂) : IsEquivalenceRelation p₂ p₁ :=
  let e := h.equivalenceRelation
  ⟨⟨{ right_cancellation := fun _ f g h₂ h₁ ↦ e.right_cancellation f g h₁ h₂
      r := e.r
      reflexivity₁ := e.reflexivity₂
      reflexivity₂ := e.reflexivity₁
      s := e.s
      symmetry₁ := e.symmetry₂
      symmetry₂ := e.symmetry₁
      c := e.c.flip
      isLimit := PullbackCone.flipIsLimit e.isLimit
      t := e.t
      transitivity₁ := e.transitivity₂
      transitivity₂ := e.transitivity₁ }⟩⟩

/-- The chosen reflexivity morphism `X ⟶ R` of an internal equivalence relation, a section of both
projections. -/
noncomputable def refl (h : IsEquivalenceRelation p₁ p₂) : X ⟶ R :=
  h.equivalenceRelation.r

@[reassoc (attr := simp)]
theorem reflexivity₁ (h : IsEquivalenceRelation p₁ p₂) : h.refl ≫ p₁ = 𝟙 X :=
  h.equivalenceRelation.reflexivity₁

@[reassoc (attr := simp)]
theorem reflexivity₂ (h : IsEquivalenceRelation p₁ p₂) : h.refl ≫ p₂ = 𝟙 X :=
  h.equivalenceRelation.reflexivity₂

/-- The chosen symmetry morphism `R ⟶ R` of an internal equivalence relation, exchanging the
projections. -/
noncomputable def symm (h : IsEquivalenceRelation p₁ p₂) : R ⟶ R :=
  h.equivalenceRelation.s

@[reassoc (attr := simp)]
theorem symmetry₁ (h : IsEquivalenceRelation p₁ p₂) : h.symm ≫ p₁ = p₂ :=
  h.equivalenceRelation.symmetry₁

@[reassoc (attr := simp)]
theorem symmetry₂ (h : IsEquivalenceRelation p₁ p₂) : h.symm ≫ p₂ = p₁ :=
  h.equivalenceRelation.symmetry₂

/-- The chosen transitivity morphism `R ×_X R ⟶ R` of an internal equivalence relation, where the
fibre product is formed over `p₂` on the first factor and `p₁` on the second: it relates `p₁` of
the first point to `p₂` of the second. -/
noncomputable def trans (h : IsEquivalenceRelation p₁ p₂) :
    pullback p₂ p₁ ⟶ R :=
  (h.equivalenceRelation.isLimit.conePointUniqueUpToIso (pullbackIsPullback p₂ p₁)).inv ≫
    h.equivalenceRelation.t

@[reassoc (attr := simp)]
theorem transitivity₁ (h : IsEquivalenceRelation p₁ p₂) :
    h.trans ≫ p₁ = pullback.fst p₂ p₁ ≫ p₁ := by
  simp [trans, h.equivalenceRelation.transitivity₁]

@[reassoc (attr := simp)]
theorem transitivity₂ (h : IsEquivalenceRelation p₁ p₂) :
    h.trans ≫ p₂ = pullback.snd p₂ p₁ ≫ p₂ := by
  simp [trans, h.equivalenceRelation.transitivity₂]

@[reassoc (attr := simp)]
theorem symm_symm (h : IsEquivalenceRelation p₁ p₂) : h.symm ≫ h.symm = 𝟙 R :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

@[reassoc (attr := simp)]
theorem refl_symm (h : IsEquivalenceRelation p₁ p₂) : h.refl ≫ h.symm = h.refl :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

/-- The symmetry morphism of an internal equivalence relation is an isomorphism. -/
instance isIso_symm (h : IsEquivalenceRelation p₁ p₂) : IsIso h.symm :=
  ⟨h.symm, h.symm_symm, h.symm_symm⟩

@[simp]
theorem inv_symm (h : IsEquivalenceRelation p₁ p₂) : inv h.symm = h.symm :=
  IsIso.inv_eq_of_hom_inv_id h.symm_symm

/-- Composing a point with the reflexivity at its second projection is the point itself. -/
@[reassoc (attr := simp)]
theorem lift_id_refl_trans (h : IsEquivalenceRelation p₁ p₂) :
    pullback.lift (𝟙 R) (p₂ ≫ h.refl) (by simp) ≫ h.trans = 𝟙 R :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

/-- Composing the reflexivity at the first projection of a point with the point is the point
itself. -/
@[reassoc (attr := simp)]
theorem lift_refl_id_trans (h : IsEquivalenceRelation p₁ p₂) :
    pullback.lift (p₁ ≫ h.refl) (𝟙 R) (by simp) ≫ h.trans = 𝟙 R :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

/-- Composing a point with its inverse gives the reflexivity at its first projection. -/
@[reassoc (attr := simp)]
theorem lift_id_symm_trans (h : IsEquivalenceRelation p₁ p₂) :
    pullback.lift (𝟙 R) h.symm (by simp) ≫ h.trans = p₁ ≫ h.refl :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

/-- Composing the inverse of a point with the point gives the reflexivity at its second
projection. -/
@[reassoc (attr := simp)]
theorem lift_symm_id_trans (h : IsEquivalenceRelation p₁ p₂) :
    pullback.lift h.symm (𝟙 R) (by simp) ≫ h.trans = p₂ ≫ h.refl :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

/-- On the kernel pair `p₁, p₂` of `f`, the reflexivity morphism is the diagonal. -/
theorem refl_eq_lift (h : IsEquivalenceRelation p₁ p₂) {Y : C} {f : X ⟶ Y}
    (hk : IsKernelPair f p₁ p₂) : h.refl = hk.lift (𝟙 X) (𝟙 X) rfl :=
  hk.hom_ext (by simp) (by simp)

/-- On the kernel pair `p₁, p₂` of `f`, the symmetry morphism exchanges the two factors. -/
theorem symm_eq_lift (h : IsEquivalenceRelation p₁ p₂) {Y : C} {f : X ⟶ Y}
    (hk : IsKernelPair f p₁ p₂) : h.symm = hk.lift p₂ p₁ hk.w.symm :=
  hk.hom_ext (by simp) (by simp)

@[simp]
theorem id_refl {X : C} (h : IsEquivalenceRelation (𝟙 X) (𝟙 X)) : h.refl = 𝟙 X := by
  simpa using h.reflexivity₁

@[simp]
theorem id_symm {X : C} (h : IsEquivalenceRelation (𝟙 X) (𝟙 X)) : h.symm = 𝟙 X := by
  simpa using h.symmetry₁

end IsEquivalenceRelation

end CategoryTheory

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory Limits

variable {C : Type*} [Category* C] {R X Y : C}

/-- The *restriction* of a pair `p₁ p₂ : R ⟶ X` along `f : Y ⟶ X`: the fibre product
`R ×_{X × X} (Y × Y)` of `(p₁, p₂)` and `f × f`, formed as the iterated fibre product
`(Y ×_{f, X, p₁} R) ×_{p₂, X, f} Y`. Its points are triples `(a, r, b)` of points `a, b` of `Y`
and `r` of `R` with `f a = p₁ r` and `p₂ r = f b`; it relates `a` to `b` exactly when `R` relates
`f a` to `f b` (`TauCeti.CategoryTheory.restrictRel.ofPairHom_iff`), and is an equivalence relation
when `p₁, p₂` is one (`CategoryTheory.IsEquivalenceRelation.restrictRel`). This is the restriction,
or pullback, of a relation (Stacks, Definition 39.3.3 (02V9), for schemes). -/
noncomputable abbrev restrictRel (f : Y ⟶ X) (p₁ p₂ : R ⟶ X) [HasPullback f p₁]
    [HasPullback (pullback.snd f p₁ ≫ p₂) f] : C :=
  pullback (pullback.snd f p₁ ≫ p₂) f

namespace restrictRel

variable (f : Y ⟶ X) (p₁ p₂ : R ⟶ X) [HasPullback f p₁] [HasPullback (pullback.snd f p₁ ≫ p₂) f]

/-- The first projection `(a, r, b) ↦ a` of the restriction of `p₁, p₂` along `f`. -/
noncomputable def fst : restrictRel f p₁ p₂ ⟶ Y :=
  pullback.fst (pullback.snd f p₁ ≫ p₂) f ≫ pullback.fst f p₁

/-- The second projection `(a, r, b) ↦ b` of the restriction of `p₁, p₂` along `f`. -/
noncomputable def snd : restrictRel f p₁ p₂ ⟶ Y :=
  pullback.snd (pullback.snd f p₁ ≫ p₂) f

/-- The projection `(a, r, b) ↦ r` from the restriction of `p₁, p₂` along `f` to `R`. -/
noncomputable def proj : restrictRel f p₁ p₂ ⟶ R :=
  pullback.fst (pullback.snd f p₁ ≫ p₂) f ≫ pullback.snd f p₁

theorem fst_def :
    fst f p₁ p₂ = pullback.fst (pullback.snd f p₁ ≫ p₂) f ≫ pullback.fst f p₁ := (rfl)

theorem snd_def : snd f p₁ p₂ = pullback.snd (pullback.snd f p₁ ≫ p₂) f := (rfl)

theorem proj_def :
    proj f p₁ p₂ = pullback.fst (pullback.snd f p₁ ≫ p₂) f ≫ pullback.snd f p₁ := (rfl)

@[reassoc (attr := simp)]
theorem proj_p₁ : proj f p₁ p₂ ≫ p₁ = fst f p₁ p₂ ≫ f := by
  simp [proj, fst, pullback.condition]

@[reassoc (attr := simp)]
theorem proj_p₂ : proj f p₁ p₂ ≫ p₂ = snd f p₁ p₂ ≫ f := by
  simpa [proj, snd] using pullback.condition (f := pullback.snd f p₁ ≫ p₂) (g := f)

variable {f p₁ p₂}

/-- The point `(a, r, b)` of the restriction of `p₁, p₂` along `f`, for `f a = p₁ r` and
`p₂ r = f b`. -/
noncomputable def lift {T : C} (a b : T ⟶ Y) (r : T ⟶ R) (h₁ : r ≫ p₁ = a ≫ f)
    (h₂ : r ≫ p₂ = b ≫ f) : T ⟶ restrictRel f p₁ p₂ :=
  pullback.lift (pullback.lift a r h₁.symm) b (by simpa using h₂)

@[reassoc (attr := simp)]
theorem lift_fst {T : C} (a b : T ⟶ Y) (r : T ⟶ R) (h₁ : r ≫ p₁ = a ≫ f)
    (h₂ : r ≫ p₂ = b ≫ f) : lift a b r h₁ h₂ ≫ fst f p₁ p₂ = a := by
  simp [lift, fst]

@[reassoc (attr := simp)]
theorem lift_snd {T : C} (a b : T ⟶ Y) (r : T ⟶ R) (h₁ : r ≫ p₁ = a ≫ f)
    (h₂ : r ≫ p₂ = b ≫ f) : lift a b r h₁ h₂ ≫ snd f p₁ p₂ = b := by
  simp [lift, snd]

@[reassoc (attr := simp)]
theorem lift_proj {T : C} (a b : T ⟶ Y) (r : T ⟶ R) (h₁ : r ≫ p₁ = a ≫ f)
    (h₂ : r ≫ p₂ = b ≫ f) : lift a b r h₁ h₂ ≫ proj f p₁ p₂ = r := by
  simp [lift, proj]

/-- Morphisms into the restriction of `p₁, p₂` along `f` agree when their composites with `fst`,
`snd` and `proj` agree. -/
@[ext high]
theorem hom_ext {T : C} {g g' : T ⟶ restrictRel f p₁ p₂} (h₁ : g ≫ fst f p₁ p₂ = g' ≫ fst f p₁ p₂)
    (h₂ : g ≫ snd f p₁ p₂ = g' ≫ snd f p₁ p₂) (h : g ≫ proj f p₁ p₂ = g' ≫ proj f p₁ p₂) :
    g = g' := by
  refine pullback.hom_ext ?_ h₂
  apply pullback.hom_ext
  · simpa [fst] using h₁
  · simpa [proj] using h

/-- The restriction of `p₁, p₂` along `f` relates `a` to `b` exactly when `p₁, p₂` relates `f a` to
`f b`. -/
theorem ofPairHom_iff {T : C} {a b : T ⟶ Y} :
    Rel.ofPairHom (fst f p₁ p₂) (snd f p₁ p₂) T a b ↔ Rel.ofPairHom p₁ p₂ T (a ≫ f) (b ≫ f) := by
  refine ⟨fun ⟨r, h₁, h₂⟩ ↦ ⟨r ≫ proj f p₁ p₂, by simp [← h₁], by simp [← h₂]⟩,
    fun ⟨r, h₁, h₂⟩ ↦ ⟨lift a b r h₁ h₂, by simp, by simp⟩⟩

/-- The projections of the restriction of a jointly monic pair are jointly monic. -/
instance jointlyMono₂ [JointlyMono₂ p₁ p₂] : JointlyMono₂ (fst f p₁ p₂) (snd f p₁ p₂) where
  right_cancellation _ g g' h₁ h₂ :=
    hom_ext h₁ h₂ <| JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _
      (by simp [reassoc_of% h₁]) (by simp [reassoc_of% h₂])

end restrictRel

end TauCeti.CategoryTheory

namespace CategoryTheory

open Limits TauCeti.CategoryTheory

variable {C : Type*} [Category* C] {R X Y : C}

/-- The restriction of an internal equivalence relation `p₁, p₂ : R ⟶ X` along `f : Y ⟶ X`, the
relation `R ×_{X × X} (Y × Y)` on `Y`, is an internal equivalence relation (Stacks, Lemma 39.3.2
(02V8), for schemes). -/
instance IsEquivalenceRelation.restrictRel (f : Y ⟶ X) (p₁ p₂ : R ⟶ X)
    [IsEquivalenceRelation p₁ p₂] [HasPullback f p₁] [HasPullback (pullback.snd f p₁ ≫ p₂) f]
    [HasPullback (restrictRel.snd f p₁ p₂) (restrictRel.fst f p₁ p₂)] :
    IsEquivalenceRelation (restrictRel.fst f p₁ p₂) (restrictRel.snd f p₁ p₂) := by
  have he := (‹IsEquivalenceRelation p₁ p₂›).equivalence_ofPairHom
  refine isEquivalenceRelation_iff.2 ⟨inferInstance, fun T ↦ ?_⟩
  refine ⟨fun a ↦ restrictRel.ofPairHom_iff.2 ((he T).refl _),
    fun h ↦ restrictRel.ofPairHom_iff.2 ((he T).symm (restrictRel.ofPairHom_iff.1 h)),
    fun h h' ↦ restrictRel.ofPairHom_iff.2
      ((he T).trans (restrictRel.ofPairHom_iff.1 h) (restrictRel.ofPairHom_iff.1 h'))⟩

/-- Restricting the kernel pair `p₁, p₂` of `φ` along `f` gives the kernel pair of `f ≫ φ`. -/
theorem IsKernelPair.restrictRel {Z : C} {φ : X ⟶ Z} {f : Y ⟶ X} {p₁ p₂ : R ⟶ X}
    [HasPullback f p₁] [HasPullback (pullback.snd f p₁ ≫ p₂) f] (hk : IsKernelPair φ p₁ p₂) :
    IsKernelPair (f ≫ φ) (restrictRel.fst f p₁ p₂) (restrictRel.snd f p₁ p₂) := by
  refine IsPullback.of_isLimit'
    ⟨by simp [← restrictRel.proj_p₁_assoc, ← restrictRel.proj_p₂_assoc, hk.w]⟩
    (PullbackCone.IsLimit.mk _ (fun c ↦ restrictRel.lift c.fst c.snd
      (hk.lift (c.fst ≫ f) (c.snd ≫ f) (by simpa using c.condition)) (by simp) (by simp))
      (fun c ↦ by simp) (fun c ↦ by simp) (fun c m h₁ h₂ ↦ restrictRel.hom_ext (by simpa using h₁)
        (by simpa using h₂) (hk.hom_ext (by simp [← h₁]) (by simp [← h₂]))))

end CategoryTheory
