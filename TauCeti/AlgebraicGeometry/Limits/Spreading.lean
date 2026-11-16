/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Final
public import TauCeti.AlgebraicGeometry.Gluing.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import TauCeti.CategoryTheory.Comma.Over.Basic

/-!
# Spreading out morphisms and isomorphisms across cofiltered limits

Let `D : I ⥤ Over S` be a cofiltered diagram of schemes over `S` with affine transition maps and
limit cone `c`. Pulling `c` back along a morphism `X ⟶ S` yields a cofiltered limit cone of
schemes with affine transition maps, whose terms remain quasi-compact (resp. quasi-separated) when
the terms of `D` and the morphism `X ⟶ S` are. Applying Mathlib's spreading-out lemmas from
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` to this pulled-back limit cone gives spreading
of equalities of morphisms, morphisms, and isomorphisms between pullbacks of `S`-schemes across
the limit (Stacks, Propositions 32.8.10 (01ZM) and 32.8.11 (01ZN)).

For any scheme `S` and point `s : S`, the local scheme `Spec 𝒪_{S, s}` is the cofiltered limit in
`Over S` of the affine open neighbourhoods `W` of `s`. Specializing the general limit-spreading
results to this cone spreads equalities, morphisms, and isomorphisms from `Spec 𝒪_{S, s}` to an
affine open neighbourhood of `s`, with no germ-injectivity or Noetherian assumptions. Combining
this with two-open gluing in `Over` spreads compatible isomorphisms given over a quasi-compact open
`U ⊆ S` and over `Spec 𝒪_{S, s}` to `U ⊔ W` for an affine open neighbourhood `W` of `s`
(Stacks, Lemma 32.20.3 (0BQ5)).

## Main declarations

* `TauCeti.AlgebraicGeometry.pullbackCompIso`: canonical natural isomorphism
  `Over.pullback g ⋙ Over.pullback f ≅ Over.pullback h` for `f ≫ g = h`.
* `TauCeti.AlgebraicGeometry.exists_pullback_map_eq_of_isLimit`: two morphisms between pullbacks
  at a stage of `D` that agree over the limit already agree at some finer stage.
* `TauCeti.AlgebraicGeometry.exists_pullback_hom_of_isLimit`: a morphism between pullbacks over
  the limit descends to a morphism at some stage (Stacks, Tag 01ZM).
* `TauCeti.AlgebraicGeometry.exists_pullback_iso_of_isLimit`: an isomorphism between pullbacks
  over the limit descends to an isomorphism at some stage (Stacks, Tag 01ZN).
* `TauCeti.AlgebraicGeometry.AffineOpenNhds`: the poset of affine open neighbourhoods of a point.
* `TauCeti.AlgebraicGeometry.fromSpecStalkOverCone` and
  `TauCeti.AlgebraicGeometry.isLimitFromSpecStalkOverCone`: `Spec 𝒪_{S, s}` as the cofiltered
  limit of affine open neighbourhoods of `s` in `Over S`.
* `TauCeti.AlgebraicGeometry.exists_pullback_map_eq_fromSpecStalk`,
  `TauCeti.AlgebraicGeometry.exists_pullback_hom_fromSpecStalk`,
  `TauCeti.AlgebraicGeometry.exists_pullback_iso_fromSpecStalk`: spreading equalities, morphisms,
  and isomorphisms from `Spec 𝒪_{S, s}` to an affine open neighbourhood of `s`.
* `TauCeti.AlgebraicGeometry.pullbackMapOpenIso`,
  `TauCeti.AlgebraicGeometry.stalkOpenRestriction`,
  `TauCeti.AlgebraicGeometry.infImageOpenIso`: open-subscheme compatibility helpers for spreading
  and gluing.
* `TauCeti.AlgebraicGeometry.exists_iso_of_iso_fromSpecStalk`: spreading compatible isomorphisms
  over a quasi-compact open `U` and `Spec 𝒪_{S, s}` to `U ⊔ W` (Stacks, Lemma 32.20.3 (0BQ5)).

## References

* [The Stacks Project, Section 32.8, Limits of schemes](https://stacks.math.columbia.edu/tag/01ZM)
* [The Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5)
-/

public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry

/-- Canonical natural isomorphism between pulling back along `g` then `f` and pulling back along
`h`, given `w : f ≫ g = h`. -/
def pullbackCompIso {A B C : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C}
    (w : f ≫ g = h) :
    Over.pullback g ⋙ Over.pullback f ≅ Over.pullback h :=
  (Over.pullbackComp f g).symm ≪≫
    NatIso.ofComponents (fun X ↦ Over.isoMk (pullback.congrHom rfl w) (by simp))
      (fun _ ↦ by ext1; apply pullback.hom_ext <;> simp)

/-- The forward map of `pullbackCompIso` commutes with the first projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_hom_app_left_fst {A B C : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ C}
    {h : A ⟶ C} (w : f ≫ g = h) (X : Over C) :
    ((pullbackCompIso w).hom.app X).left ≫ pullback.fst X.hom h =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g := by
  simp [pullbackCompIso, Over.pullbackComp]

/-- The inverse map of `pullbackCompIso` commutes with the double first projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_inv_app_left_fst_fst {A B C : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ C}
    {h : A ⟶ C} (w : f ≫ g = h) (X : Over C) :
    ((pullbackCompIso w).inv.app X).left ≫
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g =
      pullback.fst X.hom h := by
  simp [pullbackCompIso, Over.pullbackComp]

/-- Composing the inverse map of `pullbackCompIso` with the projection to `B` agrees with
pulling back along `h` followed by `f`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_inv_app_left_fst_snd {A B C : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ C}
    {h : A ⟶ C} (w : f ≫ g = h) (X : Over C) :
    ((pullbackCompIso w).inv.app X).left ≫
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.snd X.hom g =
      pullback.snd X.hom h ≫ f := by
  simp [pullbackCompIso, Over.pullbackComp]

section LimitSpreading

variable {S : Scheme.{u}} {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Over S} [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
  {c : Cone D} (hc : IsLimit c)

/-- Pulling back a diagram `D : I ⥤ Over S` along `X.hom` gives a diagram of schemes whose
transition maps are affine. -/
private instance isAffineHom_pullback_map (X : Over S) {i j : I} (f : i ⟶ j) :
    IsAffineHom ((D ⋙ Over.pullback X.hom ⋙ Over.forget X.left).map f) := by
  have houter : IsPullback (pullback.snd (D.obj i).hom X.hom) (pullback.fst (D.obj i).hom X.hom)
      X.hom ((D.map f).left ≫ (D.obj j).hom) := by
    rw [Over.w (D.map f)]
    exact (IsPullback.of_hasPullback (D.obj i).hom X.hom).flip
  have hpb : IsPullback (pullback.fst (D.obj i).hom X.hom)
      ((D ⋙ Over.pullback X.hom ⋙ Over.forget X.left).map f)
      (D.map f).left (pullback.fst (D.obj j).hom X.hom) := by
    refine (IsPullback.of_right (h₁₂ := pullback.snd (D.obj j).hom X.hom) (v₁₃ := X.hom) ?_ ?_
      (IsPullback.of_hasPullback (D.obj j).hom X.hom).flip).flip
    · simpa [Over.pullback_map_left] using houter
    · simp [Over.pullback_map_left]
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hpb inferInstance

/-- The canonical natural transformation from the pulled-back diagram `D ×_S X` to `S`. -/
private def pullbackToBaseNatTrans (D : I ⥤ Over S) (X : Over S) :
    (D ⋙ Over.pullback X.hom ⋙ Over.forget X.left) ⟶ (Functor.const I).obj S where
  app i := pullback.snd (D.obj i).hom X.hom ≫ X.hom
  naturality _ _ f := by simp [Over.pullback_map_left]

/-- Identifying `X ×_S T' ⟶ X ×_S T` via `pullbackCompIso` with the swapped pullback map
`T' ×_S X ⟶ T ×_S X`. -/
private lemma pullbackSymmetry_comp_pullbackCompIso_inv {T' T : Over S} (u : T' ⟶ T) (X : Over S) :
    (pullbackSymmetry T'.hom X.hom).hom ≫
        ((pullbackCompIso (Over.w u)).inv.app X).left ≫
          pullback.fst (pullback.snd X.hom T.hom) u.left =
      ((Over.pullback X.hom).map u).left ≫ (pullbackSymmetry T.hom X.hom).hom := by
  apply pullback.hom_ext
  · simp [Over.pullback_map_left]
  · simp [Over.pullback_map_left]

/-- Composition of morphisms conjugated by `pullbackCompIso`. -/
private lemma pullbackCompIso_conj_mul {T' T : Over S} (u : T' ⟶ T) {X Y Z : Over S}
    (a : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y)
    (b : (Over.pullback T.hom).obj Y ⟶ (Over.pullback T.hom).obj Z) :
    ((pullbackCompIso (Over.w u)).inv.app X ≫ (Over.pullback u.left).map a ≫
        (pullbackCompIso (Over.w u)).hom.app Y) ≫
      ((pullbackCompIso (Over.w u)).inv.app Y ≫ (Over.pullback u.left).map b ≫
        (pullbackCompIso (Over.w u)).hom.app Z) =
      (pullbackCompIso (Over.w u)).inv.app X ≫ (Over.pullback u.left).map (a ≫ b) ≫
        (pullbackCompIso (Over.w u)).hom.app Z := by
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc ((pullbackCompIso (Over.w u)).hom.app Y),
    Iso.hom_inv_id_app, Category.id_comp]

/-- Conjugation of the identity morphism by `pullbackCompIso` is the identity. -/
private lemma pullbackCompIso_conj_id {T' T : Over S} (u : T' ⟶ T) (X : Over S) :
    (pullbackCompIso (Over.w u)).inv.app X ≫
        (Over.pullback u.left).map (𝟙 ((Over.pullback T.hom).obj X)) ≫
        (pullbackCompIso (Over.w u)).hom.app X =
      𝟙 ((Over.pullback T'.hom).obj X) := by
  rw [CategoryTheory.Functor.map_id]
  change (pullbackCompIso (Over.w u)).inv.app X ≫
    𝟙 ((Over.pullback T.hom ⋙ Over.pullback u.left).obj X) ≫
    (pullbackCompIso (Over.w u)).hom.app X = _
  rw [Category.id_comp, Iso.inv_hom_id_app]

/-- Functoriality of conjugation by `pullbackCompIso` under composition `v ≫ u = uv` in
`Over S`. -/
private lemma pullbackCompIso_conj_comp {T'' T' T : Over S} (v : T'' ⟶ T') (u : T' ⟶ T)
    {uv : T'' ⟶ T} (huv : v ≫ u = uv) {X Y : Over S}
    (ψ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y) :
    (pullbackCompIso (Over.w v)).inv.app X ≫
        (Over.pullback v.left).map ((pullbackCompIso (Over.w u)).inv.app X ≫
          (Over.pullback u.left).map ψ ≫ (pullbackCompIso (Over.w u)).hom.app Y) ≫
        (pullbackCompIso (Over.w v)).hom.app Y =
      (pullbackCompIso (Over.w uv)).inv.app X ≫
        (Over.pullback uv.left).map ψ ≫
        (pullbackCompIso (Over.w uv)).hom.app Y := by
  subst huv
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, pullbackCompIso_hom_app_left_fst,
      Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc]
    have hkey : ((pullbackCompIso (Over.w v)).inv.app X).left ≫
          pullback.fst (pullback.snd X.hom T'.hom) v.left ≫
          ((pullbackCompIso (Over.w u)).inv.app X).left ≫
          pullback.fst (pullback.snd X.hom T.hom) u.left =
        ((pullbackCompIso (Over.w (v ≫ u))).inv.app X).left ≫
          pullback.fst (pullback.snd X.hom T.hom) (v.left ≫ u.left) := by
      apply pullback.hom_ext
      · simp
      · simp
    rw [reassoc_of% hkey]
  · exact (Over.w _).trans (Over.w _).symm

include hc in
/-- If two morphisms between pullbacks of `S`-schemes at a stage `i` of a cofiltered diagram with
affine transition maps agree after pulling back to the limit, they already agree at some finer
stage `k ⟶ i`. -/
theorem exists_pullback_map_eq_of_isLimit
    [∀ i, CompactSpace (D.obj i).left]
    {X Y : Over S} [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    {i : I}
    (a b : (Over.pullback (D.obj i).hom).obj X ⟶ (Over.pullback (D.obj i).hom).obj Y)
    (hab : (Over.pullback (c.π.app i).left).map a = (Over.pullback (c.π.app i).left).map b) :
    ∃ (k : I) (hik : k ⟶ i),
      (Over.pullback (D.map hik).left).map a = (Over.pullback (D.map hik).left).map b := by
  have : IsConnected I := IsCofiltered.isConnected I
  let DX := D ⋙ Over.pullback X.hom ⋙ Over.forget X.left
  let cX := (Over.pullback X.hom ⋙ Over.forget X.left).mapCone c
  have hcX : IsLimit cX := isLimitOfPreserves (Over.pullback X.hom ⋙ Over.forget X.left) hc
  have hcomp (j : I) : CompactSpace (DX.obj j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.obj j).hom X.hom)
  let a' : DX.obj i ⟶ Y.left :=
    (pullbackSymmetry (D.obj i).hom X.hom).hom ≫ a.left ≫ pullback.fst Y.hom (D.obj i).hom
  let b' : DX.obj i ⟶ Y.left :=
    (pullbackSymmetry (D.obj i).hom X.hom).hom ≫ b.left ≫ pullback.fst Y.hom (D.obj i).hom
  have ha' : (pullbackToBaseNatTrans D X).app i = a' ≫ Y.hom := by
    simp only [pullbackToBaseNatTrans, a', Category.assoc, pullback.condition]
    have hw : a.left ≫ pullback.snd Y.hom (D.obj i).hom = pullback.snd X.hom (D.obj i).hom :=
      Over.w a
    rw [reassoc_of% hw, pullbackSymmetry_hom_comp_snd_assoc, pullback.condition]
  have hb' : (pullbackToBaseNatTrans D X).app i = b' ≫ Y.hom := by
    simp only [pullbackToBaseNatTrans, b', Category.assoc, pullback.condition]
    have hw : b.left ≫ pullback.snd Y.hom (D.obj i).hom = pullback.snd X.hom (D.obj i).hom :=
      Over.w b
    rw [reassoc_of% hw, pullbackSymmetry_hom_comp_snd_assoc, pullback.condition]
  let πi : c.pt ⟶ D.obj i := c.π.app i
  have hab' : cX.π.app i ≫ a' = cX.π.app i ≫ b' := by
    have hcomp_eq :
        ((Over.pullback πi.left).map a).left ≫
            pullback.fst ((Over.pullback (D.obj i).hom).obj Y).hom πi.left =
          ((Over.pullback πi.left).map b).left ≫
            pullback.fst ((Over.pullback (D.obj i).hom).obj Y).hom πi.left :=
      congrArg (fun m ↦ m.left ≫ pullback.fst _ _) hab
    simp only [Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst] at hcomp_eq
    have hsym := pullbackSymmetry_comp_pullbackCompIso_inv πi X
    calc cX.π.app i ≫ a'
        = (((Over.pullback X.hom).map πi).left ≫
            (pullbackSymmetry (D.obj i).hom X.hom).hom) ≫
            a.left ≫ pullback.fst Y.hom (D.obj i).hom := by simp [cX, a', πi]
      _ = (pullbackSymmetry c.pt.hom X.hom).hom ≫
            ((pullbackCompIso (Over.w πi)).inv.app X).left ≫
            (pullback.fst (pullback.snd X.hom (D.obj i).hom) πi.left ≫ a.left) ≫
            pullback.fst Y.hom (D.obj i).hom := by rw [← hsym]; simp only [Category.assoc]
      _ = (pullbackSymmetry c.pt.hom X.hom).hom ≫
            ((pullbackCompIso (Over.w πi)).inv.app X).left ≫
            (pullback.fst (pullback.snd X.hom (D.obj i).hom) πi.left ≫ b.left) ≫
            pullback.fst Y.hom (D.obj i).hom := by rw [hcomp_eq]
      _ = (((Over.pullback X.hom).map πi).left ≫
            (pullbackSymmetry (D.obj i).hom X.hom).hom) ≫
            b.left ≫ pullback.fst Y.hom (D.obj i).hom := by rw [← hsym]; simp only [Category.assoc]
      _ = cX.π.app i ≫ b' := by simp [cX, b', πi]
  obtain ⟨k, hik, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    DX (pullbackToBaseNatTrans D X) Y.hom cX hcX a' b' ha' hb' hab'
  refine ⟨k, hik, ?_⟩
  ext1
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst]
    apply pullback.hom_ext
    · have hsym := pullbackSymmetry_comp_pullbackCompIso_inv (D.map hik) X
      have hid : ((pullbackCompIso (Over.w (D.map hik))).hom.app X).left ≫
            ((pullbackCompIso (Over.w (D.map hik))).inv.app X).left = 𝟙 _ := by
        rw [← Over.comp_left, Iso.hom_inv_id_app]; rfl
      have heq' : ((pullbackCompIso (Over.w (D.map hik))).hom.app X).left ≫
            (pullbackSymmetry (D.obj k).hom X.hom).inv ≫
            (((Over.pullback X.hom).map (D.map hik)).left ≫
              (pullbackSymmetry (D.obj i).hom X.hom).hom) ≫
            a.left ≫ pullback.fst Y.hom (D.obj i).hom =
          ((pullbackCompIso (Over.w (D.map hik))).hom.app X).left ≫
            (pullbackSymmetry (D.obj k).hom X.hom).inv ≫
            (((Over.pullback X.hom).map (D.map hik)).left ≫
              (pullbackSymmetry (D.obj i).hom X.hom).hom) ≫
            b.left ≫ pullback.fst Y.hom (D.obj i).hom := by
        simpa only [DX, a', b', Functor.comp_map, Over.forget_map, Category.assoc] using
          congrArg (fun m ↦ ((pullbackCompIso (Over.w (D.map hik))).hom.app X).left ≫
            (pullbackSymmetry (D.obj k).hom X.hom).inv ≫ m) heq
      rw [← hsym] at heq'
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hid] at heq'
      simpa only [Category.assoc] using heq'
    · have hwa : a.left ≫ pullback.snd Y.hom (D.obj i).hom = pullback.snd X.hom (D.obj i).hom :=
        Over.w a
      have hwb : b.left ≫ pullback.snd Y.hom (D.obj i).hom = pullback.snd X.hom (D.obj i).hom :=
        Over.w b
      simp only [Category.assoc, hwa, hwb]
  · simp only [Over.pullback_map_left, pullback.lift_snd]

include hc in
/-- Given a cofiltered diagram `D : I ⥤ Over S` of qcqs schemes with affine transition maps and
limit cone `c`, any morphism between pullbacks of `X` and `Y` over the limit descends to some
stage `D.obj i`, provided `X ⟶ S` is qcqs and `Y ⟶ S` is locally of finite presentation. -/
@[stacks 01ZM]
theorem exists_pullback_hom_of_isLimit
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    {X Y : Over S} [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    (φ : (Over.pullback c.pt.hom).obj X ⟶ (Over.pullback c.pt.hom).obj Y) :
    ∃ (i : I) (ψ : (Over.pullback (D.obj i).hom).obj X ⟶ (Over.pullback (D.obj i).hom).obj Y),
      (pullbackCompIso (Over.w (c.π.app i) : (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).inv.app
          X ≫
        (Over.pullback (c.π.app i).left).map ψ ≫
        (pullbackCompIso (Over.w (c.π.app i) : (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).hom.app
          Y = φ := by
  have : IsConnected I := IsCofiltered.isConnected I
  let DX := D ⋙ Over.pullback X.hom ⋙ Over.forget X.left
  let cX := (Over.pullback X.hom ⋙ Over.forget X.left).mapCone c
  have hcX : IsLimit cX := isLimitOfPreserves (Over.pullback X.hom ⋙ Over.forget X.left) hc
  have hcomp (j : I) : CompactSpace (DX.obj j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.obj j).hom X.hom)
  have hqs (j : I) : QuasiSeparatedSpace (DX.obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.obj j).hom X.hom)
  let a : cX.pt ⟶ Y.left :=
    (pullbackSymmetry c.pt.hom X.hom).hom ≫ φ.left ≫ pullback.fst Y.hom c.pt.hom
  have ha : cX.π ≫ pullbackToBaseNatTrans D X = (Functor.const I).map (a ≫ Y.hom) := by
    ext j
    simp only [NatTrans.comp_app, pullbackToBaseNatTrans, Functor.const_map_app, a, Category.assoc,
      pullback.condition, cX]
    have hw : φ.left ≫ pullback.snd Y.hom c.pt.hom = pullback.snd X.hom c.pt.hom := Over.w φ
    rw [reassoc_of% hw, pullbackSymmetry_hom_comp_snd_assoc, pullback.condition]
    simp [Over.pullback_map_left]
  obtain ⟨i, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    DX (pullbackToBaseNatTrans D X) Y.hom cX hcX a ha
  let ψ : (Over.pullback (D.obj i).hom).obj X ⟶ (Over.pullback (D.obj i).hom).obj Y :=
    Over.homMk (pullback.lift ((pullbackSymmetry (D.obj i).hom X.hom).inv ≫ g)
      (pullback.snd X.hom (D.obj i).hom) (by
        rw [Category.assoc, hg']
        simp [pullbackToBaseNatTrans, pullback.condition])) (by simp)
  let πi : c.pt ⟶ D.obj i := c.π.app i
  refine ⟨i, ψ, ?_⟩
  ext1
  apply pullback.hom_ext
  · change (((pullbackCompIso (Over.w πi)).inv.app X).left ≫
        ((Over.pullback πi.left).map ψ).left ≫
        ((pullbackCompIso (Over.w πi)).hom.app Y).left) ≫
        pullback.fst Y.hom c.pt.hom =
      φ.left ≫ pullback.fst Y.hom c.pt.hom
    simp only [Category.assoc, pullbackCompIso_hom_app_left_fst,
      Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc]
    have hψ : ψ.left ≫ pullback.fst Y.hom (D.obj i).hom =
        (pullbackSymmetry (D.obj i).hom X.hom).inv ≫ g := pullback.lift_fst _ _ _
    have hsym := pullbackSymmetry_comp_pullbackCompIso_inv πi X
    rw [hψ, ← cancel_epi (pullbackSymmetry c.pt.hom X.hom).hom]
    simp only [reassoc_of% hsym, Iso.hom_inv_id_assoc]
    simpa [cX, a, πi] using hg
  · exact (Over.w _).trans (Over.w _).symm

include hc in
/-- Given a cofiltered diagram `D : I ⥤ Over S` of qcqs schemes with affine transition maps and
limit cone `c`, any isomorphism between pullbacks of `X` and `Y` over the limit descends to an
isomorphism at some stage `D.obj i`, provided both `X ⟶ S` and `Y ⟶ S` are qcqs and locally of
finite presentation. -/
@[stacks 01ZN]
theorem exists_pullback_iso_of_isLimit
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    {X Y : Over S}
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [LocallyOfFinitePresentation Y.hom]
    (e : (Over.pullback c.pt.hom).obj X ≅ (Over.pullback c.pt.hom).obj Y) :
    ∃ (i : I) (eᵢ : (Over.pullback (D.obj i).hom).obj X ≅ (Over.pullback (D.obj i).hom).obj Y),
      ((pullbackCompIso (Over.w (c.π.app i) :
          (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).app X).symm ≪≫
        (Over.pullback (c.π.app i).left).mapIso eᵢ ≪≫
        (pullbackCompIso (Over.w (c.π.app i) :
          (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).app Y = e := by
  obtain ⟨i₁, ψ₁, hψ₁⟩ := exists_pullback_hom_of_isLimit hc e.hom
  obtain ⟨i₂, ψ₂, hψ₂⟩ := exists_pullback_hom_of_isLimit hc e.inv
  let i₀ := IsCofiltered.min i₁ i₂
  let f₁ : i₀ ⟶ i₁ := IsCofiltered.minToLeft i₁ i₂
  let f₂ : i₀ ⟶ i₂ := IsCofiltered.minToRight i₁ i₂
  let g : (Over.pullback (D.obj i₀).hom).obj X ⟶ (Over.pullback (D.obj i₀).hom).obj Y :=
    (pullbackCompIso (Over.w (D.map f₁))).inv.app X ≫
      (Over.pullback (D.map f₁).left).map ψ₁ ≫
      (pullbackCompIso (Over.w (D.map f₁))).hom.app Y
  let h : (Over.pullback (D.obj i₀).hom).obj Y ⟶ (Over.pullback (D.obj i₀).hom).obj X :=
    (pullbackCompIso (Over.w (D.map f₂))).inv.app Y ≫
      (Over.pullback (D.map f₂).left).map ψ₂ ≫
      (pullbackCompIso (Over.w (D.map f₂))).hom.app X
  let π₀ : c.pt ⟶ D.obj i₀ := c.π.app i₀
  have hg : (pullbackCompIso (Over.w π₀)).inv.app X ≫
      (Over.pullback π₀.left).map g ≫
      (pullbackCompIso (Over.w π₀)).hom.app Y = e.hom := by
    rw [pullbackCompIso_conj_comp π₀ (D.map f₁) (c.w f₁) ψ₁]
    exact hψ₁
  have hh : (pullbackCompIso (Over.w π₀)).inv.app Y ≫
      (Over.pullback π₀.left).map h ≫
      (pullbackCompIso (Over.w π₀)).hom.app X = e.inv := by
    rw [pullbackCompIso_conj_comp π₀ (D.map f₂) (c.w f₂) ψ₂]
    exact hψ₂
  have hgh : (Over.pullback π₀.left).map (g ≫ h) =
      (Over.pullback π₀.left).map (𝟙 _) := by
    rw [← cancel_epi ((pullbackCompIso (Over.w π₀)).inv.app X),
      ← cancel_mono ((pullbackCompIso (Over.w π₀)).hom.app X)]
    simp only [Category.assoc]
    rw [← pullbackCompIso_conj_mul π₀ g h, hg, hh, Iso.hom_inv_id, pullbackCompIso_conj_id]
  obtain ⟨k₁, fk₁, hfk₁⟩ := exists_pullback_map_eq_of_isLimit hc (g ≫ h) (𝟙 _) hgh
  let g₁ := (pullbackCompIso (Over.w (D.map fk₁))).inv.app X ≫
    (Over.pullback (D.map fk₁).left).map g ≫
    (pullbackCompIso (Over.w (D.map fk₁))).hom.app Y
  let h₁ := (pullbackCompIso (Over.w (D.map fk₁))).inv.app Y ≫
    (Over.pullback (D.map fk₁).left).map h ≫
    (pullbackCompIso (Over.w (D.map fk₁))).hom.app X
  have hg₁h₁ : g₁ ≫ h₁ = 𝟙 _ := by
    rw [pullbackCompIso_conj_mul (D.map fk₁) g h, hfk₁, pullbackCompIso_conj_id]
  let πk₁ : c.pt ⟶ D.obj k₁ := c.π.app k₁
  have hg₁ : (pullbackCompIso (Over.w πk₁)).inv.app X ≫
      (Over.pullback πk₁.left).map g₁ ≫
      (pullbackCompIso (Over.w πk₁)).hom.app Y = e.hom := by
    rw [pullbackCompIso_conj_comp πk₁ (D.map fk₁) (c.w fk₁) g]
    exact hg
  have hh₁ : (pullbackCompIso (Over.w πk₁)).inv.app Y ≫
      (Over.pullback πk₁.left).map h₁ ≫
      (pullbackCompIso (Over.w πk₁)).hom.app X = e.inv := by
    rw [pullbackCompIso_conj_comp πk₁ (D.map fk₁) (c.w fk₁) h]
    exact hh
  have hh₁g₁_lim : (Over.pullback πk₁.left).map (h₁ ≫ g₁) =
      (Over.pullback πk₁.left).map (𝟙 _) := by
    rw [← cancel_epi ((pullbackCompIso (Over.w πk₁)).inv.app Y),
      ← cancel_mono ((pullbackCompIso (Over.w πk₁)).hom.app Y)]
    simp only [Category.assoc]
    rw [← pullbackCompIso_conj_mul πk₁ h₁ g₁, hh₁, hg₁, Iso.inv_hom_id, pullbackCompIso_conj_id]
  obtain ⟨k, fk, hfk⟩ := exists_pullback_map_eq_of_isLimit hc (h₁ ≫ g₁) (𝟙 _) hh₁g₁_lim
  let g₂ := (pullbackCompIso (Over.w (D.map fk))).inv.app X ≫
    (Over.pullback (D.map fk).left).map g₁ ≫
    (pullbackCompIso (Over.w (D.map fk))).hom.app Y
  let h₂ := (pullbackCompIso (Over.w (D.map fk))).inv.app Y ≫
    (Over.pullback (D.map fk).left).map h₁ ≫
    (pullbackCompIso (Over.w (D.map fk))).hom.app X
  let πk : c.pt ⟶ D.obj k := c.π.app k
  refine ⟨k, ⟨g₂, h₂, ?_, ?_⟩, ?_⟩
  · rw [pullbackCompIso_conj_mul (D.map fk) g₁ h₁, hg₁h₁, pullbackCompIso_conj_id]
  · rw [pullbackCompIso_conj_mul (D.map fk) h₁ g₁, hfk, pullbackCompIso_conj_id]
  · ext1
    change (pullbackCompIso (Over.w πk)).inv.app X ≫
        (Over.pullback πk.left).map g₂ ≫
        (pullbackCompIso (Over.w πk)).hom.app Y = e.hom
    rw [pullbackCompIso_conj_comp πk (D.map fk) (c.w fk) g₁]
    exact hg₁

end LimitSpreading

section LocalSchemeLimit

/-- Affine open neighbourhoods of a point `s` of a scheme `S`, ordered by inclusion. -/
@[ext]
structure AffineOpenNhds (S : Scheme.{u}) (s : S) where
  /-- The underlying open subset of `S`. -/
  opens : S.Opens
  /-- The open subscheme is affine. -/
  isAffineOpen : IsAffineOpen opens
  /-- The open subset contains `s`. -/
  mem : s ∈ opens

namespace AffineOpenNhds

variable {S : Scheme.{u}} {s : S}

instance : PartialOrder (AffineOpenNhds S s) :=
  PartialOrder.lift AffineOpenNhds.opens (fun _ _ h ↦ AffineOpenNhds.ext h)

/-- Inclusion order on affine open neighbourhoods is inclusion of the underlying opens. -/
theorem le_def {U V : AffineOpenNhds S s} : U ≤ V ↔ U.opens ≤ V.opens := Iff.rfl

instance : IsCofiltered (AffineOpenNhds S s) where
  nonempty := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    exact ⟨⟨U, hU, hsU⟩⟩
  cone_objs U V := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hsW, hWle⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show s ∈ (U.opens ⊓ V.opens : Set S) from ⟨U.mem, V.mem⟩) (U.opens ⊓ V.opens).2
    exact ⟨⟨W, hW, hsW⟩, homOfLE (hWle.trans inf_le_left),
      homOfLE (hWle.trans inf_le_right), trivial⟩
  cone_maps U V f g := ⟨U, 𝟙 U, by simp [Subsingleton.elim f g]⟩

/-- The forgetful functor from affine open neighbourhoods of `s` to all open neighbourhoods. -/
def toOpenNhds (S : Scheme.{u}) (s : S) : AffineOpenNhds S s ⥤ OpenNhds s where
  obj U := ⟨U.opens, U.mem⟩
  map f := homOfLE f.le

instance (S : Scheme.{u}) (s : S) : (toOpenNhds S s).Initial where
  out U := by
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hsW₀, hW₀U⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open U.2 U.1.2
    have : Nonempty (CostructuredArrow (toOpenNhds S s) U) :=
      ⟨CostructuredArrow.mk (Y := ⟨W₀, hW₀, hsW₀⟩)
        (homOfLE (show (toOpenNhds S s).obj ⟨W₀, hW₀, hsW₀⟩ ≤ U from hW₀U))⟩
    refine zigzag_isConnected fun X Y ↦ ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hsW, hWle⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show s ∈ (X.left.opens ⊓ Y.left.opens : Set S) from ⟨X.left.mem, Y.left.mem⟩)
        (X.left.opens ⊓ Y.left.opens).2
    let Z : CostructuredArrow (toOpenNhds S s) U :=
      CostructuredArrow.mk (Y := ⟨W, hW, hsW⟩)
        (homOfLE (show (toOpenNhds S s).obj ⟨W, hW, hsW⟩ ≤ U from
          (hWle.trans inf_le_left).trans X.hom.le))
    refine Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (Or.inr ⟨CostructuredArrow.homMk
        (f := Z) (f' := X)
        (homOfLE (show Z.left ≤ X.left from hWle.trans inf_le_left))
        (Subsingleton.elim _ _)⟩))
      (Relation.ReflTransGen.single (Or.inl ⟨CostructuredArrow.homMk
        (f := Z) (f' := Y)
        (homOfLE (show Z.left ≤ Y.left from hWle.trans inf_le_right))
        (Subsingleton.elim _ _)⟩))

end AffineOpenNhds

/-- The diagram of affine open neighbourhoods of `s` in `Over S`, indexed by the `u`-small category
`ULiftHom.{u} (AffineOpenNhds S s)`. -/
@[expose, simps]
def fromSpecStalkOverDiagram (S : Scheme.{u}) (s : S) :
    ULiftHom.{u} (AffineOpenNhds S s) ⥤ Over S where
  obj W := Over.mk W.objDown.opens.ι
  map f := Over.homMk (S.homOfLE f.down.le) (by simp)
  map_id W := by ext1; simp
  map_comp _ _ := by ext1; simp

/-- The cone over `fromSpecStalkOverDiagram S s` with cone point `Spec 𝒪_{S, s} ⟶ S`. -/
@[expose, simps]
def fromSpecStalkOverCone (S : Scheme.{u}) (s : S) :
    Cone (fromSpecStalkOverDiagram S s) where
  pt := Over.mk (S.fromSpecStalk s)
  π :=
    { app W := Over.homMk (W.objDown.opens.fromSpecStalkOfMem s W.objDown.mem)
        (by simp [fromSpecStalkOverDiagram])
      naturality W₁ W₂ f := by
        ext1
        change 𝟙 _ ≫ W₂.objDown.opens.fromSpecStalkOfMem s W₂.objDown.mem =
          W₁.objDown.opens.fromSpecStalkOfMem s W₁.objDown.mem ≫ S.homOfLE f.down.le
        rw [Category.id_comp, ← cancel_mono W₂.objDown.opens.ι]
        simp }

instance (S : Scheme.{u}) (s : S) : IsCofiltered (ULiftHom.{u} (AffineOpenNhds S s)) :=
  IsCofiltered.of_equivalence ULiftHom.equiv

instance (S : Scheme.{u}) (s : S) (W : ULiftHom.{u} (AffineOpenNhds S s)) :
    IsAffine ((fromSpecStalkOverDiagram S s).obj W).left :=
  W.objDown.isAffineOpen

instance (S : Scheme.{u}) (s : S) {W₁ W₂ : ULiftHom.{u} (AffineOpenNhds S s)} (f : W₁ ⟶ W₂) :
    IsAffineHom ((fromSpecStalkOverDiagram S s).map f).left := by
  have : IsAffine W₁.objDown.opens.toScheme := W₁.objDown.isAffineOpen
  have : IsAffine W₂.objDown.opens.toScheme := W₂.objDown.isAffineOpen
  exact isAffineHom_of_isAffine (S.homOfLE f.down.le)

/-- The local scheme `Spec 𝒪_{S, s}` is the cofiltered limit in `Over S` of the affine open
neighbourhoods of `s`. -/
def isLimitFromSpecStalkOverCone (S : Scheme.{u}) (s : S) :
    IsLimit (fromSpecStalkOverCone S s) := by
  haveI : IsConnected (ULiftHom.{u} (AffineOpenNhds S s)) := IsCofiltered.isConnected _
  let K : ULiftHom.{u} (AffineOpenNhds S s) ⥤ OpenNhds s :=
    ULiftHom.down ⋙ AffineOpenNhds.toOpenNhds S s
  haveI : (ULiftHom.down (C := AffineOpenNhds S s)).IsEquivalence :=
    (ULiftHom.equiv (C := AffineOpenNhds S s)).isEquivalence_inverse
  haveI : K.Initial :=
    Functor.initial_equivalence_comp ULiftHom.down (AffineOpenNhds.toOpenNhds S s)
  let stalkCocone := (colimit.cocone ((OpenNhds.inclusion s).op ⋙ S.presheaf)).whisker K.op
  have hcStalk : IsColimit stalkCocone :=
    (Functor.Final.isColimitWhiskerEquiv K.op _).symm (colimit.isColimit _)
  let specCone := Scheme.Spec.mapCone (coneRightOpOfCocone stalkCocone)
  have hcSpec : IsLimit specCone :=
    isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hcStalk)
  let eDiag : (fromSpecStalkOverDiagram S s ⋙ Over.forget S) ≅
      (K.op ⋙ (OpenNhds.inclusion s).op ⋙ S.presheaf).rightOp ⋙ Scheme.Spec :=
    NatIso.ofComponents (fun W ↦ W.objDown.isAffineOpen.isoSpec) fun {W₁ W₂} f ↦ by
      change S.homOfLE f.down.le ≫ W₂.objDown.opens.toSpecΓ =
        W₁.objDown.opens.toSpecΓ ≫ Spec.map (S.presheaf.map (homOfLE f.down.le).op)
      exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map W₁.objDown.opens W₂.objDown.opens
        f.down.le).symm
  let eCone : (Over.forget S).mapCone (fromSpecStalkOverCone S s) ≅
      (Cone.postcompose eDiag.inv).obj specCone :=
    Cone.ext (Iso.refl _) fun W ↦ by
      change 𝟙 _ ≫ W.objDown.opens.fromSpecStalkOfMem s W.objDown.mem =
        Spec.map (S.presheaf.germ W.objDown.opens s W.objDown.mem) ≫
          W.objDown.isAffineOpen.isoSpec.inv
      rw [Category.id_comp, Iso.eq_comp_inv]
      exact W.objDown.opens.fromSpecStalkOfMem_toSpecΓ s W.objDown.mem
  refine isLimitOfReflects (Over.forget S) ?_
  exact ((IsLimit.postcomposeInvEquiv eDiag specCone).symm hcSpec).ofIsoLimit eCone.symm

/-- If two morphisms between `S`-schemes agree after pulling back to `Spec 𝒪_{S, s}`, they already
agree over some affine open neighbourhood of `s`. -/
theorem exists_pullback_map_eq_fromSpecStalk {S : Scheme.{u}} (s : S)
    {X Y : Over S} [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    (a b : X ⟶ Y)
    (hab : (Over.pullback (S.fromSpecStalk s)).map a =
      (Over.pullback (S.fromSpecStalk s)).map b) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W), s ∈ W ∧
      (Over.pullback W.ι).map a = (Over.pullback W.ι).map b := by
  obtain ⟨W₀⟩ := IsCofiltered.nonempty (C := ULiftHom.{u} (AffineOpenNhds S s))
  have hlim : (Over.pullback ((fromSpecStalkOverCone S s).π.app W₀).left).map
        ((Over.pullback ((fromSpecStalkOverDiagram S s).obj W₀).hom).map a) =
      (Over.pullback ((fromSpecStalkOverCone S s).π.app W₀).left).map
        ((Over.pullback ((fromSpecStalkOverDiagram S s).obj W₀).hom).map b) := by
    let e := pullbackCompIso (W₀.objDown.opens.fromSpecStalkOfMem_ι s W₀.objDown.mem)
    change (Over.pullback (W₀.objDown.opens.fromSpecStalkOfMem s W₀.objDown.mem)).map
        ((Over.pullback W₀.objDown.opens.ι).map a) =
      (Over.pullback (W₀.objDown.opens.fromSpecStalkOfMem s W₀.objDown.mem)).map
        ((Over.pullback W₀.objDown.opens.ι).map b)
    rw [← cancel_mono (e.hom.app Y)]
    have ha := e.hom.naturality a
    have hb := e.hom.naturality b
    dsimp only [Functor.comp_map] at ha hb
    rw [ha, hb, hab]
  obtain ⟨W, hW, heq⟩ := exists_pullback_map_eq_of_isLimit (isLimitFromSpecStalkOverCone S s)
    ((Over.pullback ((fromSpecStalkOverDiagram S s).obj W₀).hom).map a)
    ((Over.pullback ((fromSpecStalkOverDiagram S s).obj W₀).hom).map b) hlim
  refine ⟨W.objDown.opens, W.objDown.isAffineOpen, W.objDown.mem, ?_⟩
  let e := pullbackCompIso (S.homOfLE_ι hW.down.le)
  rw [← cancel_epi (e.hom.app X)]
  have ha := e.hom.naturality a
  have hb := e.hom.naturality b
  dsimp only [Functor.comp_map] at ha hb
  rw [← ha, ← hb]
  exact congrArg (· ≫ e.hom.app Y) heq

/-- Any morphism between pullbacks of `S`-schemes to `Spec 𝒪_{S, s}` descends to an affine open
neighbourhood of `s`, provided `X ⟶ S` is qcqs and `Y ⟶ S` is locally of finite presentation. -/
theorem exists_pullback_hom_fromSpecStalk {S : Scheme.{u}} (s : S)
    {X Y : Over S} [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    (φ : (Over.pullback (S.fromSpecStalk s)).obj X ⟶ (Over.pullback (S.fromSpecStalk s)).obj Y) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (hs : s ∈ W)
      (ψ : (Over.pullback W.ι).obj X ⟶ (Over.pullback W.ι).obj Y),
      (pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).inv.app X ≫
        (Over.pullback (W.fromSpecStalkOfMem s hs)).map ψ ≫
        (pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).hom.app Y = φ := by
  obtain ⟨W, ψ, hψ⟩ := exists_pullback_hom_of_isLimit (isLimitFromSpecStalkOverCone S s) φ
  exact ⟨W.objDown.opens, W.objDown.isAffineOpen, W.objDown.mem, ψ, hψ⟩

/-- Any isomorphism between pullbacks of `S`-schemes to `Spec 𝒪_{S, s}` descends to an affine open
neighbourhood of `s`, provided both `X ⟶ S` and `Y ⟶ S` are qcqs and locally of finite
presentation. -/
theorem exists_pullback_iso_fromSpecStalk {S : Scheme.{u}} (s : S)
    {X Y : Over S}
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [LocallyOfFinitePresentation Y.hom]
    (e : (Over.pullback (S.fromSpecStalk s)).obj X ≅ (Over.pullback (S.fromSpecStalk s)).obj Y) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (hs : s ∈ W)
      (eW : (Over.pullback W.ι).obj X ≅ (Over.pullback W.ι).obj Y),
      ((pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).app X).symm ≪≫
        (Over.pullback (W.fromSpecStalkOfMem s hs)).mapIso eW ≪≫
        (pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).app Y = e := by
  obtain ⟨W, eW, heW⟩ := exists_pullback_iso_of_isLimit (isLimitFromSpecStalkOverCone S s) e
  exact ⟨W.objDown.opens, W.objDown.isAffineOpen, W.objDown.mem, eW, heW⟩

end LocalSchemeLimit

section LocalSpreading

/-- Pulling back a scheme over an open subscheme `U ⊆ S` pushed forward to `S` along `f : T ⟶ S`
is naturally isomorphic to pulling back along `f ∣_ U` and pushing forward along `(f ⁻¹ᵁ U).ι`. -/
def pullbackMapOpenIso {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens) :
    Over.map U.ι ⋙ Over.pullback f ≅ Over.pullback (f ∣_ U) ⋙ Over.map (f ⁻¹ᵁ U).ι :=
  NatIso.ofComponents
    (fun A ↦
      let h := (IsPullback.of_hasPullback A.hom (f ∣_ U)).paste_vert
        (isPullback_morphismRestrict f U)
      Over.isoMk h.isoPullback.symm (by
        change h.isoPullback.inv ≫ pullback.snd A.hom (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι =
          pullback.snd (A.hom ≫ U.ι) f
        rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd]))
    fun {A B} g ↦ by
      ext1
      let hA := (IsPullback.of_hasPullback A.hom (f ∣_ U)).paste_vert
        (isPullback_morphismRestrict f U)
      let hB := (IsPullback.of_hasPullback B.hom (f ∣_ U)).paste_vert
        (isPullback_morphismRestrict f U)
      change ((Over.pullback f).map ((Over.map U.ι).map g)).left ≫ hB.isoPullback.inv =
        hA.isoPullback.inv ≫ ((Over.pullback (f ∣_ U)).map g).left
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      apply pullback.hom_ext
      · simp only [Category.assoc, Over.map_obj_hom, IsPullback.isoPullback_hom_fst,
          IsPullback.isoPullback_hom_fst_assoc, Over.pullback_map_left, Over.map_map_left,
          pullback.lift_fst]
      · simp only [Category.assoc, Over.map_obj_hom, IsPullback.isoPullback_hom_snd,
          Over.pullback_map_left, pullback.lift_snd_assoc, pullback.lift_snd]

/-- The canonical comparison morphism from the preimage of `W₁.ι ⁻¹ᵁ U` in `Spec 𝒪_{W₁, s}` to
the preimage of `U` in `Spec 𝒪_{S, s}`. -/
def stalkOpenRestriction {S : Scheme.{u}} (U W₁ : S.Opens) (s : S) (hs₁ : s ∈ W₁) :
    (W₁.toScheme.fromSpecStalk (⟨s, hs₁⟩ : W₁.toScheme) ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).toScheme ⟶
      (S.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  let σ : Spec (W₁.toScheme.presheaf.stalk s₁) ⟶ Spec (S.presheaf.stalk s) :=
    Spec.map (W₁.ι.stalkMap s₁)
  have hσ_S : σ ≫ S.fromSpecStalk s = W₁.toScheme.fromSpecStalk s₁ ≫ W₁.ι :=
    Scheme.SpecMap_stalkMap_fromSpecStalk W₁.ι (x := s₁)
  have hpre : W₁.toScheme.fromSpecStalk s₁ ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U) =
      σ ⁻¹ᵁ (S.fromSpecStalk s ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hσ_S]
  ((Spec _).isoOfEq hpre).hom ≫ (σ ∣_ (S.fromSpecStalk s ⁻¹ᵁ U))

/-- `stalkOpenRestriction` commutes with restriction of `fromSpecStalk` to `U`. -/
@[reassoc]
theorem stalkOpenRestriction_comp_morphismRestrict {S : Scheme.{u}} (U W₁ : S.Opens) (s : S)
    (hs₁ : s ∈ W₁) :
    stalkOpenRestriction U W₁ s hs₁ ≫ (S.fromSpecStalk s ∣_ U) =
      (W₁.toScheme.fromSpecStalk (⟨s, hs₁⟩ : W₁.toScheme) ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ∣_ U) := by
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  let σ : Spec (W₁.toScheme.presheaf.stalk s₁) ⟶ Spec (S.presheaf.stalk s) :=
    Spec.map (W₁.ι.stalkMap s₁)
  have hσ_S : σ ≫ S.fromSpecStalk s = W₁.toScheme.fromSpecStalk s₁ ≫ W₁.ι :=
    Scheme.SpecMap_stalkMap_fromSpecStalk W₁.ι (x := s₁)
  rw [← cancel_mono U.ι]
  dsimp only [stalkOpenRestriction]
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
    Scheme.isoOfEq_hom_ι_assoc]
  exact congrArg ((W₁.toScheme.fromSpecStalk s₁ ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).ι ≫ ·) hσ_S

/-- `stalkOpenRestriction` commutes with `fromSpecStalkOfMem` into `W₁`. -/
@[reassoc]
theorem stalkOpenRestriction_comp_ι_fromSpecStalkOfMem {S : Scheme.{u}} (U W₁ : S.Opens) (s : S)
    (hs₁ : s ∈ W₁) :
    stalkOpenRestriction U W₁ s hs₁ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫
        W₁.fromSpecStalkOfMem s hs₁ =
      (W₁.toScheme.fromSpecStalk (⟨s, hs₁⟩ : W₁.toScheme) ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ⁻¹ᵁ U).ι := by
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  let σ : Spec (W₁.toScheme.presheaf.stalk s₁) ⟶ Spec (S.presheaf.stalk s) :=
    Spec.map (W₁.ι.stalkMap s₁)
  have hσ_S : σ ≫ S.fromSpecStalk s = W₁.toScheme.fromSpecStalk s₁ ≫ W₁.ι :=
    Scheme.SpecMap_stalkMap_fromSpecStalk W₁.ι (x := s₁)
  have hσ : σ ≫ W₁.fromSpecStalkOfMem s hs₁ = W₁.toScheme.fromSpecStalk s₁ := by
    rw [← cancel_mono W₁.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hσ_S]
  dsimp only [stalkOpenRestriction]
  simp only [Category.assoc, morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc,
    morphismRestrict_ι]
  exact congrArg ((W₁.toScheme.fromSpecStalk s₁ ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).ι ≫ ·) hσ

/-- `stalkOpenRestriction` commutes with `S.fromSpecStalk s`. -/
@[reassoc]
theorem stalkOpenRestriction_comp_ι_fromSpecStalk {S : Scheme.{u}} (U W₁ : S.Opens) (s : S)
    (hs₁ : s ∈ W₁) :
    stalkOpenRestriction U W₁ s hs₁ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ S.fromSpecStalk s =
      (W₁.toScheme.fromSpecStalk (⟨s, hs₁⟩ : W₁.toScheme) ∣_ (W₁.ι ⁻¹ᵁ U)) ≫
        (W₁.ι ⁻¹ᵁ U).ι ≫ W₁.ι := by
  calc stalkOpenRestriction U W₁ s hs₁ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ S.fromSpecStalk s
      = (stalkOpenRestriction U W₁ s hs₁ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫
          W₁.fromSpecStalkOfMem s hs₁) ≫ W₁.ι := by
        simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    _ = _ := by rw [stalkOpenRestriction_comp_ι_fromSpecStalkOfMem, Category.assoc]

/-- For opens `U, W₁ ⊆ S` and `V ⊆ W₁`, canonical isomorphism between `U ⊓ (W₁.ι ''ᵁ V)` and
`V.ι ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)`. -/
def infImageOpenIso {S : Scheme.{u}} (U W₁ : S.Opens) (V : W₁.toScheme.Opens) :
    (U ⊓ (W₁.ι ''ᵁ V)).toScheme ≅ (V.ι ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (S.homOfLE (inf_le_left : U ⊓ (W₁.ι ''ᵁ V) ≤ U) ≫ U.ι)
    ((V.ι ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).ι ≫ V.ι ≫ W₁.ι) <| by
    rw [Scheme.homOfLE_ι, Scheme.Opens.range_ι]
    ext x
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨hxU, y, hyV, rfl⟩
      exact ⟨⟨⟨y, hyV⟩, hxU⟩, rfl⟩
    · rintro ⟨⟨⟨y, hyV⟩, hyU⟩, rfl⟩
      exact ⟨hyU, y, hyV, rfl⟩

/-- `infImageOpenIso` identifies the restriction of `V.ι ∣_ (W₁.ι ⁻¹ᵁ U) ≫ W₁.ι ∣_ U` with the
inclusion `U ⊓ (W₁.ι ''ᵁ V) ≤ U`. -/
@[reassoc]
theorem infImageOpenIso_hom_comp_left {S : Scheme.{u}} (U W₁ : S.Opens) (V : W₁.toScheme.Opens) :
    (infImageOpenIso U W₁ V).hom ≫ (V.ι ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ∣_ U) =
      S.homOfLE (inf_le_left : U ⊓ (W₁.ι ''ᵁ V) ≤ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    ← Category.assoc (V.ι ∣_ (W₁.ι ⁻¹ᵁ U)), morphismRestrict_ι, Category.assoc]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- `infImageOpenIso` identifies `(V.ι ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ⁻¹ᵁ U).ι` with the inclusion
`U ⊓ (W₁.ι ''ᵁ V) ≤ W₁.ι ''ᵁ V ≤ W₁`. -/
@[reassoc]
theorem infImageOpenIso_hom_comp_right {S : Scheme.{u}} (U W₁ : S.Opens) (V : W₁.toScheme.Opens) :
    (infImageOpenIso U W₁ V).hom ≫ (V.ι ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ⁻¹ᵁ U).ι =
      S.homOfLE (inf_le_right : U ⊓ (W₁.ι ''ᵁ V) ≤ W₁.ι ''ᵁ V) ≫
        S.homOfLE (W₁.ι_image_le V) := by
  rw [← cancel_mono W₁.ι]
  simp [infImageOpenIso, Category.assoc]

/-- Two morphisms into a pullback in `Over` are equal if their `pullback.fst` projections agree. -/
private lemma over_pullback_hom_ext {B T : Scheme.{u}} {f : T ⟶ B} {Z : Over T} {Y : Over B}
    {φ ψ : Z ⟶ (Over.pullback f).obj Y}
    (h : φ.left ≫ pullback.fst Y.hom f = ψ.left ≫ pullback.fst Y.hom f) : φ = ψ := by
  ext1
  apply pullback.hom_ext
  · exact h
  · exact (Over.w φ).trans (Over.w ψ).symm

/-- Two morphisms into a double pullback in `Over` are equal if their composite `pullback.fst`
projections agree. -/
private lemma over_pullback_pullback_hom_ext {A B C : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ C}
    {Z : Over A} {Y : Over C}
    {φ ψ : Z ⟶ (Over.pullback f).obj ((Over.pullback g).obj Y)}
    (h : φ.left ≫ pullback.fst (pullback.snd Y.hom g) f ≫ pullback.fst Y.hom g =
      ψ.left ≫ pullback.fst (pullback.snd Y.hom g) f ≫ pullback.fst Y.hom g) : φ = ψ := by
  apply over_pullback_hom_ext
  apply pullback.hom_ext
  · simpa only [Over.pullback_obj_hom, Category.assoc] using h
  · have hφ : φ.left ≫ pullback.snd (pullback.snd Y.hom g) f = Z.hom := Over.w φ
    have hψ : ψ.left ≫ pullback.snd (pullback.snd Y.hom g) f = Z.hom := Over.w ψ
    simp only [Over.pullback_obj_hom, Category.assoc, pullback.condition,
      reassoc_of% hφ, reassoc_of% hψ]

/-- Two morphisms into a triple pullback in `Over` are equal if their composite `pullback.fst`
projections agree. -/
private lemma over_pullback_pullback_pullback_hom_ext {A B C D : Scheme.{u}}
    {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {Z : Over A} {Y : Over D}
    {φ ψ : Z ⟶ (Over.pullback f).obj ((Over.pullback g).obj ((Over.pullback h).obj Y))}
    (heq : φ.left ≫ pullback.fst (pullback.snd (pullback.snd Y.hom h) g) f ≫
        pullback.fst (pullback.snd Y.hom h) g ≫ pullback.fst Y.hom h =
      ψ.left ≫ pullback.fst (pullback.snd (pullback.snd Y.hom h) g) f ≫
        pullback.fst (pullback.snd Y.hom h) g ≫ pullback.fst Y.hom h) : φ = ψ := by
  apply over_pullback_pullback_hom_ext
  apply pullback.hom_ext
  · simpa only [Over.pullback_obj_hom, Category.assoc] using heq
  · have hφ : φ.left ≫ pullback.snd (pullback.snd (pullback.snd Y.hom h) g) f = Z.hom := Over.w φ
    have hψ : ψ.left ≫ pullback.snd (pullback.snd (pullback.snd Y.hom h) g) f = Z.hom := Over.w ψ
    have hcond : pullback.fst (pullback.snd (pullback.snd Y.hom h) g) f ≫
          pullback.fst (pullback.snd Y.hom h) g ≫ pullback.snd Y.hom h =
        pullback.snd (pullback.snd (pullback.snd Y.hom h) g) f ≫ f ≫ g := by
      rw [pullback.condition, pullback.condition_assoc]
    simp only [Over.pullback_obj_hom, Category.assoc, hcond, reassoc_of% hφ, reassoc_of% hψ]

/-- **Spreading out an isomorphism from a local ring.** Given two quasi-compact, quasi-separated
schemes `Y₁, Y₂` locally of finite presentation over `S`, equipped with compatible isomorphisms
over a quasi-compact open `U ⊆ S` and over `Spec 𝒪_{S, s}`, there exist an affine open
neighbourhood `W` of `s` and an isomorphism over `U ⊔ W` restricting to both. -/
@[stacks 0BQ5]
theorem exists_iso_of_iso_fromSpecStalk {S : Scheme.{u}} (U : S.Opens)
    [QuasiCompact U.ι] (s : S) {Y₁ Y₂ : Over S}
    [QuasiCompact Y₁.hom] [QuasiSeparated Y₁.hom] [LocallyOfFinitePresentation Y₁.hom]
    [QuasiCompact Y₂.hom] [QuasiSeparated Y₂.hom] [LocallyOfFinitePresentation Y₂.hom]
    (eU : (Over.pullback U.ι).obj Y₁ ≅ (Over.pullback U.ι).obj Y₂)
    (es : (Over.pullback (S.fromSpecStalk s)).obj Y₁ ≅
      (Over.pullback (S.fromSpecStalk s)).obj Y₂)
    (he : (Over.pullback (S.fromSpecStalk s ∣_ U)).map eU.hom ≫
        (pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).hom.app Y₂ =
      (pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).hom.app Y₁ ≫
        (Over.pullback (S.fromSpecStalk s ⁻¹ᵁ U).ι).map es.hom) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (hs : s ∈ W)
      (eUW : (Over.pullback (U ⊔ W).ι).obj Y₁ ≅ (Over.pullback (U ⊔ W).ι).obj Y₂),
      (pullbackCompIso (S.homOfLE_ι (le_sup_left : U ≤ U ⊔ W))).inv.app Y₁ ≫
          (Over.pullback (S.homOfLE le_sup_left)).map eUW.hom ≫
          (pullbackCompIso (S.homOfLE_ι (le_sup_left : U ≤ U ⊔ W))).hom.app Y₂ =
        eU.hom ∧
      (pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s (Opens.mem_sup.mpr (Or.inr hs)))).inv.app
          Y₁ ≫
          (Over.pullback ((U ⊔ W).fromSpecStalkOfMem s (Opens.mem_sup.mpr (Or.inr hs)))).map
            eUW.hom ≫
          (pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s (Opens.mem_sup.mpr (Or.inr hs)))).hom.app
            Y₂ =
        es.hom := by
  -- Spread `es` to an affine open neighbourhood `W₁` of `s`.
  obtain ⟨W₁, _, hs₁, eW₁, heW₁⟩ := exists_pullback_iso_fromSpecStalk (X := Y₁) (Y := Y₂) s es
  have heW₁_hom : (pullbackCompIso (W₁.fromSpecStalkOfMem_ι s hs₁)).inv.app Y₁ ≫
      (Over.pullback (W₁.fromSpecStalkOfMem s hs₁)).map eW₁.hom ≫
      (pullbackCompIso (W₁.fromSpecStalkOfMem_ι s hs₁)).hom.app Y₂ = es.hom :=
    congrArg Iso.hom heW₁
  -- Compare `eW₁` and `eU` on `U₁ := W₁.ι ⁻¹ᵁ U`, pushed forward to `Over W₁`.
  let U₁ : W₁.toScheme.Opens := W₁.ι ⁻¹ᵁ U
  have hqcU₁ : QuasiCompact U₁.ι :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_morphismRestrict W₁.ι U)
      inferInstance
  let hsqW₁ : W₁.ι ∣_ U ≫ U.ι = U₁.ι ≫ W₁.ι := morphismRestrict_ι W₁.ι U
  let a : (Over.pullback U₁.ι).obj ((Over.pullback W₁.ι).obj Y₁) ⟶
      (Over.pullback U₁.ι).obj ((Over.pullback W₁.ι).obj Y₂) :=
    (Over.pullback U₁.ι).map eW₁.hom
  let b : (Over.pullback U₁.ι).obj ((Over.pullback W₁.ι).obj Y₁) ⟶
      (Over.pullback U₁.ι).obj ((Over.pullback W₁.ι).obj Y₂) :=
    (pullbackSquareIso hsqW₁).inv.app Y₁ ≫
      (Over.pullback (W₁.ι ∣_ U)).map eU.hom ≫
      (pullbackSquareIso hsqW₁).hom.app Y₂
  let X₁ : Over W₁.toScheme :=
    (Over.map U₁.ι).obj ((Over.pullback U₁.ι).obj ((Over.pullback W₁.ι).obj Y₁))
  let Z₁ : Over W₁.toScheme :=
    (Over.map U₁.ι).obj ((Over.pullback U₁.ι).obj ((Over.pullback W₁.ι).obj Y₂))
  have : QuasiCompact X₁.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι ≫ U₁.ι))
  have : LocallyOfFiniteType Z₁.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (pullback.snd Y₂.hom W₁.ι) U₁.ι ≫ U₁.ι))
  -- Show `a` and `b` agree over `Spec 𝒪_{W₁, s}`.
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  let p₁ : Spec (W₁.toScheme.presheaf.stalk s₁) ⟶ W₁.toScheme := W₁.toScheme.fromSpecStalk s₁
  let τ := stalkOpenRestriction U W₁ s hs₁
  have hτU : τ ≫ (S.fromSpecStalk s ∣_ U) = p₁ ∣_ U₁ ≫ W₁.ι ∣_ U :=
    stalkOpenRestriction_comp_morphismRestrict U W₁ s hs₁
  have hτW₁ : τ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ W₁.fromSpecStalkOfMem s hs₁ =
      p₁ ∣_ U₁ ≫ U₁.ι :=
    stalkOpenRestriction_comp_ι_fromSpecStalkOfMem U W₁ s hs₁
  have hτS : τ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ S.fromSpecStalk s =
      p₁ ∣_ U₁ ≫ U₁.ι ≫ W₁.ι :=
    stalkOpenRestriction_comp_ι_fromSpecStalk U W₁ s hs₁
  have hab_p₁ : (Over.pullback (p₁ ∣_ U₁)).map a = (Over.pullback (p₁ ∣_ U₁)).map b := by
    have hhe := congrArg (fun m ↦ m.left ≫ pullback.fst (pullback.snd Y₂.hom
        (S.fromSpecStalk s)) (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫
        pullback.fst Y₂.hom (S.fromSpecStalk s)) he
    dsimp only [Functor.comp_obj] at hhe
    simp only [Over.comp_left, Category.assoc, pullbackSquareIso_hom_app_left_fst_fst,
      Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc] at hhe
    have hheW₁ := congrArg (fun m ↦ m.left ≫ pullback.fst Y₂.hom (S.fromSpecStalk s)) heW₁_hom
    dsimp only [Functor.comp_obj] at hheW₁
    simp only [Over.comp_left, Category.assoc, pullbackCompIso_hom_app_left_fst,
      Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc] at hheW₁
    apply over_pullback_pullback_pullback_hom_ext
    dsimp only [a, b, Functor.comp_obj]
    simp only [CategoryTheory.Functor.map_comp, Over.comp_left, Category.assoc,
      pullbackSquareIso_hom_app_left_fst_fst, Over.pullback_map_left, Over.pullback_obj_hom,
      pullback.lift_fst_assoc]
    -- Transport both sides across `τ` via the pullback comparison into `S.fromSpecStalk s ⁻¹ᵁ U`.
    let q : pullback (pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι) (p₁ ∣_ U₁) ⟶
        pullback (pullback.snd Y₁.hom (S.fromSpecStalk s)) (S.fromSpecStalk s ⁻¹ᵁ U).ι :=
      pullback.lift
        (pullback.lift
          (pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst Y₁.hom W₁.ι)
          (pullback.snd _ _ ≫ τ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι)
          (by simp only [Category.assoc, hτS, pullback.condition, pullback.condition_assoc]))
        (pullback.snd _ _ ≫ τ) (by simp)
    have hq_left : q ≫ pullback.fst (pullback.snd Y₁.hom (S.fromSpecStalk s))
          (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫
          ((pullbackCompIso (W₁.fromSpecStalkOfMem_ι s hs₁)).inv.app Y₁).left ≫
          pullback.fst (pullback.snd Y₁.hom W₁.ι) (W₁.fromSpecStalkOfMem s hs₁) =
        pullback.fst (pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι) (p₁ ∣_ U₁) ≫
          pullback.fst (pullback.snd Y₁.hom W₁.ι) U₁.ι := by
      apply pullback.hom_ext
      · simp [q]
      · simp only [Category.assoc, pullbackCompIso_inv_app_left_fst_snd, q, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
        rw [hτW₁, pullback.condition, pullback.condition_assoc]
    have hq_right : q ≫ ((pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).inv.app
          Y₁).left ≫ pullback.fst (pullback.snd Y₁.hom U.ι) (S.fromSpecStalk s ∣_ U) =
        pullback.fst (pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι) (p₁ ∣_ U₁) ≫
          ((pullbackSquareIso hsqW₁).inv.app Y₁).left ≫
          pullback.fst (pullback.snd Y₁.hom U.ι) (W₁.ι ∣_ U) := by
      apply pullback.hom_ext
      · simp [q]
      · have h1 : ((pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).inv.app
            Y₁).left ≫ pullback.snd (pullback.snd Y₁.hom U.ι) (S.fromSpecStalk s ∣_ U) =
          pullback.snd (pullback.snd Y₁.hom (S.fromSpecStalk s))
            (S.fromSpecStalk s ⁻¹ᵁ U).ι := Over.w _
        have h2 : ((pullbackSquareIso hsqW₁).inv.app Y₁).left ≫
            pullback.snd (pullback.snd Y₁.hom U.ι) (W₁.ι ∣_ U) =
          pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι := Over.w _
        simp only [Category.assoc, pullback.condition, pullback.condition_assoc,
          reassoc_of% h1, reassoc_of% h2, q, pullback.lift_snd_assoc, hτU]
    have hcomp_s : pullback.fst (pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι) (p₁ ∣_ U₁) ≫
          pullback.fst (pullback.snd Y₁.hom W₁.ι) U₁.ι ≫
          eW₁.hom.left ≫ pullback.fst Y₂.hom W₁.ι =
        q ≫ pullback.fst (pullback.snd Y₁.hom (S.fromSpecStalk s))
          (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫
          es.hom.left ≫ pullback.fst Y₂.hom (S.fromSpecStalk s) := by
      rw [← hheW₁, ← reassoc_of% hq_left]
    have hcomp_U : pullback.fst (pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι) (p₁ ∣_ U₁) ≫
          ((pullbackSquareIso hsqW₁).inv.app Y₁).left ≫
          pullback.fst (pullback.snd Y₁.hom U.ι) (W₁.ι ∣_ U) ≫
          eU.hom.left ≫ pullback.fst Y₂.hom U.ι =
        q ≫ ((pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).inv.app
          Y₁).left ≫ pullback.fst (pullback.snd Y₁.hom U.ι) (S.fromSpecStalk s ∣_ U) ≫
          eU.hom.left ≫ pullback.fst Y₂.hom U.ι := by
      rw [reassoc_of% hq_right]
    rw [hcomp_s, hcomp_U]
    have hhe' := congrArg (fun m ↦ q ≫
      ((pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).inv.app Y₁).left ≫ m)
      hhe
    have hid : ((pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).inv.app
          Y₁).left ≫
        ((pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).hom.app
          Y₁).left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id_app]; rfl
    simpa only [Category.assoc, reassoc_of% hid] using hhe'.symm
  have hab_map : (Over.pullback p₁).map ((Over.map U₁.ι).map a) =
      (Over.pullback p₁).map ((Over.map U₁.ι).map b) := by
    rw [← cancel_mono ((pullbackMapOpenIso p₁ U₁).hom.app _)]
    have ha := (pullbackMapOpenIso p₁ U₁).hom.naturality a
    have hb := (pullbackMapOpenIso p₁ U₁).hom.naturality b
    dsimp only [Functor.comp_map] at ha hb
    rw [ha, hb, hab_p₁]
  -- Spread the equality `a = b` to an affine open neighbourhood `V ⊆ W₁` of `s`.
  obtain ⟨V, hV, hsV, hVeq⟩ := exists_pullback_map_eq_fromSpecStalk (S := W₁.toScheme)
    (X := X₁) (Y := Z₁) s₁ ((Over.map U₁.ι).map a) ((Over.map U₁.ι).map b) hab_map
  have hab_V : (Over.pullback (V.ι ∣_ U₁)).map a = (Over.pullback (V.ι ∣_ U₁)).map b := by
    apply (Over.fullyFaithfulMap (V.ι ⁻¹ᵁ U₁).ι).map_injective
    rw [← cancel_epi ((pullbackMapOpenIso V.ι U₁).hom.app _)]
    have ha := (pullbackMapOpenIso V.ι U₁).hom.naturality a
    have hb := (pullbackMapOpenIso V.ι U₁).hom.naturality b
    dsimp only [Functor.comp_map] at ha hb
    rw [← ha, ← hb, hVeq]
  -- Push `V` forward to `W := W₁.ι ''ᵁ V` and glue `eU` and `eW₁|_W` over `U ⊔ W`.
  let W : S.Opens := W₁.ι ''ᵁ V
  have hW : IsAffineOpen W := hV.image_of_isOpenImmersion W₁.ι
  have hWW₁ : W ≤ W₁ := W₁.ι_image_le V
  have hsW : s ∈ W := ⟨s₁, hsV, rfl⟩
  let eW : (Over.pullback W.ι).obj Y₁ ≅ (Over.pullback W.ι).obj Y₂ :=
    ((pullbackCompIso (S.homOfLE_ι hWW₁)).app Y₁).symm ≪≫
      (Over.pullback (S.homOfLE hWW₁)).mapIso eW₁ ≪≫
      (pullbackCompIso (S.homOfLE_ι hWW₁)).app Y₂
  -- Lift `eU` and `eW` to the pullbacks of `(Over.pullback (U ⊔ W).ι).obj Yᵢ`.
  let e₁ : (Over.pullback (S.homOfLE (le_sup_left : U ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₁) ≅
      (Over.pullback (S.homOfLE (le_sup_left : U ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₂) :=
    (pullbackCompIso (S.homOfLE_ι le_sup_left)).app Y₁ ≪≫
      eU ≪≫
      ((pullbackCompIso (S.homOfLE_ι le_sup_left)).app Y₂).symm
  let e₂ : (Over.pullback (S.homOfLE (le_sup_right : W ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₁) ≅
      (Over.pullback (S.homOfLE (le_sup_right : W ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₂) :=
    (pullbackCompIso (S.homOfLE_ι le_sup_right)).app Y₁ ≪≫
      eW ≪≫
      ((pullbackCompIso (S.homOfLE_ι le_sup_right)).app Y₂).symm
  have hpb := isPullback_opens_inf_le (X := S) (le_sup_left : U ≤ U ⊔ W) (le_sup_right : W ≤ U ⊔ W)
  have hcov := S.opensRange_homOfLE_sup U W
  -- Verify compatibility of `e₁` and `e₂` over `U ⊓ W` from `hab_V`.
  have he_compat : (Over.pullback (S.homOfLE (inf_le_left : U ⊓ W ≤ U))).map e₁.hom ≫
        (pullbackSquareIso hpb.w).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₂) =
      (pullbackSquareIso hpb.w).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₁) ≫
        (Over.pullback (S.homOfLE (inf_le_right : U ⊓ W ≤ W))).map e₂.hom := by
    let isoInf := infImageOpenIso U W₁ V
    have hisoInf_U : isoInf.hom ≫ (V.ι ∣_ U₁) ≫ (W₁.ι ∣_ U) = S.homOfLE inf_le_left :=
      infImageOpenIso_hom_comp_left U W₁ V
    have hisoInf_W : isoInf.hom ≫ (V.ι ∣_ U₁) ≫ U₁.ι =
        S.homOfLE inf_le_right ≫ S.homOfLE hWW₁ :=
      infImageOpenIso_hom_comp_right U W₁ V
    have hab_V_fst := congrArg (fun m ↦ m.left ≫
        pullback.fst (pullback.snd (pullback.snd Y₂.hom W₁.ι) U₁.ι) (V.ι ∣_ U₁) ≫
        pullback.fst (pullback.snd Y₂.hom W₁.ι) U₁.ι ≫
        pullback.fst Y₂.hom W₁.ι) hab_V
    dsimp only [a, b, Functor.comp_obj] at hab_V_fst
    simp only [CategoryTheory.Functor.map_comp, Over.comp_left, Category.assoc,
      pullbackSquareIso_hom_app_left_fst_fst, Over.pullback_map_left, Over.pullback_obj_hom,
      pullback.lift_fst_assoc] at hab_V_fst
    have hsq₁ := pullbackSquareIso_hom_app_left_fst_fst hpb.w ((Over.pullback (U ⊔ W).ι).obj Y₁)
    have hsq₂ := pullbackSquareIso_hom_app_left_fst_fst hpb.w ((Over.pullback (U ⊔ W).ι).obj Y₂)
    dsimp only [Over.pullback_obj_hom] at hsq₁ hsq₂
    apply over_pullback_pullback_pullback_hom_ext
    dsimp only [e₁, e₂, eW, Functor.comp_obj]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
      CategoryTheory.Functor.map_comp, Over.comp_left, Category.assoc, reassoc_of% hsq₂,
      pullbackCompIso_hom_app_left_fst, pullbackCompIso_inv_app_left_fst_fst,
      Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc]
    -- Map the triple pullback over `U ⊓ W` into the triple pullback over `V.ι ⁻¹ᵁ U₁`.
    let q : pullback (pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
          (S.homOfLE le_sup_left)) (S.homOfLE inf_le_left) ⟶
        pullback (pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι) (V.ι ∣_ U₁) :=
      pullback.lift
        (pullback.lift
          (pullback.lift
            (pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst Y₁.hom (U ⊔ W).ι)
            (pullback.snd _ _ ≫ S.homOfLE inf_le_right ≫ S.homOfLE hWW₁)
            (by simp [pullback.condition, pullback.condition_assoc]))
          (pullback.snd _ _ ≫ isoInf.hom ≫ (V.ι ∣_ U₁))
          (by simp only [pullback.lift_snd, Category.assoc, hisoInf_W]))
        (pullback.snd _ _ ≫ isoInf.hom) (by simp)
    have hq_W₁ : q ≫ pullback.fst _ _ ≫ pullback.fst (pullback.snd Y₁.hom W₁.ι) U₁.ι =
        ((pullbackSquareIso hpb.w).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₁)).left ≫
          pullback.fst (pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
            (S.homOfLE le_sup_right)) (S.homOfLE inf_le_right) ≫
          ((pullbackCompIso (S.homOfLE_ι le_sup_right)).hom.app Y₁).left ≫
          ((pullbackCompIso (S.homOfLE_ι hWW₁)).inv.app Y₁).left ≫
          pullback.fst (pullback.snd Y₁.hom W₁.ι) (S.homOfLE hWW₁) := by
      apply pullback.hom_ext
      · simp only [q, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst,
          pullbackCompIso_inv_app_left_fst_fst, pullbackCompIso_hom_app_left_fst,
          reassoc_of% hsq₁]
      · simp only [Category.assoc, pullbackCompIso_inv_app_left_fst_snd, q, pullback.lift_fst_assoc,
          pullback.lift_snd]
        have h1 : ((pullbackCompIso (S.homOfLE_ι le_sup_right)).hom.app Y₁).left ≫
              pullback.snd Y₁.hom W.ι =
            pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι) (S.homOfLE le_sup_right) := Over.w _
        have h2 : ((pullbackSquareIso hpb.w).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₁)).left ≫
              pullback.snd (pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
                (S.homOfLE le_sup_right)) (S.homOfLE inf_le_right) =
            pullback.snd (pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
              (S.homOfLE le_sup_left)) (S.homOfLE inf_le_left) := Over.w _
        simp only [reassoc_of% h1, pullback.condition_assoc, reassoc_of% h2]
    have hq_U : q ≫ pullback.fst _ _ ≫ ((pullbackSquareIso hsqW₁).inv.app Y₁).left ≫
          pullback.fst (pullback.snd Y₁.hom U.ι) (W₁.ι ∣_ U) =
        pullback.fst (pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
          (S.homOfLE le_sup_left)) (S.homOfLE inf_le_left) ≫
          ((pullbackCompIso (S.homOfLE_ι le_sup_left)).hom.app Y₁).left := by
      apply pullback.hom_ext
      · simp [q]
      · have h1 : ((pullbackSquareIso hsqW₁).inv.app Y₁).left ≫
              pullback.snd (pullback.snd Y₁.hom U.ι) (W₁.ι ∣_ U) =
            pullback.snd (pullback.snd Y₁.hom W₁.ι) U₁.ι := Over.w _
        have h2 : ((pullbackCompIso (S.homOfLE_ι le_sup_left)).hom.app Y₁).left ≫
              pullback.snd Y₁.hom U.ι =
            pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι) (S.homOfLE le_sup_left) := Over.w _
        simp only [Category.assoc, pullback.condition, reassoc_of% h1, h2, q,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, hisoInf_U]
    have h := congrArg (q ≫ ·) hab_V_fst
    rw [reassoc_of% hq_W₁, reassoc_of% hq_U] at h
    exact h.symm
  -- Glue `e₁` and `e₂` to an isomorphism over `U ⊔ W`.
  let eUW : (Over.pullback (U ⊔ W).ι).obj Y₁ ≅ (Over.pullback (U ⊔ W).ι).obj Y₂ :=
    glueOverIso hpb hcov e₁ e₂ he_compat
  refine ⟨W, hW, hsW, eUW, ?_, ?_⟩
  · have hL : (Over.pullback (S.homOfLE (le_sup_left : U ≤ U ⊔ W))).map eUW.hom = e₁.hom :=
      congrArg Iso.hom (pullback_mapIso_glueOverIso_left hpb hcov e₁ e₂ he_compat)
    rw [hL]
    simp [e₁]
  · have hR : (Over.pullback (S.homOfLE (le_sup_right : W ≤ U ⊔ W))).map eUW.hom = e₂.hom :=
      congrArg Iso.hom (pullback_mapIso_glueOverIso_right hpb hcov e₁ e₂ he_compat)
    have hstalk_sup : W.fromSpecStalkOfMem s hsW ≫ S.homOfLE le_sup_right =
        (U ⊔ W).fromSpecStalkOfMem s (Opens.mem_sup.mpr (Or.inr hsW)) := by
      rw [← cancel_mono (U ⊔ W).ι, Category.assoc, Scheme.homOfLE_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
    have hstalk_W₁ : W.fromSpecStalkOfMem s hsW ≫ S.homOfLE hWW₁ =
        W₁.fromSpecStalkOfMem s hs₁ := by
      rw [← cancel_mono W₁.ι, Category.assoc, Scheme.homOfLE_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
    -- Compare both sides with `heW₁_hom` by pulling back along `W.fromSpecStalkOfMem s hsW`.
    apply over_pullback_hom_ext
    have hR' := congrArg (fun m ↦
      ((pullbackCompIso hstalk_sup).inv.app ((Over.pullback (U ⊔ W).ι).obj Y₁)).left ≫
      ((Over.pullback (W.fromSpecStalkOfMem s hsW)).map m).left ≫
      ((pullbackCompIso hstalk_sup).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₂)).left ≫
      ((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
        (Opens.mem_sup.mpr (Or.inr hsW)))).hom.app Y₂).left ≫
      pullback.fst Y₂.hom (S.fromSpecStalk s)) hR
    have hR_lhs : ((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
          (Opens.mem_sup.mpr (Or.inr hsW)))).inv.app Y₁).left ≫
        ((pullbackCompIso hstalk_sup).inv.app ((Over.pullback (U ⊔ W).ι).obj Y₁)).left ≫
        ((Over.pullback (W.fromSpecStalkOfMem s hsW)).map
          ((Over.pullback (S.homOfLE le_sup_right)).map eUW.hom)).left ≫
        ((pullbackCompIso hstalk_sup).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₂)).left ≫
        ((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
          (Opens.mem_sup.mpr (Or.inr hsW)))).hom.app Y₂).left ≫
        pullback.fst Y₂.hom (S.fromSpecStalk s) =
      (((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
          (Opens.mem_sup.mpr (Or.inr hsW)))).inv.app Y₁ ≫
          (Over.pullback ((U ⊔ W).fromSpecStalkOfMem s
            (Opens.mem_sup.mpr (Or.inr hsW)))).map eUW.hom ≫
          (pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
            (Opens.mem_sup.mpr (Or.inr hsW)))).hom.app Y₂).left) ≫
        pullback.fst Y₂.hom (S.fromSpecStalk s) := by
      have hnat := (pullbackCompIso hstalk_sup).hom.naturality eUW.hom
      dsimp only [Functor.comp_map] at hnat
      have hnat' := congrArg (fun m ↦ ((pullbackCompIso
          ((U ⊔ W).fromSpecStalkOfMem_ι s (Opens.mem_sup.mpr (Or.inr hsW)))).inv.app Y₁ ≫
        (pullbackCompIso hstalk_sup).inv.app ((Over.pullback (U ⊔ W).ι).obj Y₁) ≫ m ≫
        (pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
          (Opens.mem_sup.mpr (Or.inr hsW)))).hom.app Y₂).left ≫
        pullback.fst Y₂.hom (S.fromSpecStalk s)) hnat
      simp only [Over.comp_left, Category.assoc, Iso.inv_hom_id_app_assoc] at hnat'
      exact hnat'
    have hR_rhs : ((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
          (Opens.mem_sup.mpr (Or.inr hsW)))).inv.app Y₁).left ≫
        ((pullbackCompIso hstalk_sup).inv.app ((Over.pullback (U ⊔ W).ι).obj Y₁)).left ≫
        ((Over.pullback (W.fromSpecStalkOfMem s hsW)).map e₂.hom).left ≫
        ((pullbackCompIso hstalk_sup).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₂)).left ≫
        ((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
          (Opens.mem_sup.mpr (Or.inr hsW)))).hom.app Y₂).left ≫
        pullback.fst Y₂.hom (S.fromSpecStalk s) =
      es.hom.left ≫ pullback.fst Y₂.hom (S.fromSpecStalk s) := by
      have hheW₁ := congrArg (fun m ↦ m.left ≫ pullback.fst Y₂.hom (S.fromSpecStalk s)) heW₁_hom
      dsimp only [Functor.comp_obj] at hheW₁
      simp only [Over.comp_left, Category.assoc, pullbackCompIso_hom_app_left_fst,
        Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc] at hheW₁
      rw [← hheW₁]
      dsimp only [e₂, eW, Functor.comp_obj]
      have hhom := pullbackCompIso_hom_app_left_fst hstalk_sup ((Over.pullback (U ⊔ W).ι).obj Y₂)
      dsimp only [Over.pullback_obj_hom] at hhom
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
        CategoryTheory.Functor.map_comp, Over.comp_left, Category.assoc,
        pullbackCompIso_hom_app_left_fst, reassoc_of% hhom,
        pullbackCompIso_inv_app_left_fst_fst, Over.pullback_map_left, Over.pullback_obj_hom,
        pullback.lift_fst_assoc]
      suffices h :
          ((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
            (Opens.mem_sup.mpr (Or.inr hsW)))).inv.app Y₁).left ≫
          ((pullbackCompIso hstalk_sup).inv.app ((Over.pullback (U ⊔ W).ι).obj Y₁)).left ≫
          pullback.fst (pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
            (S.homOfLE le_sup_right)) (W.fromSpecStalkOfMem s hsW) ≫
          ((pullbackCompIso (S.homOfLE_ι le_sup_right)).hom.app Y₁).left ≫
          ((pullbackCompIso (S.homOfLE_ι hWW₁)).inv.app Y₁).left ≫
          pullback.fst (pullback.snd Y₁.hom W₁.ι) (S.homOfLE hWW₁) =
          ((pullbackCompIso (W₁.fromSpecStalkOfMem_ι s hs₁)).inv.app Y₁).left ≫
          pullback.fst (pullback.snd Y₁.hom W₁.ι) (W₁.fromSpecStalkOfMem s hs₁) by
        simpa only [Category.assoc] using
          congrArg (· ≫ eW₁.hom.left ≫ pullback.fst Y₂.hom W₁.ι) h
      apply pullback.hom_ext
      · have hinv := pullbackCompIso_inv_app_left_fst_fst hstalk_sup
          ((Over.pullback (U ⊔ W).ι).obj Y₁)
        dsimp only [Over.pullback_obj_hom] at hinv
        simp [reassoc_of% hinv]
      · have h1 : ((pullbackCompIso (S.homOfLE_ι le_sup_right)).hom.app Y₁).left ≫
              pullback.snd Y₁.hom W.ι =
            pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι) (S.homOfLE le_sup_right) := Over.w _
        have h2 : ((pullbackCompIso hstalk_sup).inv.app ((Over.pullback (U ⊔ W).ι).obj Y₁)).left ≫
              pullback.snd (pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
                (S.homOfLE le_sup_right)) (W.fromSpecStalkOfMem s hsW) =
            pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
              ((U ⊔ W).fromSpecStalkOfMem s (Opens.mem_sup.mpr (Or.inr hsW))) := Over.w _
        have h3 : ((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
              (Opens.mem_sup.mpr (Or.inr hsW)))).inv.app Y₁).left ≫
              pullback.snd (pullback.snd Y₁.hom (U ⊔ W).ι)
                ((U ⊔ W).fromSpecStalkOfMem s (Opens.mem_sup.mpr (Or.inr hsW))) =
            pullback.snd Y₁.hom (S.fromSpecStalk s) := Over.w _
        simp only [Category.assoc, pullbackCompIso_inv_app_left_fst_snd,
          reassoc_of% h1, pullback.condition_assoc, reassoc_of% h2, reassoc_of% h3, hstalk_W₁]
    rw [← hR_lhs, congrArg (((pullbackCompIso ((U ⊔ W).fromSpecStalkOfMem_ι s
      (Opens.mem_sup.mpr (Or.inr hsW)))).inv.app Y₁).left ≫ ·) hR', hR_rhs]

end LocalSpreading

end TauCeti.AlgebraicGeometry
