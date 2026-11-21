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
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.CategoryTheory.Comma.Over

/-!
# Spreading out morphisms and isomorphisms across cofiltered limits

Let `D : I ⥤ Over S` be a cofiltered diagram of schemes over `S` with affine transition maps and
limit cone `c`. Pulling `c` back along a morphism `X ⟶ S` yields a cofiltered limit cone of
schemes with affine transition maps, whose terms remain quasi-compact (resp. quasi-separated) when
the terms of `D` and the morphism `X ⟶ S` are. Applying Mathlib's spreading-out lemmas from
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` to this pulled-back limit cone gives spreading
of equalities of morphisms, morphisms, and isomorphisms between pullbacks of `S`-schemes across
the limit (Stacks, Tags 01ZM and 01ZN).

For any scheme `S` and point `s : S`, the local scheme `Spec 𝒪_{S, s}` is the cofiltered limit in
`Over S` of the affine open neighbourhoods `W` of `s`. Specializing the general limit-spreading
results to this cone spreads equalities, morphisms, and isomorphisms from `Spec 𝒪_{S, s}` to an
affine open neighbourhood of `s`, with no germ-injectivity or Noetherian assumptions. Combining
this with two-open gluing in `Over` spreads compatible isomorphisms given over a quasi-compact open
`U ⊆ S` and over `Spec 𝒪_{S, s}` to `U ⊔ W` for an affine open neighbourhood `W` of `s`
(Stacks, Lemma 32.20.3 (0BQ5)).

## Main declarations

* `AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_homOfLE`: functoriality of
  `fromSpecStalkOfMem` with respect to open inclusions `W ≤ W'`.
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
* `TauCeti.AlgebraicGeometry.stalkOpenRestriction`: open-subscheme compatibility helper for
  restricting `Spec 𝒪_{S, s}` along open inclusions.
* `TauCeti.AlgebraicGeometry.quasiCompact_ι_preimage`,
  `TauCeti.AlgebraicGeometry.affineImage_fromSpecStalkOfMem`: shared open-image and
  quasi-compactness helpers for spreading out across local rings.
* `TauCeti.AlgebraicGeometry.exists_iso_of_iso_fromSpecStalk`: spreading compatible isomorphisms
  over a quasi-compact open `U` and `Spec 𝒪_{S, s}` to `U ⊔ W` (Stacks, Lemma 32.20.3 (0BQ5)).

## References

* [The Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [The Stacks Project, Tag 01ZN](https://stacks.math.columbia.edu/tag/01ZN)
* [The Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5)
-/

public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Opens

/-- `fromSpecStalkOfMem` is compatible with open inclusions `W ≤ W'`. -/
@[reassoc (attr := simp)]
theorem fromSpecStalkOfMem_homOfLE {S : Scheme.{u}} (W : S.Opens) {W' : S.Opens}
    (h : W ≤ W') (s : S) (hs : s ∈ W) :
    W.fromSpecStalkOfMem s hs ≫ S.homOfLE h = W'.fromSpecStalkOfMem s (h hs) := by
  rw [← cancel_mono W'.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]

end AlgebraicGeometry.Scheme.Opens

namespace TauCeti.AlgebraicGeometry

section LimitSpreading

variable {S : Scheme.{u}} {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Over S} [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
  {c : Cone D} (hc : IsLimit c)

private instance isAffineHom_pullback_map (X : Over S) {i j : I} (f : i ⟶ j) :
    IsAffineHom ((D ⋙ Over.pullback X.hom ⋙ Over.forget X.left).map f) := by
  have houter : IsPullback (pullback.snd (D.obj i).hom X.hom) (pullback.fst (D.obj i).hom X.hom)
      X.hom ((D.map f).left ≫ (D.obj j).hom) := by
    rw [Over.w (D.map f)]; exact (IsPullback.of_hasPullback (D.obj i).hom X.hom).flip
  have hpb : IsPullback (pullback.fst (D.obj i).hom X.hom)
      ((D ⋙ Over.pullback X.hom ⋙ Over.forget X.left).map f)
      (D.map f).left (pullback.fst (D.obj j).hom X.hom) := by
    refine (IsPullback.of_right (h₁₂ := pullback.snd (D.obj j).hom X.hom) (v₁₃ := X.hom) ?_ ?_
      (IsPullback.of_hasPullback (D.obj j).hom X.hom).flip).flip
    · simpa [Over.pullback_map_left] using houter
    · simp [Over.pullback_map_left]
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hpb inferInstance

private def pullbackToBaseNatTrans (D : I ⥤ Over S) (X : Over S) :
    (D ⋙ Over.pullback X.hom ⋙ Over.forget X.left) ⟶ (Functor.const I).obj S where
  app i := pullback.snd (D.obj i).hom X.hom ≫ X.hom
  naturality _ _ f := by simp [Over.pullback_map_left]

private lemma pullbackSymmetry_comp_pullbackCompIso_inv {T' T : Over S} (u : T' ⟶ T) (X : Over S) :
    (pullbackSymmetry T'.hom X.hom).hom ≫
        ((Over.pullbackCompIso (Over.w u)).inv.app X).left ≫
          pullback.fst (pullback.snd X.hom T.hom) u.left =
      ((Over.pullback X.hom).map u).left ≫ (pullbackSymmetry T.hom X.hom).hom := by
  apply pullback.hom_ext <;> simp [Over.pullback_map_left]

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
  let mk (m : (Over.pullback (D.obj i).hom).obj X ⟶ (Over.pullback (D.obj i).hom).obj Y) :
      DX.obj i ⟶ Y.left :=
    (pullbackSymmetry (D.obj i).hom X.hom).hom ≫ m.left ≫ pullback.fst Y.hom (D.obj i).hom
  have hmk (m : (Over.pullback (D.obj i).hom).obj X ⟶ (Over.pullback (D.obj i).hom).obj Y) :
      (pullbackToBaseNatTrans D X).app i = mk m ≫ Y.hom := by
    have hw : m.left ≫ pullback.snd Y.hom (D.obj i).hom = pullback.snd X.hom (D.obj i).hom :=
      Over.w m
    simp only [pullbackToBaseNatTrans, mk, Category.assoc, pullback.condition, reassoc_of% hw,
      pullbackSymmetry_hom_comp_snd_assoc]
  have hab' : cX.π.app i ≫ mk a = cX.π.app i ≫ mk b := by
    have hcomp_eq := congrArg (fun m ↦ m.left ≫ pullback.fst _ _) hab
    simp only [Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst] at hcomp_eq
    have hsym := pullbackSymmetry_comp_pullbackCompIso_inv (T' := c.pt) (c.π.app i) X
    simp only [cX, Functor.mapCone_π_app, Functor.comp_map, Over.forget_map, mk,
      ← reassoc_of% hsym]
    rw [reassoc_of% hcomp_eq]
  obtain ⟨k, hik, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    DX (pullbackToBaseNatTrans D X) Y.hom cX hcX (mk a) (mk b) (hmk a) (hmk b) hab'
  refine ⟨k, hik, Over.pullback_hom_ext ?_⟩
  simp only [Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst]
  apply pullback.hom_ext
  · have hsym := pullbackSymmetry_comp_pullbackCompIso_inv (D.map hik) X
    have heq' := congrArg (fun m ↦ ((Over.pullbackCompIso (Over.w (D.map hik))).hom.app X).left ≫
      (pullbackSymmetry (D.obj k).hom X.hom).inv ≫ m) heq
    have hid : ((Over.pullbackCompIso (Over.w (D.map hik))).hom.app X).left ≫
        ((Over.pullbackCompIso (Over.w (D.map hik))).inv.app X).left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.hom_inv_id_app]; rfl
    simp only [DX, mk, Functor.comp_map, Over.forget_map, ← reassoc_of% hsym,
      Iso.inv_hom_id_assoc, reassoc_of% hid] at heq'
    simpa only [Category.assoc] using heq'
  · have hwa : a.left ≫ pullback.snd Y.hom (D.obj i).hom = pullback.snd X.hom (D.obj i).hom :=
      Over.w a
    have hwb : b.left ≫ pullback.snd Y.hom (D.obj i).hom = pullback.snd X.hom (D.obj i).hom :=
      Over.w b
    simp only [Category.assoc, hwa, hwb]

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
      (Over.pullbackCompIso
          (Over.w (c.π.app i) : (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).inv.app X ≫
        (Over.pullback (c.π.app i).left).map ψ ≫
        (Over.pullbackCompIso
          (Over.w (c.π.app i) : (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).hom.app Y = φ := by
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
    have hw : φ.left ≫ pullback.snd Y.hom c.pt.hom = pullback.snd X.hom c.pt.hom := Over.w φ
    simp [pullbackToBaseNatTrans, a, cX, Category.assoc, pullback.condition, reassoc_of% hw,
      pullbackSymmetry_hom_comp_snd_assoc, Over.pullback_map_left]
  obtain ⟨i, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    DX (pullbackToBaseNatTrans D X) Y.hom cX hcX a ha
  let ψ : (Over.pullback (D.obj i).hom).obj X ⟶ (Over.pullback (D.obj i).hom).obj Y :=
    Over.homMk (pullback.lift ((pullbackSymmetry (D.obj i).hom X.hom).inv ≫ g)
      (pullback.snd X.hom (D.obj i).hom) (by
        rw [Category.assoc, hg']; simp [pullbackToBaseNatTrans, pullback.condition])) (by simp)
  refine ⟨i, ψ, Over.pullback_hom_ext ?_⟩
  simp only [Over.comp_left, Category.assoc, Over.pullbackCompIso_hom_app_left_fst,
    Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc, pullback.lift_fst,
    ψ, Over.homMk_left]
  have hsym := pullbackSymmetry_comp_pullbackCompIso_inv (T' := c.pt) (c.π.app i) X
  rw [← cancel_epi (pullbackSymmetry c.pt.hom X.hom).hom, reassoc_of% hsym, Iso.hom_inv_id_assoc]
  simpa [cX, a] using hg

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
      ((Over.pullbackCompIso (Over.w (c.π.app i) :
          (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).app X).symm ≪≫
        (Over.pullback (c.π.app i).left).mapIso eᵢ ≪≫
        (Over.pullbackCompIso (Over.w (c.π.app i) :
          (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom)).app Y = e := by
  obtain ⟨i₁, ψ₁, hψ₁⟩ := exists_pullback_hom_of_isLimit hc e.hom
  obtain ⟨i₂, ψ₂, hψ₂⟩ := exists_pullback_hom_of_isLimit hc e.inv
  rw [← Over.conjPullback_eq] at hψ₁ hψ₂
  let i₀ := IsCofiltered.min i₁ i₂
  let f₁ : i₀ ⟶ i₁ := IsCofiltered.minToLeft i₁ i₂
  let f₂ : i₀ ⟶ i₂ := IsCofiltered.minToRight i₁ i₂
  let g := Over.conjPullback (Over.w (D.map f₁)) ψ₁
  let h := Over.conjPullback (Over.w (D.map f₂)) ψ₂
  have hg : Over.conjPullback (Over.w (c.π.app i₀)) g = e.hom :=
    (Over.conjPullback_conjPullback (congrArg (·.left) (c.w f₁)) _ _ _ ψ₁).trans hψ₁
  have hh : Over.conjPullback (Over.w (c.π.app i₀)) h = e.inv :=
    (Over.conjPullback_conjPullback (congrArg (·.left) (c.w f₂)) _ _ _ ψ₂).trans hψ₂
  have hgh : (Over.pullback (c.π.app i₀).left).map (g ≫ h) =
      (Over.pullback (c.π.app i₀).left).map (𝟙 _) :=
    Over.conjPullback_injective (Over.w (c.π.app i₀)) (by
      rw [← Over.conjPullback_comp, hg, hh, Iso.hom_inv_id, Over.conjPullback_id])
  obtain ⟨k₁, fk₁, hfk₁⟩ := exists_pullback_map_eq_of_isLimit hc (g ≫ h) (𝟙 _) hgh
  let g₁ := Over.conjPullback (Over.w (D.map fk₁)) g
  let h₁ := Over.conjPullback (Over.w (D.map fk₁)) h
  have hg₁h₁ : g₁ ≫ h₁ = 𝟙 _ := by
    rw [Over.conjPullback_comp, Over.conjPullback_eq, hfk₁, ← Over.conjPullback_eq,
      Over.conjPullback_id]
  have hg₁ : Over.conjPullback (Over.w (c.π.app k₁)) g₁ = e.hom :=
    (Over.conjPullback_conjPullback (congrArg (·.left) (c.w fk₁)) _ _ _ g).trans hg
  have hh₁ : Over.conjPullback (Over.w (c.π.app k₁)) h₁ = e.inv :=
    (Over.conjPullback_conjPullback (congrArg (·.left) (c.w fk₁)) _ _ _ h).trans hh
  have hh₁g₁ : (Over.pullback (c.π.app k₁).left).map (h₁ ≫ g₁) =
      (Over.pullback (c.π.app k₁).left).map (𝟙 _) :=
    Over.conjPullback_injective (Over.w (c.π.app k₁)) (by
      rw [← Over.conjPullback_comp, hh₁, hg₁, Iso.inv_hom_id, Over.conjPullback_id])
  obtain ⟨k, fk, hfk⟩ := exists_pullback_map_eq_of_isLimit hc (h₁ ≫ g₁) (𝟙 _) hh₁g₁
  refine ⟨k, ⟨Over.conjPullback (Over.w (D.map fk)) g₁, Over.conjPullback (Over.w (D.map fk)) h₁,
    by rw [Over.conjPullback_comp, hg₁h₁, Over.conjPullback_id],
    by rw [Over.conjPullback_comp, Over.conjPullback_eq, hfk, ← Over.conjPullback_eq,
      Over.conjPullback_id]⟩, Iso.ext ?_⟩
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
    ← Over.conjPullback_eq] using
    (Over.conjPullback_conjPullback (congrArg (·.left) (c.w fk)) _ _ _ g₁).trans hg₁

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
        (show s ∈ (U.opens ⊓ V.opens : Set S) from ⟨U.mem, V.mem⟩) (U.opens ⊓ V.opens).isOpen
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
      S.isBasis_affineOpens.exists_subset_of_mem_open U.property U.val.isOpen
    have : Nonempty (CostructuredArrow (toOpenNhds S s) U) :=
      ⟨CostructuredArrow.mk (Y := ⟨W₀, hW₀, hsW₀⟩)
        (homOfLE (show (toOpenNhds S s).obj ⟨W₀, hW₀, hsW₀⟩ ≤ U from hW₀U))⟩
    refine zigzag_isConnected fun X Y ↦ ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hsW, hWle⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show s ∈ (X.left.opens ⊓ Y.left.opens : Set S) from ⟨X.left.mem, Y.left.mem⟩)
        (X.left.opens ⊓ Y.left.opens).isOpen
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
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, fromSpecStalkOverDiagram,
          Over.comp_left, Over.id_left, Over.homMk, CostructuredArrow.homMk, Over.Hom.left]
        rw [Category.id_comp, Scheme.Opens.fromSpecStalkOfMem_homOfLE] }

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
      simp only [Functor.comp_map, fromSpecStalkOverDiagram_map, IsAffineOpen.isoSpec_hom,
        Functor.rightOp_map, Scheme.Spec_map, Functor.op_map]
      exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map W₁.objDown.opens W₂.objDown.opens
        f.down.le).symm
  let eCone : (Over.forget S).mapCone (fromSpecStalkOverCone S s) ≅
      (Cone.postcompose eDiag.inv).obj specCone :=
    Cone.ext (Iso.refl _) fun W ↦ by
      -- Unfold `fromSpecStalkOverCone`, `eDiag`, and `specCone`; `Over.homMk` and
      -- `NatIso.ofComponents` store non-reducible `fromSpecStalkOverDiagram` endpoints that `rw`
      -- cannot match under `implicit` transparency.
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
  have hlim : (Over.pullback (W₀.objDown.opens.fromSpecStalkOfMem s W₀.objDown.mem)).map
        ((Over.pullback W₀.objDown.opens.ι).map a) =
      (Over.pullback (W₀.objDown.opens.fromSpecStalkOfMem s W₀.objDown.mem)).map
        ((Over.pullback W₀.objDown.opens.ι).map b) := by
    let e := Over.pullbackCompIso (W₀.objDown.opens.fromSpecStalkOfMem_ι s W₀.objDown.mem)
    rw [← cancel_mono (e.hom.app Y)]
    have ha := e.hom.naturality a
    have hb := e.hom.naturality b
    dsimp only [Functor.comp_map] at ha hb
    rw [ha, hb, hab]
  obtain ⟨W, hW, heq⟩ := exists_pullback_map_eq_of_isLimit (isLimitFromSpecStalkOverCone S s)
    ((Over.pullback ((fromSpecStalkOverDiagram S s).obj W₀).hom).map a)
    ((Over.pullback ((fromSpecStalkOverDiagram S s).obj W₀).hom).map b) hlim
  refine ⟨W.objDown.opens, W.objDown.isAffineOpen, W.objDown.mem, ?_⟩
  let e := Over.pullbackCompIso (S.homOfLE_ι hW.down.le)
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
      (Over.pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).inv.app X ≫
        (Over.pullback (W.fromSpecStalkOfMem s hs)).map ψ ≫
        (Over.pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).hom.app Y = φ := by
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
      ((Over.pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).app X).symm ≪≫
        (Over.pullback (W.fromSpecStalkOfMem s hs)).mapIso eW ≪≫
        (Over.pullbackCompIso (W.fromSpecStalkOfMem_ι s hs)).app Y = e := by
  obtain ⟨W, eW, heW⟩ := exists_pullback_iso_of_isLimit (isLimitFromSpecStalkOverCone S s) e
  exact ⟨W.objDown.opens, W.objDown.isAffineOpen, W.objDown.mem, eW, heW⟩

end LocalSchemeLimit

section LocalSpreading

private def stalkMapSpec {S : Scheme.{u}} (W₁ : S.Opens) (s : S) (hs₁ : s ∈ W₁) :
    Spec (W₁.toScheme.presheaf.stalk (⟨s, hs₁⟩ : W₁.toScheme)) ⟶ Spec (S.presheaf.stalk s) :=
  Spec.map (W₁.ι.stalkMap (⟨s, hs₁⟩ : W₁.toScheme))

private lemma stalkMapSpec_comp_fromSpecStalk {S : Scheme.{u}} (W₁ : S.Opens) (s : S)
    (hs₁ : s ∈ W₁) :
    stalkMapSpec W₁ s hs₁ ≫ S.fromSpecStalk s =
      W₁.toScheme.fromSpecStalk ⟨s, hs₁⟩ ≫ W₁.ι :=
  Scheme.SpecMap_stalkMap_fromSpecStalk W₁.ι (x := ⟨s, hs₁⟩)

/-- The canonical comparison morphism from the preimage of `W₁.ι ⁻¹ᵁ U` in `Spec 𝒪_{W₁, s}` to
the preimage of `U` in `Spec 𝒪_{S, s}`. -/
def stalkOpenRestriction {S : Scheme.{u}} (U W₁ : S.Opens) (s : S) (hs₁ : s ∈ W₁) :
    (W₁.toScheme.fromSpecStalk (⟨s, hs₁⟩ : W₁.toScheme) ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).toScheme ⟶
      (S.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  let σ := stalkMapSpec W₁ s hs₁
  have hpre : W₁.toScheme.fromSpecStalk s₁ ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U) = σ ⁻¹ᵁ (S.fromSpecStalk s ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, stalkMapSpec_comp_fromSpecStalk]
  ((Spec _).isoOfEq hpre).hom ≫ (σ ∣_ (S.fromSpecStalk s ⁻¹ᵁ U))

/-- `stalkOpenRestriction` commutes with restriction of `fromSpecStalk` to `U`. -/
@[reassoc]
theorem stalkOpenRestriction_comp_morphismRestrict {S : Scheme.{u}} (U W₁ : S.Opens) (s : S)
    (hs₁ : s ∈ W₁) :
    stalkOpenRestriction U W₁ s hs₁ ≫ (S.fromSpecStalk s ∣_ U) =
      (W₁.toScheme.fromSpecStalk (⟨s, hs₁⟩ : W₁.toScheme) ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ∣_ U) := by
  rw [← cancel_mono U.ι]
  dsimp only [stalkOpenRestriction]
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
    Scheme.isoOfEq_hom_ι_assoc]
  exact congrArg
    ((W₁.toScheme.fromSpecStalk ⟨s, hs₁⟩ ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).ι ≫ ·)
    (stalkMapSpec_comp_fromSpecStalk W₁ s hs₁)

/-- `stalkOpenRestriction` commutes with `fromSpecStalkOfMem` into `W₁`. -/
@[reassoc]
theorem stalkOpenRestriction_comp_ι_fromSpecStalkOfMem {S : Scheme.{u}} (U W₁ : S.Opens) (s : S)
    (hs₁ : s ∈ W₁) :
    stalkOpenRestriction U W₁ s hs₁ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫
        W₁.fromSpecStalkOfMem s hs₁ =
      (W₁.toScheme.fromSpecStalk (⟨s, hs₁⟩ : W₁.toScheme) ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ⁻¹ᵁ U).ι := by
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  have hσ : stalkMapSpec W₁ s hs₁ ≫ W₁.fromSpecStalkOfMem s hs₁ =
      W₁.toScheme.fromSpecStalk s₁ := by
    rw [← cancel_mono W₁.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact stalkMapSpec_comp_fromSpecStalk W₁ s hs₁
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

/-- The preimage of a quasi-compact open under a scheme morphism is quasi-compact. -/
theorem quasiCompact_ι_preimage {W S : Scheme.{u}} (j : W ⟶ S) (U : S.Opens)
    [QuasiCompact U.ι] : QuasiCompact (j ⁻¹ᵁ U).ι :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_morphismRestrict j U)
    inferInstance

/-- Pushing an affine open neighbourhood `V ⊆ W₁` of `⟨s, hs₁⟩` forward to `S` gives an affine
open neighbourhood `W := W₁.ι ''ᵁ V ≤ W₁` of `s` together with the `fromSpecStalkOfMem`
compatibilities into `U ⊔ W` and `W₁`. -/
theorem affineImage_fromSpecStalkOfMem {S : Scheme.{u}} (U W₁ : S.Opens) {s : S}
    (hs₁ : s ∈ W₁) {V : W₁.toScheme.Opens} (hV : IsAffineOpen V)
    (hsV : (⟨s, hs₁⟩ : W₁.toScheme) ∈ V) :
    IsAffineOpen (W₁.ι ''ᵁ V) ∧ W₁.ι ''ᵁ V ≤ W₁ ∧ ∃ hsW : s ∈ W₁.ι ''ᵁ V,
      (W₁.ι ''ᵁ V).fromSpecStalkOfMem s hsW ≫ S.homOfLE (le_sup_right : _ ≤ U ⊔ _) =
        (U ⊔ (W₁.ι ''ᵁ V)).fromSpecStalkOfMem s (Opens.mem_sup.mpr (Or.inr hsW)) ∧
      (W₁.ι ''ᵁ V).fromSpecStalkOfMem s hsW ≫ S.homOfLE (W₁.ι_image_le V) =
        W₁.fromSpecStalkOfMem s hs₁ := by
  have hsW : s ∈ W₁.ι ''ᵁ V := ⟨⟨s, hs₁⟩, hsV, rfl⟩
  exact ⟨hV.image_of_isOpenImmersion W₁.ι, W₁.ι_image_le V, hsW,
    Scheme.Opens.fromSpecStalkOfMem_homOfLE _ _ s hsW,
    Scheme.Opens.fromSpecStalkOfMem_homOfLE _ _ s hsW⟩

private lemma pullback_stalkOpenRestriction_eq {S : Scheme.{u}} (U W₁ : S.Opens) (s : S)
    (hs₁ : s ∈ W₁) {Y₁ Y₂ : Over S}
    (eU : (Over.pullback U.ι).obj Y₁ ≅ (Over.pullback U.ι).obj Y₂)
    (es : (Over.pullback (S.fromSpecStalk s)).obj Y₁ ≅
      (Over.pullback (S.fromSpecStalk s)).obj Y₂)
    (eW₁ : (Over.pullback W₁.ι).obj Y₁ ≅ (Over.pullback W₁.ι).obj Y₂)
    (heW₁_hom : Over.conjPullback (W₁.fromSpecStalkOfMem_ι s hs₁) eW₁.hom = es.hom)
    (he_conj : Over.conjPullback (morphismRestrict_ι (S.fromSpecStalk s) U) eU.hom =
      Over.conjPullback (rfl : (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ S.fromSpecStalk s = _) es.hom) :
    (Over.pullback (W₁.toScheme.fromSpecStalk ⟨s, hs₁⟩ ∣_ (W₁.ι ⁻¹ᵁ U))).map
        (Over.conjPullback (rfl : (W₁.ι ⁻¹ᵁ U).ι ≫ W₁.ι = _) eW₁.hom) =
      (Over.pullback (W₁.toScheme.fromSpecStalk ⟨s, hs₁⟩ ∣_ (W₁.ι ⁻¹ᵁ U))).map
        (Over.conjPullback (morphismRestrict_ι W₁.ι U) eU.hom) := by
  let U₁ : W₁.toScheme.Opens := W₁.ι ⁻¹ᵁ U
  let p₁ : Spec (W₁.toScheme.presheaf.stalk ⟨s, hs₁⟩) ⟶ W₁.toScheme :=
    W₁.toScheme.fromSpecStalk ⟨s, hs₁⟩
  have hτU := stalkOpenRestriction_comp_morphismRestrict U W₁ s hs₁
  have hτW₁ := stalkOpenRestriction_comp_ι_fromSpecStalkOfMem U W₁ s hs₁
  have hτS := stalkOpenRestriction_comp_ι_fromSpecStalk U W₁ s hs₁
  refine Over.conjPullback_injective (rfl : (p₁ ∣_ U₁) ≫ (U₁.ι ≫ W₁.ι) = _) ?_
  have hw_a : (p₁ ∣_ U₁ ≫ U₁.ι) ≫ W₁.ι = p₁ ∣_ U₁ ≫ U₁.ι ≫ W₁.ι := Category.assoc ..
  have hw_b : (p₁ ∣_ U₁ ≫ W₁.ι ∣_ U) ≫ U.ι = p₁ ∣_ U₁ ≫ U₁.ι ≫ W₁.ι := by
    rw [Category.assoc, morphismRestrict_ι]
  have hw_s : ((S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ W₁.fromSpecStalkOfMem s hs₁) ≫ W₁.ι =
      (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ S.fromSpecStalk s := by simp
  calc Over.conjPullback rfl (Over.conjPullback (rfl : U₁.ι ≫ W₁.ι = _) eW₁.hom)
      = Over.conjPullback hw_a eW₁.hom :=
        Over.conjPullback_conjPullback rfl rfl rfl hw_a eW₁.hom
    _ = Over.conjPullback hτS (Over.conjPullback hw_s eW₁.hom) :=
        (Over.conjPullback_conjPullback hτW₁ hw_s hτS hw_a eW₁.hom).symm
    _ = Over.conjPullback hτS (Over.conjPullback rfl es.hom) := by
        rw [← Over.conjPullback_conjPullback rfl (W₁.fromSpecStalkOfMem_ι s hs₁) rfl hw_s eW₁.hom,
          heW₁_hom]
    _ = Over.conjPullback hτS
          (Over.conjPullback (morphismRestrict_ι (S.fromSpecStalk s) U) eU.hom) := by
        rw [he_conj]
    _ = Over.conjPullback hw_b eU.hom :=
        Over.conjPullback_conjPullback hτU (morphismRestrict_ι (S.fromSpecStalk s) U) hτS hw_b
          eU.hom
    _ = Over.conjPullback rfl (Over.conjPullback (morphismRestrict_ι W₁.ι U) eU.hom) :=
        (Over.conjPullback_conjPullback rfl (morphismRestrict_ι W₁.ι U) rfl hw_b eU.hom).symm

private lemma conjPullback_infImage_compat {S : Scheme.{u}} (U W₁ : S.Opens)
    (V : W₁.toScheme.Opens) (hWW₁ : W₁.ι ''ᵁ V ≤ W₁) {Y₁ Y₂ : Over S}
    (eU : (Over.pullback U.ι).obj Y₁ ≅ (Over.pullback U.ι).obj Y₂)
    (eW₁ : (Over.pullback W₁.ι).obj Y₁ ≅ (Over.pullback W₁.ι).obj Y₂)
    (hab_V : (Over.pullback (V.ι ∣_ (W₁.ι ⁻¹ᵁ U))).map
        (Over.conjPullback (rfl : (W₁.ι ⁻¹ᵁ U).ι ≫ W₁.ι = _) eW₁.hom) =
      (Over.pullback (V.ι ∣_ (W₁.ι ⁻¹ᵁ U))).map
        (Over.conjPullback (morphismRestrict_ι W₁.ι U) eU.hom)) :
    Over.conjPullback (S.homOfLE_ι (inf_le_left : U ⊓ (W₁.ι ''ᵁ V) ≤ U)) eU.hom =
      Over.conjPullback (S.homOfLE_ι (inf_le_right : U ⊓ (W₁.ι ''ᵁ V) ≤ W₁.ι ''ᵁ V))
        (Over.conjPullback (S.homOfLE_ι hWW₁) eW₁.hom) := by
  let U₁ : W₁.toScheme.Opens := W₁.ι ⁻¹ᵁ U
  let W : S.Opens := W₁.ι ''ᵁ V
  let isoInf := infImageOpenIso U W₁ V
  have hisoInf_U := infImageOpenIso_hom_comp_left U W₁ V
  have hisoInf_W := infImageOpenIso_hom_comp_right U W₁ V
  have hw_V : isoInf.hom ≫ (V.ι ∣_ U₁) ≫ U₁.ι ≫ W₁.ι = (U ⊓ W).ι := by
    calc isoInf.hom ≫ (V.ι ∣_ U₁) ≫ U₁.ι ≫ W₁.ι
        = (isoInf.hom ≫ (V.ι ∣_ U₁) ≫ U₁.ι) ≫ W₁.ι := by simp only [Category.assoc]
      _ = (S.homOfLE (inf_le_right : U ⊓ W ≤ W) ≫ S.homOfLE hWW₁) ≫ W₁.ι := by rw [hisoInf_W]
      _ = (U ⊓ W).ι := by simp only [Category.assoc, Scheme.homOfLE_ι]
  have hw_aV : (V.ι ∣_ U₁ ≫ U₁.ι) ≫ W₁.ι = V.ι ∣_ U₁ ≫ U₁.ι ≫ W₁.ι := Category.assoc ..
  have hw_bV : (V.ι ∣_ U₁ ≫ W₁.ι ∣_ U) ≫ U.ι = V.ι ∣_ U₁ ≫ U₁.ι ≫ W₁.ι := by
    rw [Category.assoc, morphismRestrict_ι]
  have hw_W₁ : (S.homOfLE (inf_le_right : U ⊓ W ≤ W) ≫ S.homOfLE hWW₁) ≫ W₁.ι = (U ⊓ W).ι := by
    rw [Category.assoc, S.homOfLE_ι, S.homOfLE_ι]
  have hV_conj : Over.conjPullback (rfl : (V.ι ∣_ U₁) ≫ (U₁.ι ≫ W₁.ι) = _)
        (Over.conjPullback (rfl : U₁.ι ≫ W₁.ι = _) eW₁.hom) =
      Over.conjPullback (rfl : (V.ι ∣_ U₁) ≫ (U₁.ι ≫ W₁.ι) = _)
        (Over.conjPullback (morphismRestrict_ι W₁.ι U) eU.hom) := by
    rw [Over.conjPullback_eq (w := (rfl : (V.ι ∣_ U₁) ≫ (U₁.ι ≫ W₁.ι) = _)),
      Over.conjPullback_eq (w := (rfl : (V.ι ∣_ U₁) ≫ (U₁.ι ≫ W₁.ι) = _)), hab_V]
  calc Over.conjPullback (S.homOfLE_ι inf_le_left) eU.hom
      = Over.conjPullback hw_V (Over.conjPullback hw_bV eU.hom) :=
        (Over.conjPullback_conjPullback hisoInf_U hw_bV hw_V (S.homOfLE_ι inf_le_left)
          eU.hom).symm
    _ = Over.conjPullback hw_V
          (Over.conjPullback rfl (Over.conjPullback (morphismRestrict_ι W₁.ι U) eU.hom)) := by
        rw [Over.conjPullback_conjPullback rfl (morphismRestrict_ι W₁.ι U) rfl hw_bV eU.hom]
    _ = Over.conjPullback hw_V
          (Over.conjPullback rfl (Over.conjPullback (rfl : U₁.ι ≫ W₁.ι = _) eW₁.hom)) := by
        rw [hV_conj]
    _ = Over.conjPullback hw_V (Over.conjPullback hw_aV eW₁.hom) := by
        rw [Over.conjPullback_conjPullback rfl rfl rfl hw_aV eW₁.hom]
    _ = Over.conjPullback hw_W₁ eW₁.hom :=
        Over.conjPullback_conjPullback hisoInf_W hw_aV hw_V hw_W₁ eW₁.hom
    _ = Over.conjPullback (S.homOfLE_ι inf_le_right)
          (Over.conjPullback (S.homOfLE_ι hWW₁) eW₁.hom) :=
        (Over.conjPullback_conjPullback rfl (S.homOfLE_ι hWW₁) (S.homOfLE_ι inf_le_right) hw_W₁
          eW₁.hom).symm

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
        (Over.pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).hom.app Y₂ =
      (Over.pullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)).hom.app Y₁ ≫
        (Over.pullback (S.fromSpecStalk s ⁻¹ᵁ U).ι).map es.hom) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (hs : s ∈ W)
      (eUW : (Over.pullback (U ⊔ W).ι).obj Y₁ ≅ (Over.pullback (U ⊔ W).ι).obj Y₂),
      (Over.pullbackCompIso (S.homOfLE_ι (le_sup_left : U ≤ U ⊔ W))).inv.app Y₁ ≫
          (Over.pullback (S.homOfLE le_sup_left)).map eUW.hom ≫
          (Over.pullbackCompIso (S.homOfLE_ι (le_sup_left : U ≤ U ⊔ W))).hom.app Y₂ =
        eU.hom ∧
      (Over.pullbackCompIso
          ((U ⊔ W).fromSpecStalkOfMem_ι s (Opens.mem_sup.mpr (Or.inr hs)))).inv.app Y₁ ≫
          (Over.pullback ((U ⊔ W).fromSpecStalkOfMem s (Opens.mem_sup.mpr (Or.inr hs)))).map
            eUW.hom ≫
          (Over.pullbackCompIso
            ((U ⊔ W).fromSpecStalkOfMem_ι s (Opens.mem_sup.mpr (Or.inr hs)))).hom.app Y₂ =
        es.hom := by
  -- Spread `es` to an affine open neighbourhood `W₁` of `s`.
  obtain ⟨W₁, _, hs₁, eW₁, heW₁⟩ := exists_pullback_iso_fromSpecStalk (X := Y₁) (Y := Y₂) s es
  have heW₁_hom : Over.conjPullback (W₁.fromSpecStalkOfMem_ι s hs₁) eW₁.hom = es.hom := by
    simpa [Over.conjPullback_eq] using congrArg Iso.hom heW₁
  have he_conj : Over.conjPullback (morphismRestrict_ι (S.fromSpecStalk s) U) eU.hom =
      Over.conjPullback (rfl : (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ S.fromSpecStalk s = _) es.hom :=
    (Over.pullbackSquareIso_iff_conjPullback (morphismRestrict_ι (S.fromSpecStalk s) U) rfl _
      eU.hom es.hom).mp he
  -- Compare `eW₁` and `eU` on `U₁ := W₁.ι ⁻¹ᵁ U`, pushed forward to `Over W₁`.
  let U₁ : W₁.toScheme.Opens := W₁.ι ⁻¹ᵁ U
  have hqcU₁ : QuasiCompact U₁.ι := quasiCompact_ι_preimage W₁.ι U
  let a := Over.conjPullback (rfl : U₁.ι ≫ W₁.ι = _) eW₁.hom
  let b := Over.conjPullback (morphismRestrict_ι W₁.ι U) eU.hom
  let X₁ : Over W₁.toScheme := (Over.map U₁.ι).obj ((Over.pullback (U₁.ι ≫ W₁.ι)).obj Y₁)
  let Z₁ : Over W₁.toScheme := (Over.map U₁.ι).obj ((Over.pullback (U₁.ι ≫ W₁.ι)).obj Y₂)
  have : QuasiCompact X₁.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₁.hom (U₁.ι ≫ W₁.ι) ≫ U₁.ι))
  have : LocallyOfFiniteType Z₁.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₂.hom (U₁.ι ≫ W₁.ι) ≫ U₁.ι))
  -- Show `a` and `b` agree over `Spec 𝒪_{W₁, s}`.
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  let p₁ : Spec (W₁.toScheme.presheaf.stalk s₁) ⟶ W₁.toScheme := W₁.toScheme.fromSpecStalk s₁
  have hab_p₁ : (Over.pullback (p₁ ∣_ U₁)).map a = (Over.pullback (p₁ ∣_ U₁)).map b :=
    pullback_stalkOpenRestriction_eq U W₁ s hs₁ eU es eW₁ heW₁_hom he_conj
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
  obtain ⟨hW, hWW₁, hsW, hstalk_sup, hstalk_W₁⟩ :=
    affineImage_fromSpecStalkOfMem U W₁ hs₁ hV hsV
  let eW : (Over.pullback W.ι).obj Y₁ ≅ (Over.pullback W.ι).obj Y₂ :=
    ((Over.pullbackCompIso (S.homOfLE_ι hWW₁)).app Y₁).symm ≪≫
      (Over.pullback (S.homOfLE hWW₁)).mapIso eW₁ ≪≫
      (Over.pullbackCompIso (S.homOfLE_ι hWW₁)).app Y₂
  have heW_hom : eW.hom = Over.conjPullback (S.homOfLE_ι hWW₁) eW₁.hom := by
    simp [eW, Over.conjPullback_eq]
  let e₁ : (Over.pullback (S.homOfLE (le_sup_left : U ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₁) ≅
      (Over.pullback (S.homOfLE (le_sup_left : U ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₂) :=
    (Over.pullbackCompIso (S.homOfLE_ι le_sup_left)).app Y₁ ≪≫
      eU ≪≫ ((Over.pullbackCompIso (S.homOfLE_ι le_sup_left)).app Y₂).symm
  let e₂ : (Over.pullback (S.homOfLE (le_sup_right : W ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₁) ≅
      (Over.pullback (S.homOfLE (le_sup_right : W ≤ U ⊔ W))).obj
        ((Over.pullback (U ⊔ W).ι).obj Y₂) :=
    (Over.pullbackCompIso (S.homOfLE_ι le_sup_right)).app Y₁ ≪≫
      eW ≪≫ ((Over.pullbackCompIso (S.homOfLE_ι le_sup_right)).app Y₂).symm
  have hpb := isPullback_opens_inf_le (X := S) (le_sup_left : U ≤ U ⊔ W) (le_sup_right : W ≤ U ⊔ W)
  have hcov := S.opensRange_homOfLE_sup U W
  -- Verify compatibility of `e₁` and `e₂` over `U ⊓ W` from `hab_V`.
  have he_compat : (Over.pullback (S.homOfLE (inf_le_left : U ⊓ W ≤ U))).map e₁.hom ≫
        (Over.pullbackSquareIso hpb.w).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₂) =
      (Over.pullbackSquareIso hpb.w).hom.app ((Over.pullback (U ⊔ W).ι).obj Y₁) ≫
        (Over.pullback (S.homOfLE (inf_le_right : U ⊓ W ≤ W))).map e₂.hom := by
    have hU : U ≤ U ⊔ W := le_sup_left
    have hWle : W ≤ U ⊔ W := le_sup_right
    have hLU : U ⊓ W ≤ U := inf_le_left
    have hRW : U ⊓ W ≤ W := inf_le_right
    rw [Over.pullbackSquareIso_iff_conjPullback (S.homOfLE_homOfLE hLU hU)
      (S.homOfLE_homOfLE hRW hWle) hpb.w]
    have hL := Over.conjPullback_conjIso (S.homOfLE_homOfLE hLU hU) (S.homOfLE_ι hU)
      (S.homOfLE_ι hLU) (S.homOfLE_ι (hLU.trans hU)) eU.hom
    have hR := Over.conjPullback_conjIso (S.homOfLE_homOfLE hRW hWle) (S.homOfLE_ι hWle)
      (S.homOfLE_ι hRW) (S.homOfLE_ι (hLU.trans hU)) eW.hom
    rw [← cancel_epi ((Over.pullbackCompIso (S.homOfLE_ι (hLU.trans hU))).inv.app Y₁),
      ← cancel_mono ((Over.pullbackCompIso (S.homOfLE_ι (hLU.trans hU))).hom.app Y₂)]
    refine (Category.assoc ..).trans
      (hL.trans (Eq.trans ?_ (hR.symm.trans (Category.assoc ..).symm)))
    rw [heW_hom]
    exact conjPullback_infImage_compat U W₁ V hWW₁ eU eW₁ hab_V
  -- Glue `e₁` and `e₂` to an isomorphism over `U ⊔ W`.
  let eUW : (Over.pullback (U ⊔ W).ι).obj Y₁ ≅ (Over.pullback (U ⊔ W).ι).obj Y₂ :=
    glueOverIso hpb hcov e₁ e₂ he_compat
  refine ⟨W, hW, hsW, eUW, ?_, ?_⟩
  · have hL : (Over.pullback (S.homOfLE (le_sup_left : U ≤ U ⊔ W))).map eUW.hom = e₁.hom :=
      congrArg Iso.hom (pullback_mapIso_glueOverIso_left hpb hcov e₁ e₂ he_compat)
    rw [hL]; simp [e₁]
  · have hR : Over.conjPullback (S.homOfLE_ι (le_sup_right : W ≤ U ⊔ W)) eUW.hom = eW.hom := by
      have h : (Over.pullback (S.homOfLE (le_sup_right : W ≤ U ⊔ W))).map eUW.hom = e₂.hom :=
        congrArg Iso.hom (pullback_mapIso_glueOverIso_right hpb hcov e₁ e₂ he_compat)
      rw [Over.conjPullback_eq, h]; simp [e₂]
    rw [← Over.conjPullback_eq]
    calc Over.conjPullback
          ((U ⊔ W).fromSpecStalkOfMem_ι s (Opens.mem_sup.mpr (Or.inr hsW))) eUW.hom
        = Over.conjPullback (W.fromSpecStalkOfMem_ι s hsW)
            (Over.conjPullback (S.homOfLE_ι le_sup_right) eUW.hom) :=
          (Over.conjPullback_conjPullback hstalk_sup (S.homOfLE_ι le_sup_right)
            (W.fromSpecStalkOfMem_ι s hsW) _ eUW.hom).symm
      _ = Over.conjPullback (W.fromSpecStalkOfMem_ι s hsW)
            (Over.conjPullback (S.homOfLE_ι hWW₁) eW₁.hom) := by
          rw [hR, heW_hom]
      _ = Over.conjPullback (W₁.fromSpecStalkOfMem_ι s hs₁) eW₁.hom :=
          Over.conjPullback_conjPullback hstalk_W₁ (S.homOfLE_ι hWW₁)
            (W.fromSpecStalkOfMem_ι s hsW) (W₁.fromSpecStalkOfMem_ι s hs₁) eW₁.hom
      _ = es.hom := heW₁_hom

end LocalSpreading

end TauCeti.AlgebraicGeometry
