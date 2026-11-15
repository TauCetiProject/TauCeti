/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Category
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Fibre products of algebraic spaces

Fibre products and binary products of algebraic spaces are algebraic spaces (Stacks,
Lemma 65.7.3 (02X2)). Consequently the full subcategory `AlgSpace` has pullbacks, binary products,
and all finite limits, created and preserved by the forgetful functor `AlgSpace.toPresheaf` to
presheaves on schemes, and preserved by the fully faithful embedding `AlgSpace.ofScheme` of
schemes.

For étale atlases `a : h_U ⟶ F` and `b : h_V ⟶ G` over an algebraic space `H`, the representable
diagonal of `H` represents the presheaf fibre product `h_U ×_H h_V` by a scheme `W`, and the
induced morphism `h_W ⟶ F ×_H G` is an étale atlas (`EtaleAtlas.lift_isPullback`).

## Main definitions

* `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.pullbackObj`,
  `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.pullbackFst`,
  `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.pullbackSnd`, and
  `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.pullbackLift`: named fibre product of algebraic
  spaces, its two projections, and its universal lift.
* `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.ofSchemePullbackIso`: comparison isomorphism
  `ofScheme.obj (pullback f g) ≅ pullbackObj (ofScheme.map f) (ofScheme.map g)` compatible with
  both projections.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.RepresentableDiagonal.of_mono`,
  `TauCeti.AlgebraicGeometry.Spaces.RepresentableDiagonal.prod`, and
  `TauCeti.AlgebraicGeometry.Spaces.RepresentableDiagonal.pullback`: representability of the
  diagonal passes to subpresheaves, binary products, and pullbacks.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.lift_isPullback` and
  `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.prod`: chart products of étale atlases over a
  pullback or binary product of presheaves are étale atlases.
* `TauCeti.AlgebraicGeometry.Spaces.isAlgebraicSpace_pullback` and
  `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.prod`: pullbacks and binary products of
  algebraic spaces are algebraic spaces (Stacks, Lemma 65.7.3 (02X2)).
* `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.ofScheme_relativelyRepresentable`: every morphism from
  an embedded scheme to an algebraic space is representable by schemes on underlying presheaves.
* `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.ofScheme_preservesPullback`: `AlgSpace.ofScheme`
  preserves pullbacks (and all limits).

## References

* [Stacks Project, Lemma 65.7.1](https://stacks.math.columbia.edu/tag/02X0)
* [Stacks Project, Lemma 65.7.3](https://stacks.math.columbia.edu/tag/02X2)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe w w' u

namespace RepresentableDiagonal

/-- Representability of the diagonal passes along monomorphisms of presheaves. -/
theorem of_mono {F G : SchemePresheaf.{u}} (hG : RepresentableDiagonal G) (ι : F ⟶ G) [Mono ι] :
    RepresentableDiagonal F :=
  representableDiagonal_iff_diag.2
    (Functor.relativelyRepresentable.diag_of_mono ι (representableDiagonal_iff_diag.1 hG))

/-- Representability of the diagonal is stable under binary products of presheaves. -/
theorem prod {F G : SchemePresheaf.{u}} (hF : RepresentableDiagonal F)
    (hG : RepresentableDiagonal G) : RepresentableDiagonal (F ⨯ G) :=
  representableDiagonal_iff_diag.2
    (Functor.relativelyRepresentable.diag_prod
      (representableDiagonal_iff_diag.1 hF) (representableDiagonal_iff_diag.1 hG))

/-- Representability of the diagonal is stable under pullbacks of presheaves. -/
theorem pullback {F G H : SchemePresheaf.{u}} (hF : RepresentableDiagonal F)
    (hG : RepresentableDiagonal G) (f : F ⟶ H) (g : G ⟶ H) :
    RepresentableDiagonal (Limits.pullback f g) :=
  representableDiagonal_iff_diag.2
    (Functor.relativelyRepresentable.diag_pullback f g
      (representableDiagonal_iff_diag.1 hF) (representableDiagonal_iff_diag.1 hG))

end RepresentableDiagonal

namespace EtaleAtlas

/-- Base change of an étale atlas along any morphism of presheaves is an étale atlas. -/
theorem of_isPullback {F G : SchemePresheaf.{u}} {U V : Scheme.{u}}
    {a' : yoneda.obj V ⟶ G} {g : yoneda.obj V ⟶ yoneda.obj U}
    {a : yoneda.obj U ⟶ F} {f : G ⟶ F}
    (ha : EtaleAtlas a) (sq : IsPullback g a' a f) : EtaleAtlas a' := by
  have : (MorphismProperty.presheaf @Etale.{u}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) (P := @Etale.{u})
  have : (MorphismProperty.presheaf @Surjective.{u}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) (P := @Surjective.{u})
  exact ⟨MorphismProperty.of_isPullback sq ha.etale,
    MorphismProperty.of_isPullback sq ha.surjective⟩

/-- Postcomposing an étale atlas `a : h_U ⟶ F` with a presheaf morphism `p : F ⟶ G` that is
representable by étale surjective morphisms of schemes gives an étale atlas. -/
theorem comp_of_presheaf {F G : SchemePresheaf.{u}} {U : Scheme.{u}}
    {a : yoneda.obj U ⟶ F} {p : F ⟶ G} (ha : EtaleAtlas a)
    (hp_et : MorphismProperty.presheaf @Etale p)
    (hp_surj : MorphismProperty.presheaf @Surjective p) :
    EtaleAtlas (a ≫ p) := by
  have : MorphismProperty.IsStableUnderComposition @Etale.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : (MorphismProperty.presheaf @Etale.{u}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition (F := yoneda) (P := @Etale.{u})
  have : (MorphismProperty.presheaf @Surjective.{u}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition (F := yoneda) (P := @Surjective.{u})
  exact ⟨MorphismProperty.comp_mem _ _ _ ha.etale hp_et,
    MorphismProperty.comp_mem _ _ _ ha.surjective hp_surj⟩

/-- **Chart product of étale atlases** (Stacks, Lemma 65.7.3 (02X2)). Given a pullback square
`P ⟶ F`, `P ⟶ G` over `f : F ⟶ H` and `g : G ⟶ H` of presheaves on schemes, étale atlases
`a : h_U ⟶ F` and `b : h_V ⟶ G`, and a scheme `W` representing the pullback of `a ≫ f` and
`b ≫ g`, the induced morphism `h_W ⟶ P` is an étale atlas. -/
@[stacks 02X2 "atlas of a fibre product"]
theorem lift_isPullback {P F G H : SchemePresheaf.{u}}
    {fst : P ⟶ F} {snd : P ⟶ G} {f : F ⟶ H} {g : G ⟶ H}
    {U V W : Scheme.{u}} {a : yoneda.obj U ⟶ F} {b : yoneda.obj V ⟶ G}
    (ha : EtaleAtlas a) (hb : EtaleAtlas b) (sq : IsPullback fst snd f g)
    {u : W ⟶ U} {v : W ⟶ V}
    (sqW : IsPullback (yoneda.map u) (yoneda.map v) (a ≫ f) (b ≫ g)) :
    EtaleAtlas (sq.lift (yoneda.map u ≫ a) (yoneda.map v ≫ b)
      (by simpa only [Category.assoc] using sqW.w)) := by
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.presheaf @Etale.{u}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) (P := @Etale.{u})
  have : (MorphismProperty.presheaf @Surjective.{u}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) (P := @Surjective.{u})
  have sqM : IsPullback (Limits.pullback.fst a fst) (Limits.pullback.snd a fst ≫ snd) (a ≫ f) g :=
    (IsPullback.of_hasPullback a fst).paste_vert sq
  let k : yoneda.obj W ⟶ Limits.pullback a fst :=
    Limits.pullback.lift (yoneda.map u)
      (sq.lift (yoneda.map u ≫ a) (yoneda.map v ≫ b) (by simpa only [Category.assoc] using sqW.w))
      (by simp)
  have sqk : IsPullback (yoneda.map v) k b (Limits.pullback.snd a fst ≫ snd) :=
    (IsPullback.of_right (by simpa [k] using sqW) (by simp [k]) sqM).flip
  have hk : EtaleAtlas k := hb.of_isPullback sqk
  have hfac :
      sq.lift (yoneda.map u ≫ a) (yoneda.map v ≫ b)
        (by simpa only [Category.assoc] using sqW.w) = k ≫ Limits.pullback.snd a fst :=
    (Limits.pullback.lift_snd _ _ _).symm
  rw [hfac]
  exact hk.comp_of_presheaf (MorphismProperty.pullback_snd a fst ha.etale)
    (MorphismProperty.pullback_snd a fst ha.surjective)

/-- The product `h_{U ⨯ V} ⟶ F ⨯ G` of two étale atlases is an étale atlas. -/
theorem prod {F G : SchemePresheaf.{u}} {U V : Scheme.{u}}
    {a : yoneda.obj U ⟶ F} {b : yoneda.obj V ⟶ G}
    (ha : EtaleAtlas a) (hb : EtaleAtlas b) :
    EtaleAtlas (Limits.prod.lift (yoneda.map Limits.prod.fst ≫ a)
      (yoneda.map Limits.prod.snd ≫ b)) := by
  let Z : Scheme.{u} := Spec (.of (ULift.{u} ℤ))
  have hTZ : IsTerminal (yoneda.obj Z) :=
    specULiftZIsTerminal.isTerminalObj yoneda Z
  have sqFG : IsPullback (Limits.prod.fst : F ⨯ G ⟶ F) Limits.prod.snd
      (hTZ.from F) (hTZ.from G) :=
    IsPullback.mk' (hTZ.hom_ext _ _)
      (fun _ _ _ h₁ h₂ ↦ Limits.prod.hom_ext h₁ h₂)
      fun _ u v _ ↦ ⟨Limits.prod.lift u v, by simp, by simp⟩
  have sqUV : IsPullback (Limits.prod.fst : U ⨯ V ⟶ U) Limits.prod.snd
      (specULiftZIsTerminal.from U) (specULiftZIsTerminal.from V) :=
    IsPullback.mk' (specULiftZIsTerminal.hom_ext _ _)
      (fun _ _ _ h₁ h₂ ↦ Limits.prod.hom_ext h₁ h₂)
      fun _ u v _ ↦ ⟨Limits.prod.lift u v, by simp, by simp⟩
  have sqUV' : IsPullback (yoneda.map (Limits.prod.fst : U ⨯ V ⟶ U))
      (yoneda.map Limits.prod.snd) (a ≫ hTZ.from F) (b ≫ hTZ.from G) := by
    convert sqUV.map yoneda <;> exact hTZ.hom_ext _ _
  have h := ha.lift_isPullback hb sqFG sqUV'
  convert h using 1
  apply Limits.prod.hom_ext <;> simp

end EtaleAtlas

/-- **Fibre products of algebraic spaces are algebraic spaces** (Stacks, Lemma 65.7.3 (02X2)). -/
@[stacks 02X2]
theorem isAlgebraicSpace_pullback {F G H : SchemePresheaf.{u}} (f : F ⟶ H) (g : G ⟶ H)
    (hF : IsAlgebraicSpace F) (hG : IsAlgebraicSpace G) (hH : IsAlgebraicSpace H) :
    IsAlgebraicSpace (pullback f g) where
  isSheaf := ObjectProperty.prop_limit
    (Presheaf.IsSheaf Scheme.fppfTopology : ObjectProperty SchemePresheaf.{u}) (cospan f g) (by
      rintro (_ | _ | _)
      · exact hH.isSheaf
      · exact hF.isSheaf
      · exact hG.isSheaf)
  representableDiagonal :=
    hF.representableDiagonal.pullback hG.representableDiagonal f g
  exists_etaleAtlas := by
    obtain ⟨U, a, ha⟩ := hF.exists_etaleAtlas
    obtain ⟨V, b, hb⟩ := hG.exists_etaleAtlas
    let hr := hH.representableDiagonal.relativelyRepresentable (a ≫ f)
    refine ⟨hr.pullback (b ≫ g), _, ha.lift_isPullback hb
      (IsPullback.of_hasPullback f g) (hr.isPullback' (b ≫ g))⟩

/-- Binary products of algebraic spaces are algebraic spaces. -/
theorem IsAlgebraicSpace.prod {F G : SchemePresheaf.{u}} (hF : IsAlgebraicSpace F)
    (hG : IsAlgebraicSpace G) : IsAlgebraicSpace (F ⨯ G) where
  isSheaf := ObjectProperty.prop_limit
    (Presheaf.IsSheaf Scheme.fppfTopology : ObjectProperty SchemePresheaf.{u}) (pair F G) (by
      rintro ⟨_ | _⟩
      · exact hF.isSheaf
      · exact hG.isSheaf)
  representableDiagonal := RepresentableDiagonal.prod
    hF.representableDiagonal hG.representableDiagonal
  exists_etaleAtlas := by
    obtain ⟨U, a, ha⟩ := hF.exists_etaleAtlas
    obtain ⟨V, b, hb⟩ := hG.exists_etaleAtlas
    exact ⟨U ⨯ V, _, ha.prod hb⟩

/-- Being an algebraic space is closed under isomorphisms of presheaves. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) where
  of_iso e hF := hF.of_iso e

/-- Being an algebraic space is closed under pullbacks of presheaves. -/
instance : ObjectProperty.IsClosedUnderLimitsOfShape
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) WalkingCospan where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let e₁ : limit p.diag ≅ X := (limit.isLimit p.diag).conePointUniqueUpToIso p.isLimit
    let e₂ : limit p.diag ≅
        pullback (p.diag.map WalkingCospan.Hom.inl) (p.diag.map WalkingCospan.Hom.inr) :=
      HasLimit.isoOfNatIso (diagramIsoCospan p.diag)
    exact (isAlgebraicSpace_pullback _ _
      (p.prop_diag_obj .left) (p.prop_diag_obj .right) (p.prop_diag_obj .one)).of_iso
      (e₂.symm ≪≫ e₁)

/-- Being an algebraic space is closed under binary products of presheaves. -/
instance : ObjectProperty.IsClosedUnderBinaryProducts
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let e₁ : limit p.diag ≅ X := (limit.isLimit p.diag).conePointUniqueUpToIso p.isLimit
    let e₂ : limit p.diag ≅ p.diag.obj ⟨.left⟩ ⨯ p.diag.obj ⟨.right⟩ :=
      HasLimit.isoOfNatIso (diagramIsoPair p.diag)
    exact ((p.prop_diag_obj ⟨.left⟩).prod (p.prop_diag_obj ⟨.right⟩)).of_iso (e₂.symm ≪≫ e₁)

namespace AlgSpace

/-- The category of algebraic spaces has all finite limits. -/
noncomputable instance : HasFiniteLimits AlgSpace.{u} :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The inclusion of algebraic spaces into presheaves preserves all finite limits. -/
noncomputable instance : PreservesFiniteLimits toPresheaf.{u} :=
  have : PreservesLimit (Functor.empty.{0} AlgSpace.{u}) toPresheaf.{u} :=
    preservesLimit_of_preserves_limit_cone specZIsTerminal
      ((isLimitMapConeEmptyConeEquiv toPresheaf.{u} _).symm
        (specULiftZIsTerminal.isTerminalObj yoneda _))
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) toPresheaf.{u} :=
    preservesLimitsOfShape_pempty_of_preservesTerminal toPresheaf.{u}
  have : HasPullbacks SchemePresheaf.{u} := inferInstance
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks toPresheaf.{u}

/-- The named fibre product of two morphisms `f : F ⟶ H` and `g : G ⟶ H` in `AlgSpace`, built on
the presheaf pullback `pullback f.hom g.hom`. The object is exposed so that presheaf morphisms out
of or into `(pullbackObj f g).obj` have source or target `pullback f.hom g.hom`. -/
@[expose]
noncomputable def pullbackObj {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) : AlgSpace.{u} :=
  ⟨pullback f.hom g.hom, isAlgebraicSpace_pullback f.hom g.hom F.property G.property H.property⟩

@[simp]
lemma pullbackObj_obj {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    (pullbackObj f g).obj = pullback f.hom g.hom :=
  (rfl)

/-- The first projection `F ×_H G ⟶ F` of the named fibre product in `AlgSpace`. -/
noncomputable def pullbackFst {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    pullbackObj f g ⟶ F :=
  ObjectProperty.homMk (pullback.fst f.hom g.hom)

@[simp]
lemma pullbackFst_hom {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    (pullbackFst f g).hom = pullback.fst f.hom g.hom :=
  (rfl)

/-- The second projection `F ×_H G ⟶ G` of the named fibre product in `AlgSpace`. -/
noncomputable def pullbackSnd {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    pullbackObj f g ⟶ G :=
  ObjectProperty.homMk (pullback.snd f.hom g.hom)

@[simp]
lemma pullbackSnd_hom {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    (pullbackSnd f g).hom = pullback.snd f.hom g.hom :=
  (rfl)

/-- Commutativity of the projections of `AlgSpace.pullbackObj`. -/
@[reassoc]
theorem pullback_condition {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    pullbackFst f g ≫ f = pullbackSnd f g ≫ g := by
  ext1
  exact pullback.condition

/-- Universal lift into `AlgSpace.pullbackObj`. -/
noncomputable def pullbackLift {W F G H : AlgSpace.{u}} {f : F ⟶ H} {g : G ⟶ H}
    (u : W ⟶ F) (v : W ⟶ G) (w : u ≫ f = v ≫ g) : W ⟶ pullbackObj f g :=
  ObjectProperty.homMk (pullback.lift u.hom v.hom (congrArg (fun k ↦ k.hom) w))

@[reassoc (attr := simp)]
lemma pullbackLift_fst {W F G H : AlgSpace.{u}} {f : F ⟶ H} {g : G ⟶ H}
    (u : W ⟶ F) (v : W ⟶ G) (w : u ≫ f = v ≫ g) :
    pullbackLift u v w ≫ pullbackFst f g = u := by
  ext1
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackLift_snd {W F G H : AlgSpace.{u}} {f : F ⟶ H} {g : G ⟶ H}
    (u : W ⟶ F) (v : W ⟶ G) (w : u ≫ f = v ≫ g) :
    pullbackLift u v w ≫ pullbackSnd f g = v := by
  ext1
  exact pullback.lift_snd _ _ _

/-- Morphisms into `AlgSpace.pullbackObj` are determined by their two projections. -/
lemma pullback_hom_ext {W F G H : AlgSpace.{u}} {f : F ⟶ H} {g : G ⟶ H}
    {u v : W ⟶ pullbackObj f g}
    (h₁ : u ≫ pullbackFst f g = v ≫ pullbackFst f g)
    (h₂ : u ≫ pullbackSnd f g = v ≫ pullbackSnd f g) : u = v := by
  ext1
  exact pullback.hom_ext
    (congrArg (fun k ↦ k.hom) h₁)
    (congrArg (fun k ↦ k.hom) h₂)

/-- `AlgSpace.pullbackObj` with its projections `pullbackFst` and `pullbackSnd` is a pullback
square in `AlgSpace`. -/
theorem isPullback {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    IsPullback (pullbackFst f g) (pullbackSnd f g) f g :=
  IsPullback.mk' (pullback_condition f g)
    (fun _ _ _ ↦ pullback_hom_ext)
    fun _ u v w ↦ ⟨pullbackLift u v w, pullbackLift_fst u v w, pullbackLift_snd u v w⟩

/-- Comparison isomorphism between `AlgSpace.pullbackObj f g` and the categorical pullback
`Limits.pullback f g` in `AlgSpace`. -/
noncomputable def pullbackObjIsoPullback {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    pullbackObj f g ≅ pullback f g :=
  (isPullback f g).isoPullback

@[reassoc (attr := simp)]
lemma pullbackObjIsoPullback_hom_fst {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    (pullbackObjIsoPullback f g).hom ≫ pullback.fst f g = pullbackFst f g :=
  (isPullback f g).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma pullbackObjIsoPullback_hom_snd {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    (pullbackObjIsoPullback f g).hom ≫ pullback.snd f g = pullbackSnd f g :=
  (isPullback f g).isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma pullbackObjIsoPullback_inv_fst {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    (pullbackObjIsoPullback f g).inv ≫ pullbackFst f g = pullback.fst f g :=
  (isPullback f g).isoPullback_inv_fst

@[reassoc (attr := simp)]
lemma pullbackObjIsoPullback_inv_snd {F G H : AlgSpace.{u}} (f : F ⟶ H) (g : G ⟶ H) :
    (pullbackObjIsoPullback f g).inv ≫ pullbackSnd f g = pullback.snd f g :=
  (isPullback f g).isoPullback_inv_snd

/-- Every morphism from an embedded scheme to an algebraic space is representable by schemes on
underlying presheaves (Stacks, Lemma 65.7.1 (02X0)). -/
@[stacks 02X0]
theorem ofScheme_relativelyRepresentable {U : Scheme.{u}} {F : AlgSpace.{u}}
    (f : ofScheme.obj U ⟶ F) : yoneda.relativelyRepresentable f.hom :=
  F.property.representableDiagonal.relativelyRepresentable f.hom

/-- The fully faithful embedding `AlgSpace.ofScheme` preserves limits of any size. -/
noncomputable instance : PreservesLimitsOfSize.{w, w'} ofScheme.{u} :=
  have : PreservesLimitsOfSize.{w, w'} (ofScheme.{u} ⋙ toPresheaf) :=
    preservesLimits_of_natIso ofSchemeCompToPresheafIso.symm
  preservesLimits_of_reflects_of_preserves ofScheme toPresheaf

/-- `AlgSpace.ofScheme` preserves pullbacks of schemes. -/
theorem ofScheme_preservesPullback {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) ofScheme :=
  inferInstance

/-- Comparison isomorphism identifying the embedded fibre product of schemes with
`AlgSpace.pullbackObj` of the embedded morphisms. -/
noncomputable def ofSchemePullbackIso {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    ofScheme.obj (pullback f g) ≅ pullbackObj (ofScheme.map f) (ofScheme.map g) :=
  ((IsPullback.of_hasPullback f g).map ofScheme).isoIsPullback _ _
    (isPullback (ofScheme.map f) (ofScheme.map g))

@[reassoc (attr := simp)]
lemma ofSchemePullbackIso_hom_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (ofSchemePullbackIso f g).hom ≫ pullbackFst (ofScheme.map f) (ofScheme.map g) =
      ofScheme.map (pullback.fst f g) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc (attr := simp)]
lemma ofSchemePullbackIso_hom_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (ofSchemePullbackIso f g).hom ≫ pullbackSnd (ofScheme.map f) (ofScheme.map g) =
      ofScheme.map (pullback.snd f g) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
lemma ofSchemePullbackIso_inv_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (ofSchemePullbackIso f g).inv ≫ ofScheme.map (pullback.fst f g) =
      pullbackFst (ofScheme.map f) (ofScheme.map g) :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

@[reassoc (attr := simp)]
lemma ofSchemePullbackIso_inv_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (ofSchemePullbackIso f g).inv ≫ ofScheme.map (pullback.snd f g) =
      pullbackSnd (ofScheme.map f) (ofScheme.map g) :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

end AlgSpace

end TauCeti.AlgebraicGeometry.Spaces
