/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Category
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Sites.Limits
import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Fibre products of algebraic spaces

Fibre products and binary products of algebraic spaces are algebraic spaces (Stacks,
Lemma 65.7.3 (02X2)). Consequently `IsAlgebraicSpace` is closed under finite limits of presheaves,
so the full subcategory `AlgSpace` has pullbacks, binary products, and all finite limits, created
and preserved by the forgetful functor `AlgSpace.toPresheaf` to presheaves on schemes, and
preserved by the fully faithful embedding `AlgSpace.ofScheme` of schemes.

For étale atlases `a : h_U ⟶ F` and `b : h_V ⟶ G` over an algebraic space `H`, the representable
diagonal of `H` represents the presheaf fibre product `h_U ×_H h_V` by a scheme `W`, and the
induced morphism `h_W ⟶ F ×_H G` is an étale atlas (`EtaleAtlas.lift_isPullback`).

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
  algebraic spaces are algebraic spaces (Stacks, Lemma 65.7.3 (02X2)), giving
  `ObjectProperty.IsClosedUnderFiniteLimits` for `IsAlgebraicSpace`,
  `CreatesFiniteLimits AlgSpace.toPresheaf`, and `PreservesLimitsOfSize AlgSpace.ofScheme`.
* `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.ofScheme_relativelyRepresentable`: every morphism from
  an embedded scheme to an algebraic space is representable by schemes on underlying presheaves
  (Stacks, Lemma 65.7.1 (02X0)).

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
    (MorphismProperty.diag_of_mono ι (representableDiagonal_iff_diag.1 hG))

/-- Representability of the diagonal is stable under binary products of presheaves. -/
theorem prod {F G : SchemePresheaf.{u}} (hF : RepresentableDiagonal F)
    (hG : RepresentableDiagonal G) : RepresentableDiagonal (F ⨯ G) :=
  representableDiagonal_iff_diag.2
    (MorphismProperty.diag_prod
      (representableDiagonal_iff_diag.1 hF) (representableDiagonal_iff_diag.1 hG))

/-- Representability of the diagonal is stable under pullbacks of presheaves. -/
theorem pullback {F G H : SchemePresheaf.{u}} (hF : RepresentableDiagonal F)
    (hG : RepresentableDiagonal G) (f : F ⟶ H) (g : G ⟶ H) :
    RepresentableDiagonal (Limits.pullback f g) :=
  representableDiagonal_iff_diag.2
    (MorphismProperty.diag_pullback f g
      (representableDiagonal_iff_diag.1 hF) (representableDiagonal_iff_diag.1 hG))

end RepresentableDiagonal

namespace EtaleAtlas

/-- Base change of an étale atlas along any morphism of presheaves is an étale atlas. -/
theorem of_isPullback {F G : SchemePresheaf.{u}} {U V : Scheme.{u}}
    {a' : yoneda.obj V ⟶ G} {g : yoneda.obj V ⟶ yoneda.obj U}
    {a : yoneda.obj U ⟶ F} {f : G ⟶ F}
    (ha : EtaleAtlas a) (sq : IsPullback g a' a f) : EtaleAtlas a' :=
  ⟨MorphismProperty.of_isPullback sq ha.etale,
    MorphismProperty.of_isPullback sq ha.surjective⟩

/-- Postcomposing an étale atlas `a : h_U ⟶ F` with a presheaf morphism `p : F ⟶ G` that is
representable by étale surjective morphisms of schemes gives an étale atlas. -/
theorem comp_of_presheaf {F G : SchemePresheaf.{u}} {U : Scheme.{u}}
    {a : yoneda.obj U ⟶ F} {p : F ⟶ G} (ha : EtaleAtlas a)
    (hp_et : MorphismProperty.presheaf @Etale p)
    (hp_surj : MorphismProperty.presheaf @Surjective p) :
    EtaleAtlas (a ≫ p) :=
  ⟨MorphismProperty.comp_mem _ _ _ ha.etale hp_et,
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
    IsPullback.of_is_product' (prodIsProd F G) hTZ
  have sqUV : IsPullback (Limits.prod.fst : U ⨯ V ⟶ U) Limits.prod.snd
      (specULiftZIsTerminal.from U) (specULiftZIsTerminal.from V) :=
    IsPullback.of_is_product' (prodIsProd U V) specULiftZIsTerminal
  have sqUV' : IsPullback (yoneda.map (Limits.prod.fst : U ⨯ V ⟶ U))
      (yoneda.map Limits.prod.snd) (a ≫ hTZ.from F) (b ≫ hTZ.from G) := by
    rw [hTZ.hom_ext (a ≫ hTZ.from F) _, hTZ.hom_ext (b ≫ hTZ.from G) _]
    exact sqUV.map yoneda
  have h := ha.lift_isPullback hb sqFG sqUV'
  have heq : Limits.prod.lift (yoneda.map Limits.prod.fst ≫ a) (yoneda.map Limits.prod.snd ≫ b) =
      sqFG.lift (yoneda.map Limits.prod.fst ≫ a) (yoneda.map Limits.prod.snd ≫ b)
        (by simpa only [Category.assoc] using sqUV'.w) := by
    apply Limits.prod.hom_ext <;> simp
  rwa [heq]

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

/-- Being an algebraic space is closed under isomorphisms of presheaves. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) where
  of_iso e hF := hF.of_iso e

/-- Being an algebraic space is closed under pullbacks of presheaves. -/
instance : ObjectProperty.IsClosedUnderLimitsOfShape
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact (isAlgebraicSpace_pullback _ _ (hF .left) (hF .right) (hF .one)).of_iso
      (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm)

/-- Being an algebraic space is closed under finite limits of presheaves. -/
instance : ObjectProperty.IsClosedUnderFiniteLimits
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) where
  isClosedUnderLimitsOfShape J _ _ :=
    have : HasFiniteLimits AlgSpace.{u} := hasFiniteLimits_of_hasTerminal_and_pullbacks
    have : PreservesLimit (Functor.empty.{0} AlgSpace.{u}) AlgSpace.toPresheaf.{u} :=
      preservesLimit_of_preserves_limit_cone AlgSpace.specZIsTerminal
        ((isLimitMapConeEmptyConeEquiv AlgSpace.toPresheaf.{u} _).symm
          (specULiftZIsTerminal.isTerminalObj yoneda _))
    have : PreservesLimitsOfShape (Discrete PEmpty.{1}) AlgSpace.toPresheaf.{u} :=
      preservesLimitsOfShape_pempty_of_preservesTerminal AlgSpace.toPresheaf.{u}
    have : PreservesFiniteLimits AlgSpace.toPresheaf.{u} :=
      preservesFiniteLimits_of_preservesTerminal_and_pullbacks AlgSpace.toPresheaf.{u}
    ObjectProperty.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _ J

/-- Binary products of algebraic spaces are algebraic spaces. -/
theorem IsAlgebraicSpace.prod {F G : SchemePresheaf.{u}} (hF : IsAlgebraicSpace F)
    (hG : IsAlgebraicSpace G) : IsAlgebraicSpace (F ⨯ G) :=
  ObjectProperty.prop_prod (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) F G hF hG

namespace AlgSpace

/-- The inclusion of algebraic spaces into presheaves creates all finite limits. -/
noncomputable instance : CreatesFiniteLimits toPresheaf.{u} where
  createsFiniteLimits _ _ _ := inferInstance

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

end AlgSpace

end TauCeti.AlgebraicGeometry.Spaces
