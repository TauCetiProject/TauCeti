/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Restrict
public import TauCeti.Geometry.RingedSpace.OpenImmersion

/-!
# Open immersions of pre-adic spaces

A morphism `f : X ⟶ Y` of pre-adic spaces is an *open immersion* when its underlying morphism of
presheafed spaces of complete separated topological rings is one: its continuous map is an open
embedding and, over every open of the image, the comparison map of structure presheaves is an
isomorphism. Since `f` is a morphism of `𝒱^pre`, its stalk maps are then isomorphisms compatible
with the stalk valuations, so `f` identifies `X` with the restriction of `Y` to the open image
`f(X)` as an object of `𝒱^pre` (`isoRestrict`): open immersions are the morphisms inducing an
isomorphism onto an open subspace.

The canonical morphism from a restriction is an open immersion, open immersions compose, and
isomorphisms are open immersions. An open immersion `f : X ⟶ Z` has the universal property of
the open subspace it defines: every morphism `g : Y ⟶ Z` whose image lies in the image of `f`
factors uniquely through `f` (`lift`), so two open immersions with the same image have
isomorphic sources (`isoOfRangeEq`). The lifts are those of the underlying presheafed spaces,
promoted to `𝒱^pre` by `TauCeti.PreAdicSpace.Hom.ofFac`.

Pullbacks of open immersions exist in `𝒱^pre`. The pullback of an open immersion `f : X ⟶ Z`
along any `g : Y ⟶ Z` is the restriction of `Y` to the open preimage `g⁻¹(f(X))`
(`pullbackConeOfLeft`): a cone over `cospan f g` factors through it by the universal property of
the open immersion `Y.restrict _ ⟶ Y`, whose image is that preimage. So open immersions are stable
under base change, and the forgetful functor to presheafed spaces preserves these pullbacks, the
image of `pullbackConeOfLeft` being Mathlib's pullback cone of presheafed spaces
(`PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft`). These are the pullbacks required by
`CategoryTheory.GlueData`, whose gluing maps are open immersions with pullbacks along one another,
and the preservation statement is what carries a family of glue data in `𝒱^pre` to glue data of
presheafed spaces (`CategoryTheory.GlueData.mapGlueData`).

## Main definitions

* `TauCeti.PreAdicSpace.IsOpenImmersion`: open immersions of pre-adic spaces.
* `TauCeti.PreAdicSpace.IsOpenImmersion.lift`: the factorisation of a morphism with image inside
  the image of an open immersion.
* `TauCeti.PreAdicSpace.IsOpenImmersion.isoOfRangeEq`: two open immersions with the same image
  have isomorphic sources.
* `TauCeti.PreAdicSpace.IsOpenImmersion.isoRestrict`: an open immersion identifies its source
  with the restriction of its target to its image.
* `TauCeti.PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft`: the pullback of an open immersion
  along a morphism, with `pullbackConeOfLeftIsLimit` proving that it is a pullback.
* `TauCeti.PreAdicSpace.Hom.restrictPreimage`: a morphism restricted over an open of its target.
* `TauCeti.PreAdicSpace.restrictRestrictIso`: restricting a restriction is restricting to the
  image.

## Main results

* `TauCeti.PreAdicSpace.IsOpenImmersion.hasPullback_of_left`: pullbacks of open immersions exist.
* `TauCeti.PreAdicSpace.IsOpenImmersion.pullback_snd_of_left`: open immersions are stable under
  base change.
* `TauCeti.PreAdicSpace.IsOpenImmersion.range_pullback_snd_of_left`: the base change of an open
  immersion `f` along `g` has image `g⁻¹(f(X))`.
* `TauCeti.PreAdicSpace.IsOpenImmersion.forgetToPresheafedSpace_preservesPullback_of_left`: the
  forgetful functor to presheafed spaces preserves pullbacks of open immersions.
* `TauCeti.PreAdicSpace.Hom.prop_restrictPreimage_iff_of_isOpenImmersion`: a morphism that
  becomes the restriction of `f` over `V` after composing with open immersions onto `V` and onto
  `f⁻¹(V)` has the same isomorphism-invariant properties as that restriction.
* `TauCeti.PreAdicSpace.Hom.prop_restrictPreimage_restrictPreimage_iff`: restricting over an open
  and then over an open of it is restricting over the image of the second open.

The design follows `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`, including its
construction of pullbacks along open immersions.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.2.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

universe u

namespace PreAdicSpace

variable {X Y Z : PreAdicSpace.{u}}

/-- A morphism of pre-adic spaces is an open immersion when its underlying morphism of presheafed
spaces of complete separated topological rings is an open immersion: an open embedding of the
underlying spaces along which the structure presheaf of the target restricts to that of the
source. -/
abbrev IsOpenImmersion (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) f.toHom

/-- The underlying continuous map of an open immersion is an open embedding. -/
theorem Hom.isOpenEmbedding (f : X ⟶ Y) [H : IsOpenImmersion f] : IsOpenEmbedding f.base :=
  H.base_open

namespace IsOpenImmersion

/-- The canonical morphism from a restriction is an open immersion. -/
instance ofRestrict {U : TopCat.{u}} (X : PreAdicSpace.{u}) {f : U ⟶ X.toTopCat}
    (h : IsOpenEmbedding f) : IsOpenImmersion (X.ofRestrict h) :=
  inferInstanceAs (PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h))

/-- The composite of two open immersions is an open immersion. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) :=
  inferInstanceAs (PresheafedSpace.IsOpenImmersion
    (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace))

/-- An isomorphism of pre-adic spaces is an open immersion. -/
instance (priority := 100) of_isIso (f : X ⟶ Y) [IsIso f] : IsOpenImmersion f :=
  inferInstanceAs (PresheafedSpace.IsOpenImmersion
    (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) f.toHom)

/-- An open immersion is a monomorphism, as its underlying morphism of presheafed spaces is. -/
instance mono (f : X ⟶ Y) [IsOpenImmersion f] : Mono f :=
  forgetToPresheafedSpace.mono_of_mono_map (PresheafedSpace.IsOpenImmersion.mono f.toHom)

/-- Forgetting the topology on sections, the underlying morphism of presheafed spaces of rings of
an open immersion is an open immersion. -/
instance toRingPresheafedSpaceHom_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] :
    PresheafedSpace.IsOpenImmersion (toRingPresheafedSpaceHom f.toHom) :=
  PresheafedSpace.IsOpenImmersion.mapPresheaf_map _ f.toHom

/-- The stalk maps of an open immersion are isomorphisms. -/
instance isIso_stalkMap (f : X ⟶ Y) [IsOpenImmersion f] (x : X) : IsIso (f.stalkMap x) :=
  Hom.stalkMap_def f x ▸
    PresheafedSpace.IsOpenImmersion.stalk_iso (toRingPresheafedSpaceHom f.toHom) x

section Lift

variable (f : X ⟶ Z) [IsOpenImmersion f] (g : Y ⟶ Z)

/-- For an open immersion `f : X ⟶ Z` and a morphism `g : Y ⟶ Z` whose image is contained in the
image of `f`, the morphism `Y ⟶ X` through which `g` factors. It is the lift of the underlying
morphisms of presheafed spaces, and is unique (`lift_uniq`). -/
noncomputable def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  Hom.ofFac g f (PresheafedSpace.IsOpenImmersion.lift f.toHom g.toHom H)
    (PresheafedSpace.IsOpenImmersion.lift_fac f.toHom g.toHom H)

@[simp]
theorem lift_toHom (H : Set.range g.base ⊆ Set.range f.base) :
    (lift f g H).toHom = PresheafedSpace.IsOpenImmersion.lift f.toHom g.toHom H :=
  Hom.ofFac_toHom _ _ _ _

@[reassoc (attr := simp)]
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g := by
  apply Hom.ext'
  rw [comp_toHom, lift_toHom]
  exact PresheafedSpace.IsOpenImmersion.lift_fac f.toHom g.toHom H

theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by
  rw [← cancel_mono f, hl, lift_fac]

end Lift

section IsoOfRangeEq

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
  (e : Set.range f.base = Set.range g.base)

/-- Two open immersions into `Z` with the same image have isomorphic sources. The isomorphism is
the unique morphism compatible with the two immersions (`isoOfRangeEq_hom_comp`). -/
noncomputable def isoOfRangeEq : X ≅ Y where
  hom := lift g f e.le
  inv := lift f g e.ge
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]
theorem isoOfRangeEq_hom_comp : (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac g f e.le

@[reassoc (attr := simp)]
theorem isoOfRangeEq_inv_comp : (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac f g e.ge

end IsoOfRangeEq

section IsoRestrict

variable (f : X ⟶ Y) [IsOpenImmersion f]

/-- An open immersion `f : X ⟶ Y` identifies `X` with the restriction of `Y` to the open image
of `f`: open immersions are the morphisms of `𝒱^pre` inducing an isomorphism onto an open
subspace. -/
noncomputable def isoRestrict : X ≅ Y.restrict f.isOpenEmbedding :=
  isoOfRangeEq f (Y.ofRestrict f.isOpenEmbedding) rfl

@[reassoc (attr := simp)]
theorem isoRestrict_hom_ofRestrict :
    (isoRestrict f).hom ≫ Y.ofRestrict f.isOpenEmbedding = f :=
  isoOfRangeEq_hom_comp _ _ _

@[reassoc (attr := simp)]
theorem isoRestrict_inv_comp : (isoRestrict f).inv ≫ f = Y.ofRestrict f.isOpenEmbedding :=
  isoOfRangeEq_inv_comp _ _ _

end IsoRestrict

section Pullback

open Limits

variable (f : X ⟶ Z) [H : IsOpenImmersion f] (g : Y ⟶ Z)

-- The cone is exposed, as `ofRestrict` is: its point must unfold to the restriction of `Y`, so
-- that its second leg is the canonical morphism `Y.ofRestrict _` (`pullbackConeOfLeft_snd`).
@[expose] public section PullbackConeOfLeftDef

/-- The pullback cone of an open immersion `f : X ⟶ Z` along a morphism `g : Y ⟶ Z`: its point is
the restriction of `Y` to the open preimage `g⁻¹(f(X))`, its second leg is the canonical open
immersion of that restriction into `Y`, and its first leg is the factorisation through `f` of the
restriction of `g`. -/
noncomputable def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk
    (lift f (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base) ≫ g)
      (by
        rintro _ ⟨p, rfl⟩
        exact ⟨pullback.fst f.base g.base p, CategoryTheory.congr_fun pullback.condition p⟩))
    (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base))
    (lift_fac _ _ _)

end PullbackConeOfLeftDef

/-- The second leg of `pullbackConeOfLeft` is the canonical open immersion of the restriction of
`Y` to `g⁻¹(f(X))`. -/
@[simp]
theorem pullbackConeOfLeft_snd :
    (pullbackConeOfLeft f g).snd =
      Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base) :=
  rfl

/-- The second leg of `pullbackConeOfLeft` is an open immersion. -/
instance : IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  pullbackConeOfLeft_snd f g ▸ ofRestrict Y _

/-- `pullbackConeOfLeft` is a limit cone: a cone over `cospan f g` factors uniquely through the
open immersion `(pullbackConeOfLeft f g).snd`, whose image is `g⁻¹(f(X))`. -/
noncomputable def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s =>
    have hs : Set.range s.snd.base ⊆ Set.range (pullbackConeOfLeft f g).snd.base := by
      rintro _ ⟨z, rfl⟩
      exact (TopCat.pullback_snd_range f.base g.base).ge
        ⟨s.fst.base z, congrArg (fun φ : s.pt ⟶ Z => φ.base z) s.condition⟩
    ⟨lift _ s.snd hs,
      by rw [← cancel_mono f, Category.assoc, PullbackCone.condition, lift_fac_assoc,
        s.condition],
      lift_fac _ _ _, fun {m} _ hm => lift_uniq _ _ _ m hm⟩

/-- The first leg of `pullbackConeOfLeft` is the factorisation through `f` of the restriction of
`g` to `g⁻¹(f(X))`. -/
@[simp]
theorem pullbackConeOfLeft_fst :
    (pullbackConeOfLeft f g).fst =
      lift f (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base) ≫ g)
        (by
          rintro _ ⟨p, rfl⟩
          exact ⟨pullback.fst f.base g.base p, CategoryTheory.congr_fun pullback.condition p⟩) :=
  rfl

/-- The first leg of `pullbackConeOfLeft` is the first leg of Mathlib's pullback cone of presheafed
spaces, both factoring the restriction of `g` through the monomorphism `f`. -/
theorem pullbackConeOfLeft_fst_toHom :
    (pullbackConeOfLeft f g).fst.toHom =
      PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.toHom g.toHom :=
  -- The ascription below types `(pullbackConeOfLeft f g).fst.toHom` with source Mathlib's
  -- `Y.toPresheafedSpace.restrict _`, the source of `pullbackConeOfLeftFst`: the cone point
  -- `Y.restrict _` has this underlying presheafed space by definition
  -- (`PreAdicSpace.restrict_toPresheafedSpace`, proved by `rfl`).
  have h : ((pullbackConeOfLeft f g).fst.toHom ≫ f.toHom :
      (pullbackConeOfLeft f g).pt.toPresheafedSpace ⟶ Z.toPresheafedSpace) =
        PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.toHom g.toHom ≫ f.toHom :=
    (congrArg Hom.toHom (pullbackConeOfLeft f g).condition).trans
      (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition f.toHom g.toHom).symm
  (cancel_mono _).1 h

/-- Pre-adic spaces have pullbacks of open immersions. -/
instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩

/-- Pre-adic spaces have pullbacks of open immersions. -/
instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g

/-- Open immersions of pre-adic spaces are stable under base change. -/
instance pullback_snd_of_left : IsOpenImmersion (pullback.snd f g) := by
  rw [← (IsPullback.of_isLimit (pullbackConeOfLeftIsLimit f g)).isoPullback_inv_snd]
  infer_instance

/-- Open immersions of pre-adic spaces are stable under base change. -/
instance pullback_fst_of_right : IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

/-- The image of the base change of an open immersion `f` along `g` is the preimage under `g` of
the image of `f`. -/
theorem range_pullback_snd_of_left :
    Set.range (pullback.snd f g).base = g.base ⁻¹' Set.range f.base := by
  rw [← (IsPullback.of_isLimit (pullbackConeOfLeftIsLimit f g)).isoPullback_inv_snd, comp_base,
    TopCat.coe_comp, Function.Surjective.range_comp ?_, pullbackConeOfLeft_snd, ofRestrict_base]
  · exact TopCat.pullback_snd_range f.base g.base
  · exact (TopCat.homeoOfIso (forgetToTop.mapIso _).symm).surjective

/-- The image of the base change of an open immersion `f` along `g` is the preimage under `g` of
the image of `f`. -/
theorem range_pullback_fst_of_right :
    Set.range (pullback.fst g f).base = g.base ⁻¹' Set.range f.base := by
  rw [← pullbackSymmetry_hom_comp_snd, comp_base, TopCat.coe_comp,
    Function.Surjective.range_comp ?_, range_pullback_snd_of_left]
  exact (TopCat.homeoOfIso (forgetToTop.mapIso (pullbackSymmetry g f))).surjective

/-- The image in `Z` of the pullback of an open immersion `f` along `g` is the intersection of the
images of `f` and `g`. -/
theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst f g ≫ f).base = Set.range f.base ∩ Set.range g.base := by
  rw [pullback.condition, comp_base, TopCat.coe_comp, Set.range_comp, range_pullback_snd_of_left,
    Set.image_preimage_eq_inter_range]

/-- The map from the pullback of two open immersions to their common target is an open
immersion. -/
instance pullback_to_base_isOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance

/-- The forgetful functor to presheafed spaces preserves pullbacks of open immersions: the image
of `pullbackConeOfLeft` is Mathlib's pullback cone of presheafed spaces. -/
instance forgetToPresheafedSpace_preservesPullback_of_left :
    PreservesLimit (cospan f g) forgetToPresheafedSpace :=
  -- The point of the image cone is `(Y.restrict _).toPresheafedSpace`, which is by definition
  -- Mathlib's `Y.toPresheafedSpace.restrict _` (`PreAdicSpace.restrict_toPresheafedSpace`, proved
  -- by `rfl`), so the points are identified by `Iso.refl`. The legs of the image cone are
  -- `forgetToPresheafedSpace.map` of the legs of `pullbackConeOfLeft`, which are by definition
  -- their underlying morphisms `Hom.toHom`; the first is `pullbackConeOfLeftFst` by
  -- `pullbackConeOfLeft_fst_toHom` and the second is `Y.toPresheafedSpace.ofRestrict _` by
  -- `PreAdicSpace.ofRestrict_toHom`.
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) <|
    (isLimitMapConePullbackConeEquiv _ _).symm.toFun
      ((PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.toHom g.toHom).ofIsoLimit
        (PullbackCone.ext (s := PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft f.toHom g.toHom)
          (Iso.refl _) ((pullbackConeOfLeft_fst_toHom f g).symm.trans
            (Category.id_comp (forgetToPresheafedSpace.map (pullbackConeOfLeft f g).fst)).symm)
          (Category.id_comp (forgetToPresheafedSpace.map (pullbackConeOfLeft f g).snd)).symm))

/-- The forgetful functor to presheafed spaces preserves pullbacks of open immersions. -/
instance forgetToPresheafedSpace_preservesPullback_of_right :
    PreservesLimit (cospan g f) forgetToPresheafedSpace :=
  preservesPullback_symmetry _ _ _

end Pullback

end IsOpenImmersion

section Restrict

variable {U : TopCat.{u}} (X : PreAdicSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)

-- Both bases are the inclusion of a subtype followed by `f`, so a point lies in either range
-- exactly when it is the image of a point of `V`. The identifications of the two bases with
-- `f ∘ Subtype.val` are the `rfl`-lemmas `comp_base` and `ofRestrict_base`, which cannot be
-- rewritten inside `Set.range`: the source of the right-hand side of `ofRestrict_base` is the open
-- `(Opens.toTopCat _).obj V`, while the source of the left-hand side is the carrier of a
-- restriction, which unfolds to it only at default transparency, so the rewritten composite is
-- ill-typed for `rw`. The two sets are compared pointwise instead.
private theorem range_ofRestrict_comp_ofRestrict_base (V : Opens (X.restrict h)) :
    Set.range ((X.restrict h).ofRestrict V.isOpenEmbedding ≫ X.ofRestrict h).base =
      Set.range (X.ofRestrict (h.isOpenMap.functor.obj V).isOpenEmbedding).base := by
  ext y
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    exact ⟨⟨f v, v, hv, rfl⟩, rfl⟩
  · rintro ⟨⟨_, v, hv, rfl⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- Restricting a restriction is restricting to the image: `X` restricted to `U` and then to an
open `V` of `U` is isomorphic in `𝒱^pre` to `X` restricted to the image of `V` in `X`, both being
open subspaces of `X` with the same image. The isomorphism is compatible with the canonical
morphisms to `X` (`restrictRestrictIso_hom_ofRestrict`). -/
noncomputable def restrictRestrictIso (V : Opens (X.restrict h)) :
    (X.restrict h).restrict V.isOpenEmbedding ≅
      X.restrict (h.isOpenMap.functor.obj V).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq ((X.restrict h).ofRestrict V.isOpenEmbedding ≫ X.ofRestrict h)
    (X.ofRestrict (h.isOpenMap.functor.obj V).isOpenEmbedding)
    (range_ofRestrict_comp_ofRestrict_base X h V)

@[reassoc (attr := simp)]
theorem restrictRestrictIso_hom_ofRestrict (V : Opens (X.restrict h)) :
    (restrictRestrictIso X h V).hom ≫ X.ofRestrict (h.isOpenMap.functor.obj V).isOpenEmbedding =
      (X.restrict h).ofRestrict V.isOpenEmbedding ≫ X.ofRestrict h :=
  IsOpenImmersion.isoOfRangeEq_hom_comp _ _ _

/-- The inverse nested-restriction isomorphism commutes with the canonical morphisms to `X`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_inv_ofRestrict (V : Opens (X.restrict h)) :
    (restrictRestrictIso X h V).inv ≫ (X.restrict h).ofRestrict V.isOpenEmbedding ≫
      X.ofRestrict h = X.ofRestrict (h.isOpenMap.functor.obj V).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq_inv_comp _ _ _

end Restrict

namespace Hom

variable (f : X ⟶ Y) (V : Opens Y)

/-- Restrict a morphism over an open of its target: `f⁻¹(V) → V`, with the restricted pre-adic
structures. It is the unique morphism commuting with the inclusions into `X` and `Y`. -/
noncomputable def restrictPreimage :
    X.restrict ((Opens.map f.base).obj V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  IsOpenImmersion.lift (Y.ofRestrict V.isOpenEmbedding)
    (X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding ≫ f)
    (by rintro _ ⟨x, rfl⟩; exact ⟨⟨f.base x.1, Opens.mem_map.mp x.2⟩, rfl⟩)

/-- The restriction of a morphism commutes with the inclusions of the open subspaces. -/
@[reassoc (attr := simp)]
theorem restrictPreimage_ofRestrict :
    f.restrictPreimage V ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding ≫ f := by
  unfold restrictPreimage
  exact IsOpenImmersion.lift_fac _ _ _

/-- Any morphism between the restricted spaces that commutes with their inclusions is the
restriction of the original morphism. -/
theorem restrictPreimage_uniq
    (g : X.restrict ((Opens.map f.base).obj V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding)
    (hg : g ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding ≫ f) :
    g = f.restrictPreimage V := by
  unfold restrictPreimage
  exact IsOpenImmersion.lift_uniq _ _ _ g hg

/-- On points, the restricted morphism is the original map with codomain restricted to `V`. -/
@[simp]
theorem restrictPreimage_base_apply
    (x : X.restrict ((Opens.map f.base).obj V).isOpenEmbedding) :
    (f.restrictPreimage V).base x = ⟨f.base x.1, Opens.mem_map.mp x.2⟩ := by
  apply Subtype.ext
  exact congrArg (fun g ↦ g.base x) (f.restrictPreimage_ofRestrict V)


/-- **Restrictions of a morphism can be recognized through open immersions.** Let `f : X ⟶ Y` be
a morphism of pre-adic spaces and `V` an open of `Y`. If open immersions `v : Y' ⟶ Y` and
`u : X' ⟶ X` have images `V` and `f⁻¹(V)`, and `f' : X' ⟶ Y'` satisfies `f' ≫ v = u ≫ f`, then
`f'` is the restriction `f⁻¹(V) → V` of `f` up to the isomorphisms of `X'` and `Y'` with the open
subspaces. So every isomorphism-invariant property holds for one exactly when it holds for the
other. -/
theorem prop_restrictPreimage_iff_of_isOpenImmersion (P : MorphismProperty PreAdicSpace.{u})
    [P.RespectsIso] {X' Y' : PreAdicSpace.{u}} (f' : X' ⟶ Y') (u : X' ⟶ X) (v : Y' ⟶ Y)
    [IsOpenImmersion u] [IsOpenImmersion v] (hv : Set.range v.base = V)
    (hu : Set.range u.base = f.base ⁻¹' V) (w : f' ≫ v = u ≫ f) :
    P (f.restrictPreimage V) ↔ P f' := by
  -- the images are compared pointwise, as the bases of `ofRestrict` are inclusions of opens only
  -- up to unfolding the restricted spaces
  have hV : Set.range v.base = Set.range (Y.ofRestrict V.isOpenEmbedding).base := by
    rw [hv]
    ext y
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩
  have hU : Set.range u.base =
      Set.range (X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding).base := by
    rw [hu]
    ext x
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩
  let eY := IsOpenImmersion.isoOfRangeEq v (Y.ofRestrict V.isOpenEmbedding) hV
  let eX := IsOpenImmersion.isoOfRangeEq u
    (X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding) hU
  -- `f'` is the restriction of `f`, up to the two identifications
  have hsq : f' ≫ eY.hom = eX.hom ≫ f.restrictPreimage V := by
    rw [← cancel_mono (Y.ofRestrict V.isOpenEmbedding), Category.assoc, Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_comp, restrictPreimage_ofRestrict,
      IsOpenImmersion.isoOfRangeEq_hom_comp_assoc, w]
  rw [← MorphismProperty.cancel_left_of_respectsIso P eX.hom, ← hsq,
    MorphismProperty.cancel_right_of_respectsIso P f' eY.hom]

/-- **Restricting twice is restricting once**: for a morphism `f : X ⟶ Y`, an open `W` of `Y` and
an open `O` of the restriction of `Y` to `W`, an isomorphism-invariant property holds for `f`
restricted over `W` and then over `O` exactly when it holds for `f` restricted over the image of
`O` in `Y`. -/
theorem prop_restrictPreimage_restrictPreimage_iff (P : MorphismProperty PreAdicSpace.{u})
    [P.RespectsIso] (W : Opens Y) (O : Opens (Y.restrict W.isOpenEmbedding)) :
    P ((f.restrictPreimage W).restrictPreimage O) ↔
      P (f.restrictPreimage (W.isOpenEmbedding.isOpenMap.functor.obj O)) := by
  refine (prop_restrictPreimage_iff_of_isOpenImmersion f _ P _
    ((X.restrict ((Opens.map f.base).obj W).isOpenEmbedding).ofRestrict
        ((Opens.map (f.restrictPreimage W).base).obj O).isOpenEmbedding ≫
      X.ofRestrict ((Opens.map f.base).obj W).isOpenEmbedding)
    ((Y.restrict W.isOpenEmbedding).ofRestrict O.isOpenEmbedding ≫ Y.ofRestrict W.isOpenEmbedding)
    ?_ ?_ ?_).symm
  · ext y
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      refine ⟨(f.restrictPreimage W).base z, hz, ?_⟩
      rw [restrictPreimage_base_apply]
      rfl
    · rintro ⟨z, hz, hzx⟩
      have hxW : f.base x ∈ W := hzx ▸ z.2
      let x' : X.restrict ((Opens.map f.base).obj W).isOpenEmbedding := ⟨x, Opens.mem_map.mpr hxW⟩
      have heq : (f.restrictPreimage W).base x' = z :=
        (f.restrictPreimage_base_apply W x').trans (Subtype.ext hzx.symm)
      exact ⟨⟨x', Opens.mem_map.mpr (heq.symm ▸ hz)⟩, rfl⟩
  · simp

end Hom

end PreAdicSpace

end TauCeti

end
