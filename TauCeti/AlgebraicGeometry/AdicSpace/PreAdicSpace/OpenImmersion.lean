/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Restrict

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

## Main results

* `TauCeti.PreAdicSpace.IsOpenImmersion.hasPullback_of_left`: pullbacks of open immersions exist.
* `TauCeti.PreAdicSpace.IsOpenImmersion.pullback_snd_of_left`: open immersions are stable under
  base change.
* `TauCeti.PreAdicSpace.IsOpenImmersion.range_pullback_snd_of_left`: the base change of an open
  immersion `f` along `g` has image `g⁻¹(f(X))`.
* `TauCeti.PreAdicSpace.IsOpenImmersion.forgetToPresheafedSpace_preservesPullback_of_left`: the
  forgetful functor to presheafed spaces preserves pullbacks of open immersions.

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
instance toRingPresheafedSpaceHom_isOpenImmersion (f : X ⟶ Y) [H : IsOpenImmersion f] :
    PresheafedSpace.IsOpenImmersion (toRingPresheafedSpaceHom f.toHom) where
  base_open := H.base_open
  c_iso U := by
    -- the component of the whiskered presheaf map is the image of the component of `f.c`, which
    -- is an isomorphism, under the forgetful functor
    have : IsIso (f.toHom.c.app (Opposite.op (H.base_open.functor.obj U))) := H.c_iso U
    exact Functor.map_isIso
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat)
      (f.toHom.c.app (Opposite.op (H.base_open.functor.obj U)))

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

end PreAdicSpace

end TauCeti

end
