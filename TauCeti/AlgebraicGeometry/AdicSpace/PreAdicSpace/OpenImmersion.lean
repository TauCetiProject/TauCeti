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

## Main definitions

* `TauCeti.PreAdicSpace.IsOpenImmersion`: open immersions of pre-adic spaces.
* `TauCeti.PreAdicSpace.IsOpenImmersion.lift`: the factorisation of a morphism with image inside
  the image of an open immersion.
* `TauCeti.PreAdicSpace.IsOpenImmersion.isoOfRangeEq`: two open immersions with the same image
  have isomorphic sources.
* `TauCeti.PreAdicSpace.IsOpenImmersion.isoRestrict`: an open immersion identifies its source
  with the restriction of its target to its image.
* `TauCeti.PreAdicSpace.Hom.restrictPreimage`: a morphism restricted over an open of its target.
* `TauCeti.PreAdicSpace.restrictRestrictIso`: restricting a restriction is restricting to the
  image.

The design follows `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`.

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

end Hom

end PreAdicSpace

end TauCeti

end
