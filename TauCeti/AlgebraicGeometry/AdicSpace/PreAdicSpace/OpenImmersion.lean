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

## Main definitions

* `TauCeti.PreAdicSpace.IsOpenImmersion`: open immersions of pre-adic spaces.
* `TauCeti.PreAdicSpace.IsOpenImmersion.lift`: the factorisation of a morphism with image inside
  the image of an open immersion.
* `TauCeti.PreAdicSpace.IsOpenImmersion.isoOfRangeEq`: two open immersions with the same image
  have isomorphic sources.
* `TauCeti.PreAdicSpace.IsOpenImmersion.isoRestrict`: an open immersion identifies its source
  with the restriction of its target to its image.

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

end IsOpenImmersion

end PreAdicSpace

end TauCeti

end
