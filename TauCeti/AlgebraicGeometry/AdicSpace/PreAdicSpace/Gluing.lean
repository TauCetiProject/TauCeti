/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom

/-!
# Descent of morphisms along pre-adic gluing charts

Compatibility with stalk valuations can be checked after precomposition with a jointly
surjective family of morphisms. In particular it can be checked on an open cover. This lets a
morphism of presheafed spaces obtained by gluing chartwise morphisms lift uniquely to a morphism of
pre-adic spaces.

Consequently, a cocone of pre-adic spaces with jointly surjective legs is a colimit whenever its
underlying cocone of presheafed spaces is a colimit. This supplies the universal-property step in
gluing spaces with local stalks and residue-field valuations. The cocone and its pre-adic point
are inputs: this result neither constructs the glued object nor proves that it is an adic space.

The descent argument takes place in the category of pre-adic spaces. For gluing adic spaces,
sheafiness and local affinoidness of the glued object are separate steps from this universal
property.

## Main results

* `TauCeti.PreAdicSpace.Hom.ofCover`: lift a presheafed-space morphism from its chartwise
  lifts, for a jointly surjective family.
* `TauCeti.PreAdicSpace.isColimitOfIsColimitForgetToPresheafedSpace`: lift an underlying
  colimit cocone with jointly surjective legs.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1 and §8.3.
* Mathlib's `AlgebraicGeometry.PresheafedSpace.GlueData` provides the underlying gluing;
  `CategoryTheory.Limits.IsColimit.ofFaithful` lifts its universal property.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.PreAdicSpace

universe u v w

variable {X Y : PreAdicSpace.{u}} {ι : Type v} {U : ι → PreAdicSpace.{u}}

/-- A presheafed-space morphism lifts to a morphism of pre-adic spaces if it lifts after
precomposition with a jointly surjective family. No sheaf condition is needed: the underlying
morphism is already given, and valuation compatibility is checked pointwise on stalks. -/
def Hom.ofCover (j : ∀ i, U i ⟶ X)
    (hcover : ∀ x : X, ∃ (i : ι) (y : U i), (j i).base y = x)
    (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (f : ∀ i, U i ⟶ Y)
    (hfac : ∀ i, (j i).toHom ≫ g = (f i).toHom) : X ⟶ Y where
  toHom := g
  stalkValuation_eq x := by
    obtain ⟨i, y, rfl⟩ := hcover x
    let y' : (U i).toRingPresheafedSpace := y
    have hf := (f i).stalkValuation_eq y'
    -- Rewrite the entire underlying morphism, including the base point in the stalk type.
    -- The composite base point is definitionally `g.base ((j i).base y)`; rewriting only
    -- that point would give an ill-typed motive.
    rw [← hfac i, toRingPresheafedSpaceHom, Functor.map_comp,
      PresheafedSpace.stalkMap.comp] at hf
    rw [(j i).stalkValuation_eq_comap y, Hom.stalkMap_def]
    exact hf.trans (ValuationSpectrum.comap_hom_comap_hom _ _ _).symm

/-- The lift retains the given underlying morphism of presheafed spaces. -/
@[simp]
theorem Hom.ofCover_toHom (j : ∀ i, U i ⟶ X)
    (hcover : ∀ x : X, ∃ (i : ι) (y : U i), (j i).base y = x)
    (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (f : ∀ i, U i ⟶ Y)
    (hfac : ∀ i, (j i).toHom ≫ g = (f i).toHom) :
    (Hom.ofCover j hcover g f hfac).toHom = g := (rfl)

/-- The lifted morphism agrees with the given morphism on each chart. -/
@[reassoc (attr := simp)]
theorem Hom.comp_ofCover (j : ∀ i, U i ⟶ X)
    (hcover : ∀ x : X, ∃ (i : ι) (y : U i), (j i).base y = x)
    (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (f : ∀ i, U i ⟶ Y)
    (hfac : ∀ i, (j i).toHom ≫ g = (f i).toHom) (i : ι) :
    j i ≫ Hom.ofCover j hcover g f hfac = f i := by
  apply Hom.ext'
  simpa using hfac i

/-- **The universal property of gluing lifts to pre-adic spaces.** A cocone whose legs are
jointly surjective is a colimit if its underlying cocone of presheafed spaces is a colimit. In
particular, once the glued object and its chart inclusions have been equipped
with their pre-adic structures, no further valuation condition is needed for the universal
property. The diagram and the target of a descended morphism need not be sheafy. -/
noncomputable def isColimitOfIsColimitForgetToPresheafedSpace
    {J : Type v} [Category.{w} J] {F : J ⥤ PreAdicSpace.{u}} (c : Cocone F)
    (hcover : ∀ x : c.pt, ∃ (i : J) (y : F.obj i), (c.ι.app i).base y = x)
    (hc : IsColimit (forgetToPresheafedSpace.mapCocone c)) : IsColimit c := by
  refine IsColimit.ofFaithful forgetToPresheafedSpace hc
    (fun s ↦ Hom.ofCover c.ι.app hcover (hc.desc (forgetToPresheafedSpace.mapCocone s))
      s.ι.app (fun i ↦ hc.fac _ i)) (fun s ↦ ?_)
  exact Hom.ofCover_toHom c.ι.app hcover (hc.desc (forgetToPresheafedSpace.mapCocone s))
    s.ι.app (fun i ↦ hc.fac _ i)

/-- The descended morphism in the lifted colimit is the underlying presheafed-space descent.
Thus the colimit lift changes neither the continuous map nor the map of structure presheaves. -/
@[simp]
theorem isColimitOfIsColimitForgetToPresheafedSpace_desc_toHom
    {J : Type v} [Category.{w} J] {F : J ⥤ PreAdicSpace.{u}} (c : Cocone F)
    (hcover : ∀ x : c.pt, ∃ (i : J) (y : F.obj i), (c.ι.app i).base y = x)
    (hc : IsColimit (forgetToPresheafedSpace.mapCocone c)) (s : Cocone F) :
    ((isColimitOfIsColimitForgetToPresheafedSpace c hcover hc).desc s).toHom =
      hc.desc (forgetToPresheafedSpace.mapCocone s) := (rfl)

end TauCeti.PreAdicSpace
