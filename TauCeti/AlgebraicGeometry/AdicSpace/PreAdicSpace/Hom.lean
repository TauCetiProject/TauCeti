/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Basic

/-!
# Morphisms of pre-adic spaces

A morphism of pre-adic spaces is a morphism of the underlying presheafed spaces of complete
separated topological rings which, on the stalk at every point, pulls the stalk valuation of
that point back to the stalk valuation of its image. With these morphisms, pre-adic spaces
form Wedhorn's category `𝒱^pre`.

Wedhorn requires only compatibility of the stalk valuations: locality of the induced stalk
maps follows, because the support of each stalk valuation is the maximal ideal of the stalk.
This is `PreAdicSpace.isLocalHom_stalkMap`, and the corresponding compatibility of the
residue-field valuations is `PreAdicSpace.Hom.valuation_eq_comap`.

## Main definitions

* `TauCeti.PreAdicSpace.Hom`: morphisms of pre-adic spaces, making `PreAdicSpace` a category.
* `TauCeti.PreAdicSpace.Hom.stalkMap`: the ring homomorphism induced on stalks.
* `TauCeti.PreAdicSpace.Hom.residueFieldMap`: the homomorphism induced on residue fields.
* `TauCeti.PreAdicSpace.Hom.ofFac`: a morphism of presheafed spaces factoring a morphism of
  pre-adic spaces through one whose stalk maps over its image are isomorphisms is a morphism of
  pre-adic spaces.
* `TauCeti.PreAdicSpace.forgetToPresheafedSpace`, `TauCeti.PreAdicSpace.forgetToTop`: the
  forgetful functors to presheafed spaces and to topological spaces. The first is faithful and
  reflects isomorphisms: the inverse of an isomorphism of presheafed spaces is automatically
  compatible with the stalk valuations, as the case of `Hom.ofFac` in which it factors the
  identity through the isomorphism.

The design follows `AlgebraicGeometry.LocallyRingedSpace`, with the valuation compatibility in
place of the locality condition.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

universe u

namespace PreAdicSpace

-- The category structure and the forgetful functors are exposed, as for Mathlib's locally
-- ringed spaces: a morphism `X ⟶ Y` of pre-adic spaces must unfold to a `PreAdicSpace.Hom X Y`,
-- and identities and composites are used through their definitional components. The stalk and
-- residue-field maps below are used through their `_def` lemmas, so their bodies stay hidden.
@[expose] public section Category

variable {X Y Z : PreAdicSpace.{u}}

/-- The morphism of presheafed spaces of rings obtained from a morphism of presheafed spaces of
complete separated topological rings by forgetting the topology on sections. -/
noncomputable abbrev toRingPresheafedSpaceHom (f : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) :
    X.toRingPresheafedSpace ⟶ Y.toRingPresheafedSpace :=
  (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).mapPresheaf.map f

/-- A morphism of pre-adic spaces is a morphism of presheafed spaces of complete separated
topological rings whose induced map on the stalk at every point `x` pulls the stalk valuation
at `x` back to the stalk valuation at the image of `x`. -/
structure Hom (X Y : PreAdicSpace.{u}) : Type u
    extends X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  /-- The stalk valuation at the image of `x` is the pullback of the stalk valuation at `x`
  along the induced map on stalks. The point ranges over the presheafed space of rings so that
  both sides have the same type without unfolding `Functor.mapPresheaf`; the form with a point
  of `X` is `PreAdicSpace.Hom.stalkValuation_eq_comap`. -/
  stalkValuation_eq : ∀ x : X.toRingPresheafedSpace,
    Y.stalkValuation ((toRingPresheafedSpaceHom toHom).base x) =
      ValuationSpectrum.comap ((toRingPresheafedSpaceHom toHom).stalkMap x).hom
        (X.stalkValuation x)

/-- Morphisms of pre-adic spaces are determined by their underlying morphisms of presheafed
spaces. -/
@[ext]
theorem Hom.ext {f g : X.Hom Y} (h : f.toHom = g.toHom) : f = g := by
  cases f; cases g; congr

/-- The identity morphism of a pre-adic space. -/
def id (X : PreAdicSpace.{u}) : Hom X X where
  toHom := 𝟙 X.toPresheafedSpace
  stalkValuation_eq x := by
    rw [toRingPresheafedSpaceHom, CategoryTheory.Functor.map_id, PresheafedSpace.stalkMap.id]
    -- The base point `(𝟙 _).base x` is definitionally `x`, and `(𝟙 _).hom` is `RingHom.id`.
    exact (congrFun ValuationSpectrum.comap_id (X.stalkValuation x)).symm

instance (X : PreAdicSpace.{u}) : Inhabited (Hom X X) := ⟨id X⟩

/-- Composition of morphisms of pre-adic spaces. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toHom := (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace)
  stalkValuation_eq x := by
    rw [toRingPresheafedSpaceHom, CategoryTheory.Functor.map_comp, PresheafedSpace.stalkMap.comp]
    -- The base point `(f' ≫ g').base x` is definitionally `g'.base (f'.base x)`.
    exact (g.stalkValuation_eq _).trans
      ((congrArg (ValuationSpectrum.comap _) (f.stalkValuation_eq x)).trans
        (ValuationSpectrum.comap_hom_comap_hom _ _ _))

/-- The category `𝒱^pre` of pre-adic spaces. -/
instance : Category PreAdicSpace.{u} where
  Hom := Hom
  id := id
  comp f g := comp f g
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

-- Register extensionality for categorical morphisms `X ⟶ Y`; `Hom.ext` alone does not let
-- `ext` recognize that these morphisms are `PreAdicSpace.Hom` structures.
@[ext]
theorem Hom.ext' {f g : X ⟶ Y} (h : f.toHom = g.toHom) : f = g := Hom.ext h

@[simp]
theorem id_toHom (X : PreAdicSpace.{u}) : Hom.toHom (𝟙 X) = 𝟙 X.toPresheafedSpace := rfl

@[simp]
theorem comp_toHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toHom = (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace) := rfl

theorem comp_base (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base := rfl

theorem comp_c_app (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ) :
    (f ≫ g).c.app U = g.c.app U ≫ f.c.app (Opposite.op ((Opens.map g.base).obj U.unop)) := rfl

/-- The forgetful functor to presheafed spaces of complete separated topological rings. -/
@[simps]
def forgetToPresheafedSpace :
    PreAdicSpace.{u} ⥤ PresheafedSpace CompleteSeparatedTopCommRingCat.{u} where
  obj X := X.toPresheafedSpace
  map f := f.toHom

instance : forgetToPresheafedSpace.Faithful where
  map_injective h := Hom.ext' h

/-- The forgetful functor to topological spaces. -/
@[simps!]
def forgetToTop : PreAdicSpace.{u} ⥤ TopCat.{u} :=
  forgetToPresheafedSpace ⋙ PresheafedSpace.forget _

end Category

variable {X Y Z : PreAdicSpace.{u}}

section Stalks

/-- The ring homomorphism induced on stalks by a morphism of pre-adic spaces. -/
noncomputable def Hom.stalkMap (f : X ⟶ Y) (x : X) :
    Y.toRingPresheafedSpace.presheaf.stalk (f.base x) ⟶
      X.toRingPresheafedSpace.presheaf.stalk x :=
  (toRingPresheafedSpaceHom f.toHom).stalkMap x

/-- The stalk map is the stalk map of the underlying morphism of presheafed spaces of rings. -/
theorem Hom.stalkMap_def (f : X ⟶ Y) (x : X) :
    f.stalkMap x = (toRingPresheafedSpaceHom f.toHom).stalkMap x := by
  rfl

/-- The stalk valuation at the image of `x` is the pullback of the stalk valuation at `x`. -/
theorem Hom.stalkValuation_eq_comap (f : X ⟶ Y) (x : X) :
    Y.stalkValuation (f.base x) =
      ValuationSpectrum.comap (f.stalkMap x).hom (X.stalkValuation x) :=
  f.stalkValuation_eq x

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The stalk maps of the identity are identities. -/
@[simp]
theorem stalkMap_id (X : PreAdicSpace.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.toRingPresheafedSpace.presheaf.stalk x) := by
  rw [Hom.stalkMap_def, PresheafedSpace.stalkMap.congr_hom
    (toRingPresheafedSpaceHom (𝟙 X : X ⟶ X).toHom) (𝟙 _) (CategoryTheory.Functor.map_id _ _) x,
    PresheafedSpace.stalkMap.id X.toRingPresheafedSpace x]
  -- The `eqToHom` relates two stalks at base points which are definitionally `x`.
  exact (Category.comp_id _).trans (eqToHom_refl _ _)

/-- The stalk maps of a composite are the composites of the stalk maps. -/
theorem stalkMap_comp (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x := by
  rw [Hom.stalkMap_def, Hom.stalkMap_def, Hom.stalkMap_def,
    PresheafedSpace.stalkMap.congr_hom (toRingPresheafedSpaceHom (f ≫ g).toHom)
      (toRingPresheafedSpaceHom f.toHom ≫ toRingPresheafedSpaceHom g.toHom)
      (CategoryTheory.Functor.map_comp _ _ _) x,
    PresheafedSpace.stalkMap.comp (toRingPresheafedSpaceHom f.toHom)
      (toRingPresheafedSpaceHom g.toHom) x]
  -- The `eqToHom` relates two stalks at base points which are definitionally `g.base (f.base x)`.
  exact (congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)

/-- The stalk maps of a morphism of pre-adic spaces are local homomorphisms. This is forced by
compatibility with the stalk valuations, whose supports are the maximal ideals of the stalks. -/
instance isLocalHom_stalkMap (x : X) : IsLocalHom (f.stalkMap x).hom where
  map_nonunit a ha := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← supp_stalkValuation] at ha ⊢
    rwa [f.stalkValuation_eq_comap x, ValuationSpectrum.supp_comap, Ideal.mem_comap]

/-- The homomorphism induced on residue fields by a morphism of pre-adic spaces. -/
noncomputable def Hom.residueFieldMap (x : X) :
    IsLocalRing.ResidueField (Y.toRingPresheafedSpace.presheaf.stalk (f.base x)) →+*
      IsLocalRing.ResidueField (X.toRingPresheafedSpace.presheaf.stalk x) :=
  IsLocalRing.ResidueField.map (f.stalkMap x).hom

/-- The residue-field map is induced by the local stalk map. -/
theorem Hom.residueFieldMap_def (x : X) :
    f.residueFieldMap x = IsLocalRing.ResidueField.map (f.stalkMap x).hom := by
  rfl

/-- The residue square: the residue-field map composed with the residue map at the image of `x`
is the residue map at `x` composed with the stalk map. -/
theorem Hom.residueFieldMap_comp_residue (x : X) :
    (f.residueFieldMap x).comp (IsLocalRing.residue _) =
      (IsLocalRing.residue _).comp (f.stalkMap x).hom :=
  IsLocalRing.ResidueField.map_comp_residue _

/-- The residue-field map sends the residue class of a stalk element to the residue class of
its image under the stalk map. -/
-- Not `@[simp]`: `Functor.mapPresheaf_obj_presheaf` unfolds the stalk in the type of the
-- residue map, so the left-hand side is not in simp normal form; use `rw`.
theorem Hom.residueFieldMap_residue (x : X)
    (a : Y.toRingPresheafedSpace.presheaf.stalk (f.base x)) :
    f.residueFieldMap x (IsLocalRing.residue _ a) = IsLocalRing.residue _ (f.stalkMap x a) :=
  IsLocalRing.ResidueField.map_residue _ a

/-- The residue-field maps of the identity are identities. -/
@[simp]
theorem residueFieldMap_id (X : PreAdicSpace.{u}) (x : X) :
    (𝟙 X : X ⟶ X).residueFieldMap x = RingHom.id _ := by
  simp only [Hom.residueFieldMap_def, stalkMap_id]
  exact IsLocalRing.ResidueField.map_id

/-- The residue-field maps of a composite are the composites of the residue-field maps. -/
@[simp]
theorem residueFieldMap_comp (x : X) :
    (f ≫ g : X ⟶ Z).residueFieldMap x =
      (f.residueFieldMap x).comp (g.residueFieldMap (f.base x)) := by
  simp only [Hom.residueFieldMap_def, stalkMap_comp]
  exact IsLocalRing.ResidueField.map_comp (g.stalkMap (f.base x)).hom (f.stalkMap x).hom

/-- The residue-field valuation at the image of `x` is the pullback of the residue-field
valuation at `x` along the induced map on residue fields. -/
theorem Hom.valuation_eq_comap (x : X) :
    Y.valuation (f.base x) = ValuationSpectrum.comap (f.residueFieldMap x) (X.valuation x) := by
  refine (Y.valuation_eq_of_comap_residue_eq (f.base x) ?_).symm
  rw [← Function.comp_apply (f := ValuationSpectrum.comap _), ← ValuationSpectrum.comap_comp,
    Hom.residueFieldMap_comp_residue, ValuationSpectrum.comap_comp, Function.comp_apply,
    ← X.stalkValuation_def x, f.stalkValuation_eq_comap x]

/-- The stalk maps of a morphism of pre-adic spaces whose underlying morphism of presheafed
spaces is an isomorphism are isomorphisms. -/
instance isIso_stalkMap [IsIso (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) f.toHom]
    (x : X) : IsIso (f.stalkMap x) :=
  -- instance search does not unfold the abbreviation `toRingPresheafedSpaceHom` to a functor
  -- application, so the underlying instance is supplied by hand
  have : IsIso (toRingPresheafedSpaceHom f.toHom) := Functor.map_isIso _ _
  Hom.stalkMap_def f x ▸ PresheafedSpace.stalkMap.isIso (toRingPresheafedSpaceHom f.toHom) x

end Stalks

section OfFac

variable {X Y Z : PreAdicSpace.{u}}

/-- A morphism of presheafed spaces `g` with `g ≫ j = i`, for morphisms `i : X ⟶ Z` and
`j : Y ⟶ Z` of pre-adic spaces such that the stalk maps of `j` at the points of the image of `g`
are isomorphisms, is a morphism of pre-adic spaces: pulling back along those invertible stalk maps
recovers the compatibility of `g` with the stalk valuations from that of `i` and `j`. -/
def Hom.ofFac (i : X ⟶ Z) (j : Y ⟶ Z) (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace)
    [hj : ∀ x : X, IsIso (j.stalkMap (g.base x))] (h : g ≫ j.toHom = i.toHom) : X ⟶ Y where
  toHom := g
  stalkValuation_eq x := by
    obtain ⟨i, hi⟩ := i
    have h' : g ≫ j.toHom = i := h
    subst h'
    have hi' := hi x
    rw [toRingPresheafedSpaceHom, CategoryTheory.Functor.map_comp,
      PresheafedSpace.stalkMap.comp] at hi'
    have hj' := j.stalkValuation_eq ((toRingPresheafedSpaceHom g).base x)
    -- the stalk map of `j` at `g x` is an isomorphism, so pulling back along it is injective; the
    -- point `g x` is a point of the presheafed space of rings, so the instance is instantiated by
    -- hand
    have hiso : IsIso ((toRingPresheafedSpaceHom j.toHom).stalkMap
        ((toRingPresheafedSpaceHom g).base x)) :=
      Hom.stalkMap_def j (g.base x) ▸ hj x
    refine ValuationSpectrum.comap_injective (ConcreteCategory.bijective_of_isIso
      ((toRingPresheafedSpaceHom j.toHom).stalkMap ((toRingPresheafedSpaceHom g).base x))).2 ?_
    -- `hi'` is stated at the point `(g' ≫ j').base x`, which is `j'.base (g'.base x)` by the
    -- `rfl`-lemma `PresheafedSpace.comp_base`. It cannot be rewritten with that lemma: the point
    -- occurs in the types of both sides of `hi'` (the stalk valuations and the stalk map live on
    -- the stalk at that point), so the motive is not type correct. The two forms are identified
    -- definitionally here instead.
    exact hj'.symm.trans (hi'.trans (ValuationSpectrum.comap_hom_comap_hom _ _ _).symm)

@[simp]
theorem Hom.ofFac_toHom (i : X ⟶ Z) (j : Y ⟶ Z) (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace)
    [∀ x : X, IsIso (j.stalkMap (g.base x))] (h : g ≫ j.toHom = i.toHom) :
    (Hom.ofFac i j g h).toHom = g := by
  rfl

end OfFac

section ReflectsIsomorphisms

/-- The underlying morphism of presheafed spaces of an isomorphism of pre-adic spaces is an
isomorphism. Instance search does not see `forgetToPresheafedSpace.map f` as `f.toHom`, so
Mathlib's `Functor.map_isIso` does not supply this. -/
instance isIso_toHom (f : X ⟶ Y) [IsIso f] :
    IsIso (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) f.toHom :=
  (forgetToPresheafedSpace.mapIso (asIso f)).isIso_hom

/-- The forgetful functor to presheafed spaces reflects isomorphisms: the inverse of the
underlying isomorphism of presheafed spaces factors the identity through `f`, whose stalk maps
are isomorphisms, so it is a morphism of pre-adic spaces by `Hom.ofFac`. -/
instance : forgetToPresheafedSpace.{u}.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    obtain ⟨g, hg₁, hg₂⟩ := hf.out
    -- Instance search does not see the objects `forgetToPresheafedSpace.obj X` in the type of
    -- `hf` as the objects `X.toPresheafedSpace` of the morphisms below, so the instance is
    -- restated.
    have : IsIso (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) f.toHom := hf
    exact ⟨⟨Hom.ofFac (𝟙 Y) f g hg₂, Hom.ext' hg₁, Hom.ext' hg₂⟩⟩

/-- A morphism of pre-adic spaces whose underlying morphism of presheafed spaces is an
isomorphism is an isomorphism: the converse of `isIso_toHom`, by reflection of isomorphisms
along the forgetful functor. -/
theorem isIso_of_isIso_toHom (f : X ⟶ Y)
    [hf : IsIso (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) f.toHom] : IsIso f :=
  -- Instance search does not see `forgetToPresheafedSpace.map f` as `f.toHom`, so the instance
  -- is restated.
  have : IsIso (forgetToPresheafedSpace.map f) := hf
  isIso_of_reflects_iso f forgetToPresheafedSpace

end ReflectsIsomorphisms

end PreAdicSpace

end TauCeti

end
