/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import TauCeti.AlgebraicGeometry.FiniteEtale.Exactness
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
public import TauCeti.CategoryTheory.Sites.Point.Representable

/-!
# Finite étale covers as étale sheaves

A finite étale `S`-scheme `X` is in particular étale over `S`, so it is an object of the small
étale site `S.Etale` (`TauCeti.FiniteEtaleScheme.toEtale`), and the presheaf of its sections
`U ↦ Hom_S(U, X)` is an étale sheaf of sets on `S`, because the small étale topology is
subcanonical. This gives a functor (`TauCeti.FiniteEtaleScheme.toSheaf`)

`FiniteEtaleScheme S ⥤ Sheaf (Scheme.smallEtaleTopology S) (Type u)`,

which is fully faithful (`TauCeti.FiniteEtaleScheme.toSheafFullyFaithful`), since both
`toEtale` and the Yoneda embedding of a subcanonical site are.

The stalk of the sheaf of sections of `X` at a geometric point `x : Spec Ω ⟶ S`, for the point
`Scheme.pointSmallEtale x` of the small étale site, is the geometric fibre of `X` at `x`
(`TauCeti.FiniteEtaleScheme.toSheafCompSheafFiberIso`), naturally in `X`. Indeed the stalk of a
representable sheaf at a point of a site is the value of the point's fibre functor, which for
`pointSmallEtale x` is the set of lifts of `x`, and the geometric fibre functor is corepresented
by `x` (`TauCeti.FiniteEtaleScheme.fiberCompInclIso`). Through this isomorphism the action of
the étale fundamental group `Aut (FiniteEtaleScheme.fiber x)` on geometric fibres becomes an
action on the stalks of the corresponding étale sheaves.

The geometric points through separable closures of the residue fields form a conservative family
of points of the small étale site, and stalk functors preserve colimits and finite limits.
Therefore `toSheaf` preserves every colimit, and every finite limit, that all geometric fibre
functors preserve (`TauCeti.FiniteEtaleScheme.preservesColimit_toSheaf`,
`TauCeti.FiniteEtaleScheme.preservesLimit_toSheaf`). In particular it preserves finite limits,
finite coproducts, quotients by finite groups and epimorphisms.

## Main definitions

* `TauCeti.FiniteEtaleScheme.toEtale S`: a finite étale `S`-scheme as an object of the small
  étale site of `S`.
* `TauCeti.FiniteEtaleScheme.toSheaf S`: the étale sheaf of sections of a finite étale
  `S`-scheme.
* `TauCeti.FiniteEtaleScheme.toSheafCompSheafFiberIso x`: the stalk at a geometric point `x` of
  the sheaf of sections is the geometric fibre at `x`.

## Main results

* `TauCeti.FiniteEtaleScheme.toSheafFullyFaithful`: the sheaf-of-sections functor is fully
  faithful.
* `TauCeti.FiniteEtaleScheme.preservesColimit_toSheaf`,
  `TauCeti.FiniteEtaleScheme.preservesLimit_toSheaf`: the sheaf-of-sections functor preserves
  the colimits and finite limits preserved by all geometric fibre functors.
* Instances: `toSheaf S` preserves finite limits, finite coproducts, quotients by finite groups
  and epimorphisms.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2 (points of the étale
  topos) and Exposé IX, §2 (locally constant sheaves and finite étale covers).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable (S : Scheme.{u})

/-- A finite étale `S`-scheme, regarded as an object of the small étale site of `S`. -/
@[expose] noncomputable def toEtale : FiniteEtaleScheme S ⥤ S.Etale :=
  MorphismProperty.Comma.lift (finiteEtaleSchemeProperty S).ι
    (fun X ↦ inferInstanceAs (Etale X.obj.hom))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- Forgetting étaleness of a finite étale `S`-scheme in the small étale site gives its
underlying scheme over `S`. -/
theorem toEtale_comp_forget :
    toEtale S ⋙ Scheme.Etale.forget S = (finiteEtaleSchemeProperty S).ι :=
  (rfl)

/-- The scheme over `S` underlying `toEtale S X` is that of `X`. -/
@[simp]
theorem forget_obj_toEtale_obj (X : FiniteEtaleScheme S) :
    (Scheme.Etale.forget S).obj ((toEtale S).obj X) = X.obj :=
  (rfl)

/-- The morphism over `S` underlying `toEtale S` of a morphism is the original one. -/
@[simp]
theorem forget_map_toEtale_map {X Y : FiniteEtaleScheme S} (f : X ⟶ Y) :
    (Scheme.Etale.forget S).map ((toEtale S).map f) = f.hom :=
  (rfl)

/-- Finite étale `S`-schemes form a full subcategory of the small étale site of `S`. -/
noncomputable def toEtaleFullyFaithful : (toEtale S).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := Scheme.Etale.forget S)
    (ObjectProperty.fullyFaithfulι _)

instance : (toEtale S).Full := (toEtaleFullyFaithful S).full

instance : (toEtale S).Faithful := (toEtaleFullyFaithful S).faithful

/-- The étale sheaf of sections of a finite étale `S`-scheme `X`: its value on a scheme `U`
étale over `S` is the set of morphisms `U ⟶ X` over `S`. -/
@[expose] noncomputable def toSheaf :
    FiniteEtaleScheme S ⥤ Sheaf (Scheme.smallEtaleTopology S) (Type u) :=
  toEtale S ⋙ (Scheme.smallEtaleTopology S).yoneda

/-- The underlying presheaf of the sheaf of sections of `X` is the presheaf represented by `X`
on the small étale site: its value on `U` is the set of morphisms `U ⟶ X` over `S`. -/
@[simp]
theorem toSheaf_obj_obj (X : FiniteEtaleScheme S) :
    ((toSheaf S).obj X).obj = yoneda.obj ((toEtale S).obj X) :=
  (rfl)

/-- On morphisms, the sheaf of sections is the Yoneda embedding of the small étale site. -/
@[simp]
theorem toSheaf_map_hom {X Y : FiniteEtaleScheme S} (f : X ⟶ Y) :
    ((toSheaf S).map f).hom = yoneda.map ((toEtale S).map f) :=
  (rfl)

/-- A finite étale `S`-scheme is determined by its étale sheaf of sections: the
sheaf-of-sections functor is fully faithful. -/
noncomputable def toSheafFullyFaithful : (toSheaf S).FullyFaithful :=
  (toEtaleFullyFaithful S).comp (Scheme.smallEtaleTopology S).yonedaFullyFaithful

instance : (toSheaf S).Full := (toSheafFullyFaithful S).full

instance : (toSheaf S).Faithful := (toSheafFullyFaithful S).faithful

variable {S} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The stalk at a geometric point `x : Spec Ω ⟶ S` of the étale sheaf of sections of a finite
étale `S`-scheme is its geometric fibre at `x`, naturally in the finite étale scheme. -/
noncomputable def toSheafCompSheafFiberIso (x : Spec (.of Ω) ⟶ S) :
    toSheaf S ⋙ (Scheme.pointSmallEtale x).sheafFiber ≅ fiber x ⋙ FintypeCat.incl :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toEtale S) (Scheme.pointSmallEtale x).yonedaCompSheafFiberIso ≪≫
    (fiberCompInclIso x).symm

/-- A point `y` of the geometric fibre of `X` at `x` corresponds to the germ, at the lift of `x`
to `X` attached to `y`, of the tautological section of the sheaf of sections of `X`. -/
theorem toSheafCompSheafFiberIso_inv_app_apply (x : Spec (.of Ω) ⟶ S) (X : FiniteEtaleScheme S)
    (y : (fiber x).obj X) :
    (toSheafCompSheafFiberIso x).inv.app X y =
      (Scheme.pointSmallEtale x).toPresheafFiber ((toEtale S).obj X)
        ((fiberCompInclIso x).hom.app X y) ((toSheaf S).obj X).obj (𝟙 _) := by
  -- The associator has identity components, so the inverse at `X` is that of
  -- `yonedaCompSheafFiberIso` applied after `fiberCompInclIso`.
  exact (Scheme.pointSmallEtale x).yonedaCompSheafFiberIso_inv_app_apply _ _

/-- The sheaf-of-sections functor sends a colimit cocone to a colimit cocone when every geometric
fibre functor does. -/
theorem preservesColimit_toSheaf {J : Type*} [Category J] (K : J ⥤ FiniteEtaleScheme S)
    [HasColimit (K ⋙ toSheaf S)]
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S),
      PreservesColimit K (fiber x ⋙ FintypeCat.incl)) :
    PreservesColimit K (toSheaf S) where
  preserves {c} hc := ⟨((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' S)
    |>.jointlyReflectIsomorphisms (Type u)).jointlyReflectsColimit fun Φ ↦ Classical.choice (by
      obtain ⟨Φ, ⟨s⟩⟩ := Φ
      exact ⟨IsColimit.mapCoconeEquiv (toSheafCompSheafFiberIso _).symm
        (isColimitOfPreserves (fiber _ ⋙ FintypeCat.incl) hc)⟩)⟩

/-- The sheaf-of-sections functor sends a finite limit cone to a limit cone when every geometric
fibre functor does. -/
theorem preservesLimit_toSheaf {J : Type*} [SmallCategory J] [FinCategory J]
    (K : J ⥤ FiniteEtaleScheme S)
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S),
      PreservesLimit K (fiber x ⋙ FintypeCat.incl)) :
    PreservesLimit K (toSheaf S) where
  preserves {c} hc := ⟨((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' S)
    |>.jointlyReflectIsomorphisms (Type u)).jointlyReflectsLimit fun Φ ↦ Classical.choice (by
      obtain ⟨Φ, ⟨s⟩⟩ := Φ
      exact ⟨IsLimit.mapConeEquiv (toSheafCompSheafFiberIso _).symm
        (isLimitOfPreserves (fiber _ ⋙ FintypeCat.incl) hc)⟩)⟩

instance : PreservesFiniteLimits (toSheaf S) where
  preservesFiniteLimits _ _ _ :=
    ⟨fun {K} ↦ preservesLimit_toSheaf K fun _ _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteCoproducts (toSheaf S) where
  preserves n := by
    -- Instance search for colimits of étale sheaves of this shape times out, so the instance
    -- deduced from finite colimits is given explicitly.
    have := hasColimitsOfShape_of_hasFiniteColimits
      (C := Sheaf (Scheme.smallEtaleTopology S) (Type u)) (Discrete (Fin n))
    exact ⟨fun {K} ↦ preservesColimit_toSheaf K fun _ _ _ _ ↦ inferInstance⟩

/-- The sheaf-of-sections functor preserves quotients by finite groups. -/
instance {G : Type u} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (toSheaf S) where
  preservesColimit {K} := by
    -- Sheafification is supplied by the affine étale site; making it a local instance lets
    -- instance search find colimits of étale sheaves of this shape.
    have : HasWeakSheafify (Scheme.smallEtaleTopology S) (Type u) := inferInstance
    exact preservesColimit_toSheaf K fun _ _ _ _ ↦ inferInstance

instance : (toSheaf S).PreservesEpimorphisms where
  preserves f _ := by
    refine (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' S).jointlyReflectEpimorphisms
      (Type u)).epi_iff _).2 fun Φ ↦ ?_
    obtain ⟨Φ, ⟨s⟩⟩ := Φ
    -- On stalks the map is that of geometric fibres, and geometric fibre functors preserve
    -- epimorphisms.
    exact (Functor.PreservesEpimorphisms.of_iso (toSheafCompSheafFiberIso _).symm).preserves f

end TauCeti.FiniteEtaleScheme
