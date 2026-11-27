/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.AtlasRelation
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.QuotientSheaf
public import TauCeti.CategoryTheory.Sites.QuotientSheaf.Represented

/-!
# Presentations of algebraic spaces

Let `F` be an fppf sheaf on schemes and `a : h_U ⟶ F` an étale atlas. Its kernel pair is
represented by a scheme `R = U ×_F U`, and the two projections `s, t : R ⟶ U` form an étale
equivalence relation (`TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.of_etaleAtlas`). This file
proves that `F` is the quotient sheaf `U/R` of this relation (Stacks, Spaces, Lemma 65.9.1
(0262), Definition 65.9.3 (0263)): every algebraic space has a presentation by an étale
equivalence relation on a scheme.

The quotient sheaf `TauCeti.AlgebraicGeometry.Spaces.quotientSheaf s t` takes values in
`Type (u + 1)`, where Mathlib's sheafification for the big fppf site lands, while `F` takes values
in `Type u`. The comparison is therefore with the image of `F` under Mathlib's
`sheafCompose _ uliftFunctor`, the sheaf `TauCeti.AlgebraicGeometry.Spaces.uliftSheaf hF`.

The proof is `TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_isKernelPair`: the atlas, as a
morphism of sheaves `h_U ⟶ F`, is locally surjective for the fppf topology, because its base
change along any `h_T ⟶ F` is an étale surjective morphism of schemes and hence an fppf covering
of `T` (`TauCeti.AlgebraicGeometry.Spaces.isLocallySurjective_atlasSheafHom`), and its kernel
pair is `h_R` (`TauCeti.AlgebraicGeometry.Spaces.isKernelPair_atlasSheafHom`).

## Main definitions

* `TauCeti.AlgebraicGeometry.Spaces.uliftSheaf hF`: an fppf sheaf of `Type u` on schemes, as a
  sheaf of `Type (u + 1)`.
* `TauCeti.AlgebraicGeometry.Spaces.atlasSheafHom hF a`: a morphism `h_U ⟶ F` as a morphism of
  sheaves of `Type (u + 1)`.
* `TauCeti.AlgebraicGeometry.Spaces.spacePresentation hF ha`: for an étale atlas `a : h_U ⟶ F`,
  the isomorphism `U/(U ×_F U) ≅ F`.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.π_spacePresentation_hom`: the projection `h_U ⟶ U/R`
  followed by `spacePresentation` is the atlas.
* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.exists_presentation`: every algebraic space
  is the quotient sheaf of an étale equivalence relation on a scheme, through its étale atlas.

For a monomorphism `a`, for instance the identity atlas of a scheme, the presentation is the
diagonal relation `(U, Δ)`: see
`CategoryTheory.Functor.relativelyRepresentable.fst'_self_eq_snd_of_mono` and
`CategoryTheory.Functor.relativelyRepresentable.isIso_snd_self_of_mono`.

## References

* [Stacks Project, Lemma 65.9.1](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Definition 65.9.3](https://stacks.math.columbia.edu/tag/0263)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {F : SchemePresheaf.{u}}

/-- An fppf sheaf `F` of `Type u` on schemes, viewed as a sheaf of `Type (u + 1)` through
`sheafCompose _ uliftFunctor`, in the universe of `TauCeti.AlgebraicGeometry.Spaces.quotientSheaf`.
-/
noncomputable abbrev uliftSheaf (hF : Presheaf.IsSheaf Scheme.fppfTopology F) :
    Sheaf Scheme.fppfTopology.{u} (Type (u + 1)) :=
  (sheafCompose Scheme.fppfTopology uliftFunctor.{u + 1, u}).obj ⟨F, hF⟩

/-- The sections of `uliftSheaf hF` restrict as those of `F`. -/
@[simp]
theorem uliftSheaf_map_down (hF : Presheaf.IsSheaf Scheme.fppfTopology F) {T T' : Scheme.{u}}
    (f : T' ⟶ T) (x : (uliftSheaf hF).obj.obj (op T)) :
    ((uliftSheaf hF).obj.map f.op x).down = F.map f.op x.down :=
  rfl

variable {U : Scheme.{u}}

/-- A morphism `a : h_U ⟶ F` from a scheme to an fppf sheaf, as a morphism of sheaves of
`Type (u + 1)` from the representable sheaf `h_U` to `uliftSheaf hF`: the image of `a` under
`sheafCompose _ uliftFunctor`. -/
noncomputable abbrev atlasSheafHom (hF : Presheaf.IsSheaf Scheme.fppfTopology F)
    (a : yoneda.obj U ⟶ F) :
    Scheme.fppfTopology.uliftYoneda.{u + 1}.obj U ⟶ uliftSheaf hF :=
  (sheafCompose Scheme.fppfTopology uliftFunctor.{u + 1, u}).map (ObjectProperty.homMk a)

/-- The component of `atlasSheafHom hF a` at a scheme `T` sends a `T`-point `x` of `U` to the
image of `x` under `a`. -/
theorem atlasSheafHom_hom_app_down (hF : Presheaf.IsSheaf Scheme.fppfTopology F)
    (a : yoneda.obj U ⟶ F) {T : Scheme.{u}} (x : T ⟶ U) :
    ((atlasSheafHom hF a).hom.app (op T) (ULift.up x)).down = a.app (op T) x :=
  rfl

/-- A morphism of schemes `f : V ⟶ U` followed by `atlasSheafHom hF a` is
`atlasSheafHom hF (yoneda.map f ≫ a)`. -/
@[reassoc (attr := simp)]
theorem uliftYoneda_map_atlasSheafHom (hF : Presheaf.IsSheaf Scheme.fppfTopology F)
    (a : yoneda.obj U ⟶ F) {V : Scheme.{u}} (f : V ⟶ U) :
    Scheme.fppfTopology.uliftYoneda.{u + 1}.map f ≫ atlasSheafHom hF a =
      atlasSheafHom hF (yoneda.map f ≫ a) :=
  ((sheafCompose _ _).map_comp _ _).symm

/-- The underlying morphism of presheaves of `Scheme.fppfTopology.uliftYoneda.map f`. -/
private theorem sheafToPresheaf_map_uliftYoneda_map {V : Scheme.{u}} (f : V ⟶ U) :
    (sheafToPresheaf _ _).map (Scheme.fppfTopology.uliftYoneda.{u + 1}.map f) =
      Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u} :=
  rfl

variable {a : yoneda.obj U ⟶ F}

/-- **An étale atlas is fppf locally surjective.** For an étale atlas `a : h_U ⟶ F` of an fppf
sheaf, every `T`-point of `F` lifts to `U` after pulling back along the étale surjective base
change `U ×_F T ⟶ T`, which is an fppf covering. -/
theorem isLocallySurjective_atlasSheafHom (hF : Presheaf.IsSheaf Scheme.fppfTopology F)
    (ha : EtaleAtlas a) : Sheaf.IsLocallySurjective (atlasSheafHom hF a) where
  imageSieve_mem {T} x := by
    let g : yoneda.obj T ⟶ F := yonedaEquiv.symm x.down
    have hr := ha.relativelyRepresentable
    have := ha.etale_snd g
    have := ha.surjective_snd g
    refine Scheme.fppfTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
      (hr.snd g).singleton_mem_fppfPrecoverage)
    rintro T' f ⟨W, b, c, ⟨⟩, rfl⟩
    refine ⟨ULift.up (b ≫ hr.fst' g), ULift.ext ?_⟩
    rw [atlasSheafHom_hom_app_down, uliftSheaf_map_down]
    have hw := congrArg (fun φ ↦ yonedaEquiv (yoneda.map b ≫ φ)) (hr.isPullback' g).w
    simp only [← Functor.map_comp_assoc, yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hw
    exact hw.trans (yonedaEquiv_symm_app_apply _ _ _)

/-- **The kernel pair of an atlas is the scheme representing it.** For `a : h_U ⟶ F`
representable by schemes, with `R = U ×_F U` and projections `t = hr.fst' a`, `s = hr.snd a`,
the square `h_R ⇉ h_U ⟶ F` is a kernel pair in fppf sheaves of `Type (u + 1)`. -/
theorem isKernelPair_atlasSheafHom (hF : Presheaf.IsSheaf Scheme.fppfTopology F)
    (hr : yoneda.relativelyRepresentable a) :
    IsKernelPair (atlasSheafHom hF a) (Scheme.fppfTopology.uliftYoneda.{u + 1}.map (hr.fst' a))
      (Scheme.fppfTopology.uliftYoneda.{u + 1}.map (hr.snd a)) := by
  refine IsPullback.of_map (sheafToPresheaf _ _)
    (by rw [uliftYoneda_map_atlasSheafHom, uliftYoneda_map_atlasSheafHom, (hr.isPullback' a).w]) ?_
  rw [sheafToPresheaf_map_uliftYoneda_map, sheafToPresheaf_map_uliftYoneda_map,
    ObjectProperty.ι_map, sheafCompose_map_hom, ObjectProperty.homMk_hom]
  exact (hr.isPullback' a).map ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u})

/-- **Every space with an étale atlas is a quotient of a scheme by an étale equivalence relation**
(Stacks, Spaces, Lemma 65.9.1 (0262)). For an fppf sheaf `F` with an étale atlas `a : h_U ⟶ F`,
the quotient sheaf of the étale equivalence relation `U ×_F U ⇉ U` is `F`. -/
noncomputable def spacePresentation (hF : Presheaf.IsSheaf Scheme.fppfTopology F)
    (ha : EtaleAtlas a) :
    quotientSheaf (ha.relativelyRepresentable.snd a) (ha.relativelyRepresentable.fst' a) ≅
      uliftSheaf hF :=
  have := isLocallySurjective_atlasSheafHom hF ha
  have := TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_isKernelPair _
    (isKernelPair_atlasSheafHom hF ha.relativelyRepresentable)
  asIso (TauCeti.CategoryTheory.quotientSheaf.desc (atlasSheafHom hF a)
    (isKernelPair_atlasSheafHom hF ha.relativelyRepresentable).w)

/-- The projection `h_U ⟶ U/(U ×_F U)` followed by `spacePresentation hF ha` is the atlas. -/
@[reassoc (attr := simp)]
theorem π_spacePresentation_hom (ha : EtaleAtlas a) :
    TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology
        (ha.relativelyRepresentable.snd a) (ha.relativelyRepresentable.fst' a) ≫
        (spacePresentation hF ha).hom =
      atlasSheafHom hF a :=
  TauCeti.CategoryTheory.quotientSheaf.π_desc _ _

/-- The atlas followed by the inverse of `spacePresentation hF ha` is the projection
`h_U ⟶ U/(U ×_F U)`. -/
@[reassoc (attr := simp)]
theorem atlasSheafHom_spacePresentation_inv (ha : EtaleAtlas a) :
    atlasSheafHom hF a ≫ (spacePresentation hF ha).inv =
      TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology
        (ha.relativelyRepresentable.snd a) (ha.relativelyRepresentable.fst' a) :=
  (Iso.comp_inv_eq _).2 (π_spacePresentation_hom ha).symm

/-- **Every algebraic space has a presentation** (Stacks, Spaces, Lemma 65.9.1 (0262) and
Definition 65.9.3 (0263)): an algebraic space `F` is the quotient sheaf `U/R` of an étale
equivalence relation `s, t : R ⟶ U` on a scheme, through an étale atlas `a : h_U ⟶ F`: the
isomorphism `U/R ≅ F` composed with the projection `h_U ⟶ U/R` is `a`. -/
theorem IsAlgebraicSpace.exists_presentation (hF : IsAlgebraicSpace F) :
    ∃ (U R : Scheme.{u}) (s t : R ⟶ U) (a : yoneda.obj U ⟶ F),
      EtaleAtlas a ∧ EtaleEquivRel s t ∧ ∃ e : quotientSheaf s t ≅ uliftSheaf hF.isSheaf,
        TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology s t ≫ e.hom =
          atlasSheafHom hF.isSheaf a := by
  obtain ⟨U, a, ha⟩ := hF.exists_etaleAtlas
  exact ⟨U, _, _, _, a, ha, EtaleEquivRel.of_etaleAtlas ha, spacePresentation hF.isSheaf ha,
    π_spacePresentation_hom ha⟩

end TauCeti.AlgebraicGeometry.Spaces
