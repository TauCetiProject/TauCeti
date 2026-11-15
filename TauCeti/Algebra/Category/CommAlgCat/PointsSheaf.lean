/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.Fppf

/-!
# Functoriality and full faithfulness of the affine fppf points sheaf

For a commutative ring `R`, `TauCeti.CommAlgCat.pointsSheaf` sends a scheme `X` over `Spec R`
to its `Type (u + 1)`-valued sheaf of points on the affine fppf site `(CommAlgCat R)ᵒᵖ`. This
file upgrades `pointsSheaf` to a functor `pointsSheafFunctor R` and proves that it is full and
faithful.

Full faithfulness combines two ingredients:
1. The fppf topology on `Over (Spec R)` is subcanonical, so the universe-lifted Yoneda functor
   `uliftYoneda` from schemes over `Spec R` into fppf sheaves on `Over (Spec R)` is fully faithful.
2. Relative spectra of `R`-algebras form a cover-dense full subcategory of `Over (Spec R)` for
   the fppf topology (`TauCeti.CommAlgCat.isCoverDense_algSpec`), so restriction of fppf sheaves
   along `algSpec` is full and faithful.

Consequently, morphisms and isomorphisms between schemes over `Spec R` are canonically equivalent
to morphisms and isomorphisms between their affine fppf sheaves of points, without requiring any
finiteness, separation, or affine-scheme hypotheses on the schemes.

## Main declarations

* `TauCeti.CommAlgCat.pointsSheafFunctor`: the functor sending a scheme over `Spec R` to its
  fppf sheaf of affine points.
* `TauCeti.CommAlgCat.fullyFaithfulPointsSheafFunctor`: full faithfulness of `pointsSheafFunctor`.
* `TauCeti.CommAlgCat.pointsSheafHomEquiv`: morphisms `X ⟶ Y` over `Spec R` are equivalent to
  morphisms `pointsSheaf X ⟶ pointsSheaf Y` of affine fppf sheaves.
* `TauCeti.CommAlgCat.pointsSheafIsoEquiv`: isomorphisms `X ≅ Y` over `Spec R` are equivalent to
  isomorphisms `pointsSheaf X ≅ pointsSheaf Y` of affine fppf sheaves.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, functors of points and sheaves on the fppf site.
* P. T. Johnstone, *Sketches of an Elephant*, C2.2, the comparison lemma for dense subsites.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.CommAlgCat

universe u

section Functor

variable (R : Type u) [CommRing R]

/-- **The affine fppf points-sheaf functor.** Sends a scheme `X` over `Spec R` to its
`Type (u + 1)`-valued fppf sheaf of points on `(CommAlgCat R)ᵒᵖ`, and a morphism `f : X ⟶ Y` over
`Spec R` to postcomposition with `f` on `A`-valued points.

The body is exposed so that `(pointsSheafFunctor R).obj X` reduces definitionally to
`pointsSheaf X` in the signatures of `pointsSheafHomEquiv` and `pointsSheafIsoEquiv`. -/
@[expose] noncomputable def pointsSheafFunctor :
    Over (Spec (CommRingCat.of R)) ⥤ Sheaf (fppfTopology R) (Type (u + 1)) where
  obj X := pointsSheaf X
  map f := ⟨Functor.whiskerRight
    (Functor.whiskerLeft (algSpec (CommRingCat.of R)).op (yoneda.map f)) uliftFunctor.{u + 1, u}⟩
  map_id X := by
    ext A ⟨x⟩
    exact congrArg ULift.up (Category.comp_id x)
  map_comp f g := by
    ext A ⟨x⟩
    exact congrArg ULift.up (Category.assoc x f g).symm

/-- On objects, `pointsSheafFunctor` is `pointsSheaf`. -/
@[simp]
theorem pointsSheafFunctor_obj (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctor R).obj X = pointsSheaf X :=
  (rfl)

/-- On morphisms, `pointsSheafFunctor` postcomposes each affine point with `f`. -/
@[simp]
theorem pointsSheafFunctor_map_hom_app_apply {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : ULift.{u + 1, u} ((algSpec (CommRingCat.of R)).obj A.unop ⟶ X)) :
    dsimp% ((pointsSheafFunctor R).map f).hom.app A x = ULift.up (x.down ≫ f) :=
  (rfl)

/-- `pointsSheafFunctor` agrees with the subcanonical universe-lifted Yoneda embedding on
`Over (Spec R)` followed by sheaf restriction along the cover-dense functor `algSpec`. -/
private noncomputable def pointsSheafFunctorIsoUliftYonedaComp :
    pointsSheafFunctor R ≅
      GrothendieckTopology.uliftYoneda.{u + 1}
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) ⋙
          (algSpec (CommRingCat.of R)).sheafPushforwardContinuous (Type (u + 1))
            (fppfTopology R) (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) :=
  NatIso.ofComponents
    (fun X ↦
      { hom := ⟨𝟙 (pointsSheaf X).obj⟩
        inv := ⟨𝟙 (pointsSheaf X).obj⟩ })
    (fun _ ↦ by
      ext A ⟨x⟩
      rfl)

/-- **Full faithfulness of the affine fppf points sheaf.** A morphism of affine fppf sheaves
between the point sheaves of two schemes over `Spec R` comes from a unique morphism of schemes
over `Spec R`. -/
noncomputable def fullyFaithfulPointsSheafFunctor :
    (pointsSheafFunctor R).FullyFaithful := by
  let _ : (algSpec (CommRingCat.of R)).Full :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (algSpec (CommRingCat.of R)).Faithful :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  let hpush : ((algSpec (CommRingCat.of R)).sheafPushforwardContinuous (Type (u + 1))
      (fppfTopology R) (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  exact Functor.FullyFaithful.ofIso
    ((GrothendieckTopology.fullyFaithfulUliftYoneda.{u + 1}
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).comp hpush)
    (pointsSheafFunctorIsoUliftYonedaComp R).symm

instance instFullPointsSheafFunctor : (pointsSheafFunctor R).Full :=
  (fullyFaithfulPointsSheafFunctor R).full

instance instFaithfulPointsSheafFunctor : (pointsSheafFunctor R).Faithful :=
  (fullyFaithfulPointsSheafFunctor R).faithful

end Functor

section Equiv

variable {R : Type u} [CommRing R] {X Y Z : Over (Spec (CommRingCat.of R))}

/-- Morphisms between schemes over `Spec R` are equivalent to morphisms between their affine fppf
sheaves of points. -/
noncomputable def pointsSheafHomEquiv :
    (X ⟶ Y) ≃ (pointsSheaf X ⟶ pointsSheaf Y) :=
  (fullyFaithfulPointsSheafFunctor R).homEquiv

/-- The forward direction of `pointsSheafHomEquiv` is the action of `pointsSheafFunctor` on
morphisms. -/
theorem pointsSheafHomEquiv_apply (f : X ⟶ Y) :
    pointsSheafHomEquiv f = (pointsSheafFunctor R).map f :=
  (rfl)

/-- Applying `pointsSheafHomEquiv` to `f` postcomposes each affine point with `f`. -/
@[simp]
theorem pointsSheafHomEquiv_hom_app_apply (f : X ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : ULift.{u + 1, u} ((algSpec (CommRingCat.of R)).obj A.unop ⟶ X)) :
    dsimp% (pointsSheafHomEquiv f).hom.app A x = ULift.up (x.down ≫ f) :=
  (rfl)

/-- `pointsSheafFunctor` recovers any sheaf morphism from its descended scheme morphism. -/
theorem map_pointsSheafHomEquiv_symm (α : pointsSheaf X ⟶ pointsSheaf Y) :
    (pointsSheafFunctor R).map (pointsSheafHomEquiv.symm α) = α :=
  (fullyFaithfulPointsSheafFunctor R).map_preimage α

/-- Descending the points-sheaf map of a scheme morphism recovers that morphism. -/
theorem pointsSheafHomEquiv_symm_map (f : X ⟶ Y) :
    pointsSheafHomEquiv.symm ((pointsSheafFunctor R).map f) = f :=
  (fullyFaithfulPointsSheafFunctor R).preimage_map f

/-- `pointsSheafHomEquiv` sends the identity scheme morphism to the identity sheaf morphism. -/
@[simp]
theorem pointsSheafHomEquiv_id :
    pointsSheafHomEquiv (𝟙 X) = 𝟙 (pointsSheaf X) :=
  (pointsSheafFunctor R).map_id X

/-- Descending the identity morphism of `pointsSheaf X` gives the identity of `X`. -/
@[simp]
theorem pointsSheafHomEquiv_symm_id :
    pointsSheafHomEquiv.symm (𝟙 (pointsSheaf X)) = 𝟙 X := by
  rw [← pointsSheafHomEquiv_id, Equiv.symm_apply_apply]

/-- `pointsSheafHomEquiv` preserves composition. -/
@[simp]
theorem pointsSheafHomEquiv_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointsSheafHomEquiv (f ≫ g) = pointsSheafHomEquiv f ≫ pointsSheafHomEquiv g :=
  (pointsSheafFunctor R).map_comp f g

/-- Descending morphisms of points sheaves preserves composition. -/
@[simp]
theorem pointsSheafHomEquiv_symm_comp (α : pointsSheaf X ⟶ pointsSheaf Y)
    (β : pointsSheaf Y ⟶ pointsSheaf Z) :
    pointsSheafHomEquiv.symm (α ≫ β) =
      pointsSheafHomEquiv.symm α ≫ pointsSheafHomEquiv.symm β :=
  (fullyFaithfulPointsSheafFunctor R).preimage_comp α β

/-- Isomorphisms between schemes over `Spec R` are equivalent to isomorphisms between their affine
fppf sheaves of points. -/
noncomputable def pointsSheafIsoEquiv :
    (X ≅ Y) ≃ (pointsSheaf X ≅ pointsSheaf Y) where
  toFun e :=
    { hom := pointsSheafHomEquiv e.hom
      inv := pointsSheafHomEquiv e.inv
      hom_inv_id := by rw [← pointsSheafHomEquiv_comp, e.hom_inv_id, pointsSheafHomEquiv_id]
      inv_hom_id := by rw [← pointsSheafHomEquiv_comp, e.inv_hom_id, pointsSheafHomEquiv_id] }
  invFun := (fullyFaithfulPointsSheafFunctor R).preimageIso
  left_inv e := by
    ext1
    exact e.hom |> pointsSheafHomEquiv.symm_apply_apply
  right_inv e := by
    ext1
    exact e.hom |> pointsSheafHomEquiv.apply_symm_apply

/-- The forward morphism of `pointsSheafIsoEquiv e` is `pointsSheafHomEquiv e.hom`. -/
@[simp]
theorem pointsSheafIsoEquiv_hom (e : X ≅ Y) :
    (pointsSheafIsoEquiv e).hom = pointsSheafHomEquiv e.hom :=
  (rfl)

/-- The inverse morphism of `pointsSheafIsoEquiv e` is `pointsSheafHomEquiv e.inv`. -/
@[simp]
theorem pointsSheafIsoEquiv_inv (e : X ≅ Y) :
    (pointsSheafIsoEquiv e).inv = pointsSheafHomEquiv e.inv :=
  (rfl)

/-- The forward morphism of a descended isomorphism is the descended forward morphism. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_hom (e : pointsSheaf X ≅ pointsSheaf Y) :
    (pointsSheafIsoEquiv.symm e).hom = pointsSheafHomEquiv.symm e.hom :=
  (rfl)

/-- The inverse morphism of a descended isomorphism is the descended inverse morphism. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_inv (e : pointsSheaf X ≅ pointsSheaf Y) :
    (pointsSheafIsoEquiv.symm e).inv = pointsSheafHomEquiv.symm e.inv :=
  (rfl)

/-- `pointsSheafIsoEquiv` sends the identity isomorphism to the identity isomorphism. -/
@[simp]
theorem pointsSheafIsoEquiv_refl :
    pointsSheafIsoEquiv (Iso.refl X) = Iso.refl (pointsSheaf X) := by
  ext1
  exact pointsSheafHomEquiv_id

/-- Descending the identity isomorphism of `pointsSheaf X` gives `Iso.refl X`. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_refl :
    pointsSheafIsoEquiv.symm (Iso.refl (pointsSheaf X)) = Iso.refl X := by
  ext1
  exact pointsSheafHomEquiv_symm_id

/-- Descending isomorphisms of points sheaves commutes with composition of isomorphisms. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_trans (e : pointsSheaf X ≅ pointsSheaf Y)
    (f : pointsSheaf Y ≅ pointsSheaf Z) :
    pointsSheafIsoEquiv.symm (e ≪≫ f) =
      pointsSheafIsoEquiv.symm e ≪≫ pointsSheafIsoEquiv.symm f := by
  ext1
  exact pointsSheafHomEquiv_symm_comp e.hom f.hom

/-- Descending isomorphisms of points sheaves commutes with symmetry. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_symm (e : pointsSheaf X ≅ pointsSheaf Y) :
    pointsSheafIsoEquiv.symm e.symm = (pointsSheafIsoEquiv.symm e).symm :=
  (rfl)

/-- Any isomorphism-invariant property of scheme morphisms transfers between the structural
morphisms of two schemes over `Spec R` whose affine fppf sheaves of points are isomorphic. -/
theorem morphismProperty_hom_iff_of_pointsSheafIso (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (e : pointsSheaf X ≅ pointsSheaf Y) :
    P X.hom ↔ P Y.hom := by
  let eXY : X ≅ Y := pointsSheafIsoEquiv.symm e
  have : IsIso eXY.hom.left := ((Over.forget (Spec (CommRingCat.of R))).mapIso eXY).isIso_hom
  rw [← Over.w eXY.hom, P.cancel_left_of_respectsIso]

end Equiv

end TauCeti.CommAlgCat
