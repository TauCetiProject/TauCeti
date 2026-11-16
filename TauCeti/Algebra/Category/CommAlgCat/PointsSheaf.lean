/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import TauCeti.Algebra.Category.CommAlgCat.Fppf

/-!
# Full faithfulness of the fppf sheaf of points

For a commutative ring `R`, every scheme `X` over `Spec R` defines an fppf sheaf of points
`TauCeti.CommAlgCat.pointsSheaf X` on the affine fppf site `(CommAlgCat R)ᵒᵖ`, sending a
commutative `R`-algebra `A` to the set of morphisms `Spec A ⟶ X` over `Spec R` lifted to
`Type (u + 1)`.

This file upgrades `pointsSheaf` to a functor `TauCeti.CommAlgCat.pointsSheafFunctor` and proves
that it is fully faithful via `TauCeti.CommAlgCat.isDenseSubsite_algSpec` and
`TauCeti.CommAlgCat.fppfSheafEquiv` (`TauCeti.CommAlgCat.pointsSheafFunctorIso`). Consequently,
morphisms and isomorphisms of fppf point sheaves descend uniquely to `R`-schemes
(`TauCeti.CommAlgCat.homOfPointsSheafHom`, `TauCeti.CommAlgCat.isoOfPointsSheafIso`), and fppf-local
surjectivity on point sheaves implies surjectivity on underlying schemes
(`TauCeti.CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap`).

## Main declarations

* `TauCeti.CommAlgCat.pointsSheafMap`: the morphism of fppf point sheaves induced by an `R`-scheme
  morphism.
* `TauCeti.CommAlgCat.pointsSheafFunctor`: the functor sending an `R`-scheme to its fppf sheaf of
  points.
* `TauCeti.CommAlgCat.pointsSheafFunctorIso`: natural isomorphism with subcanonical Yoneda on
  `Over (Spec R)` followed by `(fppfSheafEquiv R (Type (u + 1))).inverse`.
* `TauCeti.CommAlgCat.fullyFaithfulPointsSheafFunctor`: full faithfulness of `pointsSheafFunctor`.
* `TauCeti.CommAlgCat.homOfPointsSheafHom`, `TauCeti.CommAlgCat.pointsSheafHomEquiv`,
  `TauCeti.CommAlgCat.isoOfPointsSheafIso`: descent of morphisms and isomorphisms of fppf sheaves of
  points to `R`-schemes.
* `TauCeti.CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap`: fppf-local
  surjectivity on sheaves of points implies surjectivity on underlying schemes.

## References

* P. T. Johnstone, *Sketches of an Elephant*, C2.2, the comparison lemma for dense subsites.
* J. S. Milne, *Algebraic Groups* (2017), §5, functors of points and fppf sheaves.
* [The Stacks Project, Tag 01JF](https://stacks.math.columbia.edu/tag/01JF), schemes as functors on
  rings.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u

namespace CommAlgCat

variable {R : Type u} [CommRing R] {X Y Z : Over (Spec (CommRingCat.of R))}

/-- Postcomposition with a morphism `f : X ⟶ Y` of schemes over `Spec R`, as a morphism between
their fppf sheaves of points. -/
noncomputable def pointsSheafMap (f : X ⟶ Y) : pointsSheaf X ⟶ pointsSheaf Y where
  hom := Functor.whiskerRight (Functor.whiskerLeft (algSpec (CommRingCat.of R)).op (yoneda.map f))
    uliftFunctor.{u + 1, u}

/-- Evaluating `pointsSheafMap f` on an affine point postcomposes that point with `f`. -/
@[simp] theorem pointsSheafMap_hom_app_apply (f : X ⟶ Y) (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (a : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X) :
    dsimp% (pointsSheafMap f).hom.app A (ULift.up a) = ULift.up (a ≫ f) := (rfl)

/-- The identity morphism induces the identity on fppf sheaves of points. -/
@[simp] theorem pointsSheafMap_id (X : Over (Spec (CommRingCat.of R))) :
    pointsSheafMap (𝟙 X) = 𝟙 (pointsSheaf X) := by
  ext A ⟨a⟩; exact congrArg ULift.up (Category.comp_id a)

/-- Composition of morphisms over `Spec R` becomes composition on fppf sheaves of points. -/
@[simp] theorem pointsSheafMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointsSheafMap (f ≫ g) = pointsSheafMap f ≫ pointsSheafMap g := by
  ext A ⟨a⟩; exact congrArg ULift.up (Category.assoc a f g).symm

/-- An isomorphism of schemes over `Spec R` induces an isomorphism of their fppf sheaves of
points. -/
noncomputable def pointsSheafIso (e : X ≅ Y) : pointsSheaf X ≅ pointsSheaf Y where
  hom := pointsSheafMap e.hom
  inv := pointsSheafMap e.inv
  hom_inv_id := by rw [← pointsSheafMap_comp, e.hom_inv_id, pointsSheafMap_id]
  inv_hom_id := by rw [← pointsSheafMap_comp, e.inv_hom_id, pointsSheafMap_id]

/-- The forward morphism of `pointsSheafIso e` is induced by `e.hom`. -/
@[simp] theorem pointsSheafIso_hom (e : X ≅ Y) : (pointsSheafIso e).hom = pointsSheafMap e.hom :=
  (rfl)

/-- The inverse morphism of `pointsSheafIso e` is induced by `e.inv`. -/
@[simp] theorem pointsSheafIso_inv (e : X ≅ Y) : (pointsSheafIso e).inv = pointsSheafMap e.inv :=
  (rfl)

/-- The identity isomorphism induces the identity isomorphism on fppf sheaves of points. -/
@[simp] theorem pointsSheafIso_refl (X : Over (Spec (CommRingCat.of R))) :
    pointsSheafIso (Iso.refl X) = Iso.refl (pointsSheaf X) := Iso.ext <| pointsSheafMap_id X

/-- Inverting an isomorphism of schemes over `Spec R` inverts `pointsSheafIso`. -/
@[simp] theorem pointsSheafIso_symm (e : X ≅ Y) : pointsSheafIso e.symm = (pointsSheafIso e).symm :=
  (rfl)

/-- Composition of scheme isomorphisms over `Spec R` becomes composition of `pointsSheafIso`. -/
@[simp] theorem pointsSheafIso_trans (e₁ : X ≅ Y) (e₂ : Y ≅ Z) :
    pointsSheafIso (e₁ ≪≫ e₂) = pointsSheafIso e₁ ≪≫ pointsSheafIso e₂ :=
  Iso.ext <| pointsSheafMap_comp e₁.hom e₂.hom

variable (R) in
/-- **The fppf sheaf-of-points functor** from schemes over `Spec R` to fppf sheaves on the affine
site `(CommAlgCat R)ᵒᵖ`. -/
noncomputable def pointsSheafFunctor :
    Over (Spec (CommRingCat.of R)) ⥤ Sheaf (fppfTopology R) (Type (u + 1)) where
  obj := pointsSheaf
  map := pointsSheafMap
  map_id := pointsSheafMap_id
  map_comp := pointsSheafMap_comp

/-- On objects, `pointsSheafFunctor` is `pointsSheaf`. -/
@[simp] theorem pointsSheafFunctor_obj (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctor R).obj X = pointsSheaf X := (rfl)

/-- On morphisms, `pointsSheafFunctor` is `pointsSheafMap`, transported along
`pointsSheafFunctor_obj`. -/
@[simp] theorem pointsSheafFunctor_map (f : X ⟶ Y) :
    (pointsSheafFunctor R).map f = eqToHom (pointsSheafFunctor_obj X) ≫ pointsSheafMap f ≫
      eqToHom (pointsSheafFunctor_obj Y).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- On isomorphisms, `pointsSheafFunctor.mapIso` agrees with `pointsSheafIso`, transported along
`pointsSheafFunctor_obj`. -/
@[simp] theorem pointsSheafFunctor_mapIso (e : X ≅ Y) :
    (pointsSheafFunctor R).mapIso e = eqToIso (pointsSheafFunctor_obj X) ≪≫ pointsSheafIso e ≪≫
      eqToIso (pointsSheafFunctor_obj Y).symm := Iso.ext <| pointsSheafFunctor_map e.hom

/-- On morphisms, restricting `uliftYoneda` along `(fppfSheafEquiv R (Type (u + 1))).inverse`
agrees with `pointsSheafMap`, transported along `fppfSheafEquiv_inverse_obj_uliftYoneda`. -/
theorem fppfSheafEquiv_inverse_map_uliftYoneda (f : X ⟶ Y) :
    (fppfSheafEquiv R (Type (u + 1))).inverse.map
        ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).uliftYoneda.{u + 1}.map f) =
      eqToHom (fppfSheafEquiv_inverse_obj_uliftYoneda X) ≫ pointsSheafMap f ≫
        eqToHom (fppfSheafEquiv_inverse_obj_uliftYoneda Y).symm := by
  apply Sheaf.hom_ext
  simp only [fppfSheafEquiv_inverse_map_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.eqToHom_hom]; rfl

variable (R) in
/-- `pointsSheafFunctor` is naturally isomorphic to subcanonical Yoneda on `Over (Spec R)`
followed by restriction along `algSpec`. -/
noncomputable def pointsSheafFunctorIso :
    pointsSheafFunctor R ≅
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).uliftYoneda.{u + 1} ⋙
        (fppfSheafEquiv R (Type (u + 1))).inverse :=
  NatIso.ofComponents (fun X ↦ eqToIso ((pointsSheafFunctor_obj X).trans
      (fppfSheafEquiv_inverse_obj_uliftYoneda X).symm)) fun {X Y} f ↦ by
    rw [pointsSheafFunctor_map, Functor.comp_map, fppfSheafEquiv_inverse_map_uliftYoneda]; simp

/-- At each `R`-scheme `X`, `pointsSheafFunctorIso` is the `eqToIso` given by
`pointsSheafFunctor_obj` and `fppfSheafEquiv_inverse_obj_uliftYoneda`. -/
@[simp] theorem pointsSheafFunctorIso_app (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctorIso R).app X = eqToIso ((pointsSheafFunctor_obj X).trans
      (fppfSheafEquiv_inverse_obj_uliftYoneda X).symm) := (rfl)

/-- The forward component of `pointsSheafFunctorIso` at `X` is the canonical `eqToHom`. -/
@[simp] theorem pointsSheafFunctorIso_hom_app (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctorIso R).hom.app X = eqToHom ((pointsSheafFunctor_obj X).trans
      (fppfSheafEquiv_inverse_obj_uliftYoneda X).symm) := (rfl)

/-- The inverse component of `pointsSheafFunctorIso` at `X` is the canonical `eqToHom`. -/
@[simp] theorem pointsSheafFunctorIso_inv_app (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctorIso R).inv.app X = eqToHom ((fppfSheafEquiv_inverse_obj_uliftYoneda X).trans
      (pointsSheafFunctor_obj X).symm) := (rfl)

variable (R) in
/-- **The fppf sheaf-of-points functor is fully faithful.** Morphisms between schemes over
`Spec R` are in natural bijection with morphisms between their affine fppf sheaves of points. -/
noncomputable def fullyFaithfulPointsSheafFunctor : (pointsSheafFunctor R).FullyFaithful :=
  Functor.FullyFaithful.ofIso
    (((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).fullyFaithfulUliftYoneda).comp
      (fppfSheafEquiv R (Type (u + 1))).fullyFaithfulInverse)
    (pointsSheafFunctorIso R).symm

instance instFullPointsSheafFunctor : (pointsSheafFunctor R).Full :=
  (fullyFaithfulPointsSheafFunctor R).full

instance instFaithfulPointsSheafFunctor : (pointsSheafFunctor R).Faithful :=
  (fullyFaithfulPointsSheafFunctor R).faithful

/-- **Morphism of `R`-schemes from a morphism of fppf point sheaves.** Every morphism
`pointsSheaf X ⟶ pointsSheaf Y` is induced by a unique morphism `X ⟶ Y` over `Spec R`. -/
noncomputable def homOfPointsSheafHom (α : pointsSheaf X ⟶ pointsSheaf Y) : X ⟶ Y :=
  (fullyFaithfulPointsSheafFunctor R).preimage
    (eqToHom (pointsSheafFunctor_obj X) ≫ α ≫ eqToHom (pointsSheafFunctor_obj Y).symm)

/-- `pointsSheafMap` recovers the sheaf morphism from `homOfPointsSheafHom`. -/
@[simp] theorem pointsSheafMap_homOfPointsSheafHom (α : pointsSheaf X ⟶ pointsSheaf Y) :
    pointsSheafMap (homOfPointsSheafHom α) = α := by
  have h := (fullyFaithfulPointsSheafFunctor R).map_preimage
    (eqToHom (pointsSheafFunctor_obj X) ≫ α ≫ eqToHom (pointsSheafFunctor_obj Y).symm)
  rw [← homOfPointsSheafHom, pointsSheafFunctor_map] at h
  simpa [Category.assoc] using
    congrArg (eqToHom (pointsSheafFunctor_obj X).symm ≫ · ≫ eqToHom (pointsSheafFunctor_obj Y)) h

/-- `homOfPointsSheafHom` is left inverse to `pointsSheafMap`. -/
@[simp] theorem homOfPointsSheafHom_pointsSheafMap (f : X ⟶ Y) :
    homOfPointsSheafHom (pointsSheafMap f) = f := by
  rw [homOfPointsSheafHom, ← pointsSheafFunctor_map]
  exact (fullyFaithfulPointsSheafFunctor R).preimage_map f

/-- `pointsSheafMap` is injective on `R`-scheme morphisms. -/
theorem pointsSheafMap_injective :
    Function.Injective (pointsSheafMap (R := R) (X := X) (Y := Y)) :=
  Function.LeftInverse.injective homOfPointsSheafHom_pointsSheafMap

/-- Two morphisms of `R`-schemes are equal when they induce the same morphism on fppf sheaves of
points. -/
theorem over_hom_ext_of_pointsSheafMap {f g : X ⟶ Y} (h : pointsSheafMap f = pointsSheafMap g) :
    f = g := pointsSheafMap_injective h

/-- A morphism `f : X ⟶ Y` over `Spec R` equals `homOfPointsSheafHom α` if and only if
`pointsSheafMap f = α`. -/
theorem eq_homOfPointsSheafHom_iff (f : X ⟶ Y) (α : pointsSheaf X ⟶ pointsSheaf Y) :
    f = homOfPointsSheafHom α ↔ pointsSheafMap f = α :=
  ⟨by rintro rfl; exact pointsSheafMap_homOfPointsSheafHom α,
   by rintro rfl; exact (homOfPointsSheafHom_pointsSheafMap f).symm⟩

/-- `homOfPointsSheafHom` sends the identity sheaf morphism to the identity `R`-scheme morphism. -/
@[simp] theorem homOfPointsSheafHom_id (X : Over (Spec (CommRingCat.of R))) :
    homOfPointsSheafHom (𝟙 (pointsSheaf X)) = 𝟙 X := by
  rw [← pointsSheafMap_id, homOfPointsSheafHom_pointsSheafMap]

/-- `homOfPointsSheafHom` preserves composition of morphisms of fppf point sheaves. -/
@[simp] theorem homOfPointsSheafHom_comp (α : pointsSheaf X ⟶ pointsSheaf Y)
    (β : pointsSheaf Y ⟶ pointsSheaf Z) :
    homOfPointsSheafHom (α ≫ β) = homOfPointsSheafHom α ≫ homOfPointsSheafHom β :=
  over_hom_ext_of_pointsSheafMap <| by simp

/-- Composing an affine `A`-valued point of `X` with `homOfPointsSheafHom α` evaluates `α` at
that point. -/
@[reassoc (attr := simp)] theorem comp_homOfPointsSheafHom (α : pointsSheaf X ⟶ pointsSheaf Y)
    {A : CommAlgCat.{u} R} (a : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X) :
    a ≫ homOfPointsSheafHom α = (α.hom.app (op (op A)) (ULift.up a)).down :=
  congrArg (fun β : pointsSheaf X ⟶ pointsSheaf Y ↦ (β.hom.app (op (op A)) (ULift.up a)).down)
    (pointsSheafMap_homOfPointsSheafHom α)

/-- Morphisms `X ⟶ Y` over `Spec R` are equivalent to morphisms `pointsSheaf X ⟶ pointsSheaf Y`
of fppf sheaves. -/
noncomputable def pointsSheafHomEquiv (X Y : Over (Spec (CommRingCat.of R))) :
    (X ⟶ Y) ≃ (pointsSheaf X ⟶ pointsSheaf Y) where
  toFun := pointsSheafMap
  invFun := homOfPointsSheafHom
  left_inv := homOfPointsSheafHom_pointsSheafMap
  right_inv := pointsSheafMap_homOfPointsSheafHom

/-- Forward evaluation of `pointsSheafHomEquiv` is `pointsSheafMap`. -/
@[simp] theorem pointsSheafHomEquiv_apply (f : X ⟶ Y) :
    pointsSheafHomEquiv X Y f = pointsSheafMap f := (rfl)

/-- Inverse evaluation of `pointsSheafHomEquiv` is `homOfPointsSheafHom`. -/
@[simp] theorem pointsSheafHomEquiv_symm_apply (α : pointsSheaf X ⟶ pointsSheaf Y) :
    (pointsSheafHomEquiv X Y).symm α = homOfPointsSheafHom α := (rfl)

/-- An isomorphism of fppf point sheaves descends to an isomorphism of `R`-schemes. -/
instance isIso_homOfPointsSheafHom (α : pointsSheaf X ⟶ pointsSheaf Y) [IsIso α] :
    IsIso (homOfPointsSheafHom α) :=
  ⟨⟨homOfPointsSheafHom (inv α),
    by rw [← homOfPointsSheafHom_comp, IsIso.hom_inv_id, homOfPointsSheafHom_id],
    by rw [← homOfPointsSheafHom_comp, IsIso.inv_hom_id, homOfPointsSheafHom_id]⟩⟩

/-- A morphism of `R`-schemes is an isomorphism when its induced map on fppf sheaves of points is
an isomorphism. -/
theorem isIso_of_isIso_pointsSheafMap (f : X ⟶ Y) [IsIso (pointsSheafMap f)] : IsIso f := by
  rw [← homOfPointsSheafHom_pointsSheafMap f]; infer_instance

/-- **Isomorphism of `R`-schemes from an isomorphism of fppf point sheaves.** -/
noncomputable def isoOfPointsSheafIso (e : pointsSheaf X ≅ pointsSheaf Y) : X ≅ Y where
  hom := homOfPointsSheafHom e.hom
  inv := homOfPointsSheafHom e.inv
  hom_inv_id := by rw [← homOfPointsSheafHom_comp, e.hom_inv_id, homOfPointsSheafHom_id]
  inv_hom_id := by rw [← homOfPointsSheafHom_comp, e.inv_hom_id, homOfPointsSheafHom_id]

/-- The forward morphism of `isoOfPointsSheafIso e` is `homOfPointsSheafHom e.hom`. -/
@[simp] theorem isoOfPointsSheafIso_hom (e : pointsSheaf X ≅ pointsSheaf Y) :
    (isoOfPointsSheafIso e).hom = homOfPointsSheafHom e.hom := (rfl)

/-- The inverse morphism of `isoOfPointsSheafIso e` is `homOfPointsSheafHom e.inv`. -/
@[simp] theorem isoOfPointsSheafIso_inv (e : pointsSheaf X ≅ pointsSheaf Y) :
    (isoOfPointsSheafIso e).inv = homOfPointsSheafHom e.inv := (rfl)

/-- Applying `pointsSheafIso` to `isoOfPointsSheafIso e` recovers `e`. -/
@[simp] theorem pointsSheafIso_isoOfPointsSheafIso (e : pointsSheaf X ≅ pointsSheaf Y) :
    pointsSheafIso (isoOfPointsSheafIso e) = e := Iso.ext <| pointsSheafMap_homOfPointsSheafHom _

/-- Applying `isoOfPointsSheafIso` to `pointsSheafIso e` recovers `e`. -/
@[simp] theorem isoOfPointsSheafIso_pointsSheafIso (e : X ≅ Y) :
    isoOfPointsSheafIso (pointsSheafIso e) = e := Iso.ext <| homOfPointsSheafHom_pointsSheafMap _

/-- `isoOfPointsSheafIso` preserves identity isomorphisms. -/
@[simp] theorem isoOfPointsSheafIso_refl (X : Over (Spec (CommRingCat.of R))) :
    isoOfPointsSheafIso (Iso.refl (pointsSheaf X)) = Iso.refl X :=
  Iso.ext <| homOfPointsSheafHom_id X

/-- `isoOfPointsSheafIso` commutes with symmetry of isomorphisms. -/
@[simp] theorem isoOfPointsSheafIso_symm (e : pointsSheaf X ≅ pointsSheaf Y) :
    isoOfPointsSheafIso e.symm = (isoOfPointsSheafIso e).symm := (rfl)

/-- `isoOfPointsSheafIso` preserves composition of sheaf isomorphisms. -/
@[simp] theorem isoOfPointsSheafIso_trans (e₁ : pointsSheaf X ≅ pointsSheaf Y)
    (e₂ : pointsSheaf Y ≅ pointsSheaf Z) :
    isoOfPointsSheafIso (e₁ ≪≫ e₂) = isoOfPointsSheafIso e₁ ≪≫ isoOfPointsSheafIso e₂ :=
  Iso.ext <| homOfPointsSheafHom_comp e₁.hom e₂.hom

/-- **Local surjectivity on fppf point sheaves implies surjectivity on underlying schemes.**
If `f : X ⟶ Y` over `Spec R` induces a locally surjective morphism `pointsSheaf X ⟶ pointsSheaf Y`,
then `f.left : X.left ⟶ Y.left` is surjective. -/
theorem surjective_left_of_isLocallySurjective_pointsSheafMap (f : X ⟶ Y)
    [Sheaf.IsLocallySurjective (pointsSheafMap f)] : Surjective f.left := by
  refine ⟨fun y ↦ ?_⟩
  let φ₀ : CommRingCat.of R ⟶ Y.left.residueField y :=
    Spec.preimage (Y.left.fromSpecResidueField y ≫ Y.hom)
  let _ : Algebra R (Y.left.residueField y) := φ₀.hom.toAlgebra
  have hφ₀ : Spec.map (CommRingCat.ofHom (algebraMap R (Y.left.residueField y))) =
      Y.left.fromSpecResidueField y ≫ Y.hom := Spec.map_preimage _
  let A : CommAlgCat.{u} R := CommAlgCat.of R (Y.left.residueField y)
  let yPt : (algSpec (CommRingCat.of R)).obj (op A) ⟶ Y :=
    Over.homMk (eqToHom (algSpec_obj_left (R := CommRingCat.of R) (op A)) ≫
      Y.left.fromSpecResidueField y)
      (by rw [Category.assoc, ← hφ₀, eqToHom_algSpec_obj_left_comp_Spec_map])
  have hS : Presheaf.imageSieve (pointsSheafMap f).hom (ULift.up yPt) ∈ fppfTopology R (op A) :=
    Presheaf.imageSieve_mem (CA := fun X ↦ X) (fppfTopology R) (pointsSheafMap f).hom
      (U := op (op A)) (ULift.up yPt)
  let z₀ : Spec (Y.left.residueField y) := IsLocalRing.closedPoint (Y.left.residueField y)
  obtain ⟨Z, hZ, z, g, B, ψ, hB, hgz, ⟨⟨xPt⟩, hxPt⟩, hfac⟩ :=
    exists_over_comp_left_eq_of_mem_fppfTopology hS z₀
  rw [pointsSheafMap_hom_app_apply] at hxPt
  have hxEq : xPt ≫ f = (algSpec (CommRingCat.of R)).map ψ ≫ yPt := congrArg ULift.down hxPt
  have hcomp : hB.left ≫ xPt.left ≫ f.left = g ≫ Y.left.fromSpecResidueField y := by
    simpa only [Over.comp_left, Over.homMk_left, Category.assoc, yPt, ← reassoc_of% hfac] using
      congrArg Over.Hom.left (congrArg (hB ≫ ·) hxEq)
  have hz := congrArg (fun m : Z ⟶ Y.left ↦ m z) hcomp
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hgz,
    Scheme.fromSpecResidueField_apply] at hz
  exact ⟨xPt.left (hB.left z), hz⟩

/-- Descending a locally surjective morphism of fppf point sheaves yields a surjective morphism on
underlying schemes. -/
instance instSurjectiveHomOfPointsSheafHomLeft (α : pointsSheaf X ⟶ pointsSheaf Y)
    [Sheaf.IsLocallySurjective α] : Surjective (homOfPointsSheafHom α).left := by
  have : Sheaf.IsLocallySurjective (pointsSheafMap (homOfPointsSheafHom α)) := by
    rwa [pointsSheafMap_homOfPointsSheafHom]
  exact surjective_left_of_isLocallySurjective_pointsSheafMap (homOfPointsSheafHom α)

end CommAlgCat

end TauCeti
