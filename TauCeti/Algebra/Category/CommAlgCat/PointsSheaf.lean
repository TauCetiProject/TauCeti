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
that it is fully faithful. Because `(CommAlgCat R)ᵒᵖ` is a dense subsite of `Over (Spec R)` for
the fppf topology (`TauCeti.CommAlgCat.isDenseSubsite_algSpec`), restricting fppf sheaves on
`Over (Spec R)` to affine schemes is an equivalence of sheaf categories
(`TauCeti.CommAlgCat.fppfSheafEquiv`), and `pointsSheafFunctor` is naturally isomorphic to
subcanonical Yoneda followed by this equivalence (`TauCeti.CommAlgCat.pointsSheafFunctorIso`).

Consequently, morphisms and isomorphisms between the fppf sheaves of points of two `R`-schemes
descend uniquely to morphisms and isomorphisms of the `R`-schemes themselves
(`TauCeti.CommAlgCat.homOfPointsSheafHom`, `TauCeti.CommAlgCat.isoOfPointsSheafIso`). Moreover,
any `R`-scheme morphism whose induced map on fppf sheaves of points is locally surjective is
surjective on underlying schemes
(`TauCeti.CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap`).

## Main declarations

* `TauCeti.CommAlgCat.pointsSheafMap`: the morphism of fppf point sheaves induced by an
  `R`-scheme morphism.
* `TauCeti.CommAlgCat.pointsSheafFunctor`: the functor sending an `R`-scheme to its fppf sheaf of
  points.
* `TauCeti.CommAlgCat.pointsSheafFunctorIso`: natural isomorphism identifying `pointsSheafFunctor`
  with subcanonical Yoneda on `Over (Spec R)` followed by
  `(fppfSheafEquiv R (Type (u + 1))).inverse`.
* `TauCeti.CommAlgCat.fullyFaithfulPointsSheafFunctor`: full faithfulness of
  `pointsSheafFunctor`.
* `TauCeti.CommAlgCat.homOfPointsSheafHom`: the unique `R`-scheme morphism inducing a morphism of
  fppf sheaves of points.
* `TauCeti.CommAlgCat.pointsSheafHomEquiv`: equivalence between `R`-scheme morphisms and
  morphisms of their fppf sheaves of points.
* `TauCeti.CommAlgCat.isoOfPointsSheafIso`: the unique `R`-scheme isomorphism inducing an
  isomorphism of fppf sheaves of points.
* `TauCeti.CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap`: fppf-local
  surjectivity on sheaves of points implies surjectivity on underlying schemes.

## References

* P. T. Johnstone, *Sketches of an Elephant*, C2.2, the comparison lemma for dense subsites.
* J. S. Milne, *Algebraic Groups* (2017), §5, functors of points and fppf sheaves.
* [The Stacks Project, Tag 01JF](https://stacks.math.columbia.edu/tag/01JF), schemes as functors
  on rings.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u

namespace CommAlgCat

section Functor

variable {R : Type u} [CommRing R]

/-- Postcomposition with a morphism `f : X ⟶ Y` of schemes over `Spec R`, as a morphism between
their fppf sheaves of points. -/
noncomputable def pointsSheafMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    pointsSheaf X ⟶ pointsSheaf Y where
  hom := Functor.whiskerRight (Functor.whiskerLeft (algSpec (CommRingCat.of R)).op (yoneda.map f))
    uliftFunctor.{u + 1, u}

/-- Evaluating `pointsSheafMap f` on an affine point postcomposes that point with `f`. -/
@[simp]
theorem pointsSheafMap_hom_app_apply {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (a : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X) :
    dsimp% (pointsSheafMap f).hom.app A (ULift.up a) = ULift.up (a ≫ f) :=
  (rfl)

/-- The identity morphism induces the identity on fppf sheaves of points. -/
@[simp]
theorem pointsSheafMap_id (X : Over (Spec (CommRingCat.of R))) :
    pointsSheafMap (𝟙 X) = 𝟙 (pointsSheaf X) := by
  ext A ⟨a⟩
  exact congrArg ULift.up (Category.comp_id a)

/-- Composition of morphisms over `Spec R` becomes composition on fppf sheaves of points. -/
@[simp]
theorem pointsSheafMap_comp {X Y Z : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointsSheafMap (f ≫ g) = pointsSheafMap f ≫ pointsSheafMap g := by
  ext A ⟨a⟩
  exact congrArg ULift.up (Category.assoc a f g).symm

/-- An isomorphism of schemes over `Spec R` induces an isomorphism of their fppf sheaves of
points. -/
noncomputable def pointsSheafIso {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    pointsSheaf X ≅ pointsSheaf Y where
  hom := pointsSheafMap e.hom
  inv := pointsSheafMap e.inv
  hom_inv_id := by rw [← pointsSheafMap_comp, e.hom_inv_id, pointsSheafMap_id]
  inv_hom_id := by rw [← pointsSheafMap_comp, e.inv_hom_id, pointsSheafMap_id]

/-- The forward morphism of `pointsSheafIso e` is induced by `e.hom`. -/
@[simp]
theorem pointsSheafIso_hom {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    (pointsSheafIso e).hom = pointsSheafMap e.hom :=
  (rfl)

/-- The inverse morphism of `pointsSheafIso e` is induced by `e.inv`. -/
@[simp]
theorem pointsSheafIso_inv {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    (pointsSheafIso e).inv = pointsSheafMap e.inv :=
  (rfl)

/-- The identity isomorphism induces the identity isomorphism on fppf sheaves of points. -/
@[simp]
theorem pointsSheafIso_refl (X : Over (Spec (CommRingCat.of R))) :
    pointsSheafIso (Iso.refl X) = Iso.refl (pointsSheaf X) := by
  ext : 1
  exact pointsSheafMap_id X

/-- Inverting an isomorphism of schemes over `Spec R` inverts `pointsSheafIso`. -/
@[simp]
theorem pointsSheafIso_symm {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    pointsSheafIso e.symm = (pointsSheafIso e).symm :=
  (rfl)

/-- Composition of scheme isomorphisms over `Spec R` becomes composition of `pointsSheafIso`. -/
@[simp]
theorem pointsSheafIso_trans {X Y Z : Over (Spec (CommRingCat.of R))} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) :
    pointsSheafIso (e₁ ≪≫ e₂) = pointsSheafIso e₁ ≪≫ pointsSheafIso e₂ := by
  ext : 1
  exact pointsSheafMap_comp e₁.hom e₂.hom

variable (R) in
/-- **The fppf sheaf-of-points functor** from schemes over `Spec R` to fppf sheaves on the affine
site `(CommAlgCat R)ᵒᵖ`.

The functor record is exposed so that `(pointsSheafFunctor R).obj X` and
`(pointsSheafFunctor R).map f` unify directly with `pointsSheaf X` and `pointsSheafMap f`, while
`pointsSheafMap` itself remains opaque. -/
@[expose] noncomputable def pointsSheafFunctor :
    Over (Spec (CommRingCat.of R)) ⥤ Sheaf (fppfTopology R) (Type (u + 1)) where
  obj := pointsSheaf
  map := pointsSheafMap
  map_id := pointsSheafMap_id
  map_comp := pointsSheafMap_comp

/-- On objects, `pointsSheafFunctor` is `pointsSheaf`. -/
theorem pointsSheafFunctor_obj (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctor R).obj X = pointsSheaf X :=
  (rfl)

/-- On morphisms, `pointsSheafFunctor` is `pointsSheafMap`. -/
theorem pointsSheafFunctor_map {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    (pointsSheafFunctor R).map f = pointsSheafMap f :=
  (rfl)

/-- On isomorphisms, `pointsSheafFunctor.mapIso` agrees with `pointsSheafIso`. -/
theorem pointsSheafFunctor_mapIso {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    (pointsSheafFunctor R).mapIso e = pointsSheafIso e :=
  (rfl)

variable (R) in
/-- `pointsSheafFunctor` is naturally isomorphic to subcanonical Yoneda on `Over (Spec R)`
followed by restriction along `algSpec`. -/
noncomputable def pointsSheafFunctorIso :
    pointsSheafFunctor R ≅
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).uliftYoneda.{u + 1} ⋙
        (fppfSheafEquiv R (Type (u + 1))).inverse :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    ext _ ⟨_⟩
    rfl

/-- At each `R`-scheme `X`, `pointsSheafFunctorIso` is the identity sheaf isomorphism. -/
@[simp]
theorem pointsSheafFunctorIso_app (X : Over (Spec (CommRingCat.of R))) :
    dsimp% (pointsSheafFunctorIso R).app X = Iso.refl (pointsSheaf X) :=
  (rfl)

/-- The forward component of `pointsSheafFunctorIso` at `X` is the identity morphism. -/
@[simp]
theorem pointsSheafFunctorIso_hom_app (X : Over (Spec (CommRingCat.of R))) :
    dsimp% (pointsSheafFunctorIso R).hom.app X = 𝟙 (pointsSheaf X) :=
  (rfl)

/-- The inverse component of `pointsSheafFunctorIso` at `X` is the identity morphism. -/
@[simp]
theorem pointsSheafFunctorIso_inv_app (X : Over (Spec (CommRingCat.of R))) :
    dsimp% (pointsSheafFunctorIso R).inv.app X = 𝟙 (pointsSheaf X) :=
  (rfl)

variable (R) in
/-- **The fppf sheaf-of-points functor is fully faithful.** Morphisms between schemes over
`Spec R` are in natural bijection with morphisms between their affine fppf sheaves of points. -/
noncomputable def fullyFaithfulPointsSheafFunctor :
    (pointsSheafFunctor R).FullyFaithful :=
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
noncomputable def homOfPointsSheafHom {X Y : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) : X ⟶ Y :=
  (fullyFaithfulPointsSheafFunctor R).preimage α

/-- `pointsSheafMap` recovers the sheaf morphism from `homOfPointsSheafHom`. -/
@[simp]
theorem pointsSheafMap_homOfPointsSheafHom {X Y : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) :
    pointsSheafMap (homOfPointsSheafHom α) = α :=
  (fullyFaithfulPointsSheafFunctor R).map_preimage α

/-- `homOfPointsSheafHom` is left inverse to `pointsSheafMap`. -/
@[simp]
theorem homOfPointsSheafHom_pointsSheafMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    homOfPointsSheafHom (pointsSheafMap f) = f :=
  (fullyFaithfulPointsSheafFunctor R).preimage_map f

/-- `pointsSheafMap` is injective on `R`-scheme morphisms. -/
theorem pointsSheafMap_injective {X Y : Over (Spec (CommRingCat.of R))} :
    Function.Injective (pointsSheafMap (R := R) (X := X) (Y := Y)) :=
  Function.LeftInverse.injective homOfPointsSheafHom_pointsSheafMap

/-- Two morphisms of `R`-schemes are equal when they induce the same morphism on fppf sheaves of
points. -/
theorem over_hom_ext_of_pointsSheafMap {X Y : Over (Spec (CommRingCat.of R))} {f g : X ⟶ Y}
    (h : pointsSheafMap f = pointsSheafMap g) : f = g :=
  pointsSheafMap_injective h

/-- A morphism `f : X ⟶ Y` over `Spec R` equals `homOfPointsSheafHom α` if and only if
`pointsSheafMap f = α`. -/
theorem eq_homOfPointsSheafHom_iff {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (α : pointsSheaf X ⟶ pointsSheaf Y) :
    f = homOfPointsSheafHom α ↔ pointsSheafMap f = α :=
  ⟨by rintro rfl; exact pointsSheafMap_homOfPointsSheafHom α,
   by rintro rfl; exact (homOfPointsSheafHom_pointsSheafMap f).symm⟩

/-- `homOfPointsSheafHom` sends the identity sheaf morphism to the identity `R`-scheme
morphism. -/
@[simp]
theorem homOfPointsSheafHom_id (X : Over (Spec (CommRingCat.of R))) :
    homOfPointsSheafHom (𝟙 (pointsSheaf X)) = 𝟙 X := by
  rw [← pointsSheafMap_id, homOfPointsSheafHom_pointsSheafMap]

/-- `homOfPointsSheafHom` preserves composition of morphisms of fppf point sheaves. -/
@[simp]
theorem homOfPointsSheafHom_comp {X Y Z : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) (β : pointsSheaf Y ⟶ pointsSheaf Z) :
    homOfPointsSheafHom (α ≫ β) = homOfPointsSheafHom α ≫ homOfPointsSheafHom β := by
  apply over_hom_ext_of_pointsSheafMap
  rw [pointsSheafMap_comp, pointsSheafMap_homOfPointsSheafHom,
    pointsSheafMap_homOfPointsSheafHom, pointsSheafMap_homOfPointsSheafHom]

/-- Composing an affine `A`-valued point of `X` with `homOfPointsSheafHom α` evaluates `α` at
that point. -/
@[reassoc (attr := simp)]
theorem comp_homOfPointsSheafHom {X Y : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) {A : CommAlgCat.{u} R}
    (a : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X) :
    a ≫ homOfPointsSheafHom α = (α.hom.app (op (op A)) (ULift.up a)).down :=
  congrArg (fun β : pointsSheaf X ⟶ pointsSheaf Y ↦
    (β.hom.app (op (op A)) (ULift.up a)).down)
    (pointsSheafMap_homOfPointsSheafHom α)

/-- Morphisms `X ⟶ Y` over `Spec R` are equivalent to morphisms `pointsSheaf X ⟶ pointsSheaf Y`
of fppf sheaves. -/
noncomputable def pointsSheafHomEquiv (X Y : Over (Spec (CommRingCat.of R))) :
    (X ⟶ Y) ≃ (pointsSheaf X ⟶ pointsSheaf Y) :=
  (fullyFaithfulPointsSheafFunctor R).homEquiv

/-- Forward evaluation of `pointsSheafHomEquiv` is `pointsSheafMap`. -/
@[simp]
theorem pointsSheafHomEquiv_apply {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    pointsSheafHomEquiv X Y f = pointsSheafMap f :=
  (rfl)

/-- Inverse evaluation of `pointsSheafHomEquiv` is `homOfPointsSheafHom`. -/
@[simp]
theorem pointsSheafHomEquiv_symm_apply {X Y : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) :
    (pointsSheafHomEquiv X Y).symm α = homOfPointsSheafHom α :=
  (rfl)

/-- An isomorphism of fppf point sheaves descends to an isomorphism of `R`-schemes. -/
instance isIso_homOfPointsSheafHom {X Y : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) [IsIso α] :
    IsIso (homOfPointsSheafHom α) :=
  ⟨⟨homOfPointsSheafHom (inv α),
    by rw [← homOfPointsSheafHom_comp, IsIso.hom_inv_id, homOfPointsSheafHom_id],
    by rw [← homOfPointsSheafHom_comp, IsIso.inv_hom_id, homOfPointsSheafHom_id]⟩⟩

/-- A morphism of `R`-schemes is an isomorphism when its induced map on fppf sheaves of points is
an isomorphism. -/
theorem isIso_of_isIso_pointsSheafMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [IsIso (pointsSheafMap f)] : IsIso f := by
  rw [← homOfPointsSheafHom_pointsSheafMap f]
  infer_instance

/-- **Isomorphism of `R`-schemes from an isomorphism of fppf point sheaves.** -/
noncomputable def isoOfPointsSheafIso {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) : X ≅ Y :=
  (fullyFaithfulPointsSheafFunctor R).preimageIso e

/-- The forward morphism of `isoOfPointsSheafIso e` is `homOfPointsSheafHom e.hom`. -/
@[simp]
theorem isoOfPointsSheafIso_hom {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) :
    (isoOfPointsSheafIso e).hom = homOfPointsSheafHom e.hom :=
  (rfl)

/-- The inverse morphism of `isoOfPointsSheafIso e` is `homOfPointsSheafHom e.inv`. -/
@[simp]
theorem isoOfPointsSheafIso_inv {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) :
    (isoOfPointsSheafIso e).inv = homOfPointsSheafHom e.inv :=
  (rfl)

/-- Applying `pointsSheafIso` to `isoOfPointsSheafIso e` recovers `e`. -/
@[simp]
theorem pointsSheafIso_isoOfPointsSheafIso {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) :
    pointsSheafIso (isoOfPointsSheafIso e) = e := by
  ext : 1
  exact pointsSheafMap_homOfPointsSheafHom e.hom

/-- Applying `isoOfPointsSheafIso` to `pointsSheafIso e` recovers `e`. -/
@[simp]
theorem isoOfPointsSheafIso_pointsSheafIso {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    isoOfPointsSheafIso (pointsSheafIso e) = e := by
  ext : 1
  exact homOfPointsSheafHom_pointsSheafMap e.hom

/-- `isoOfPointsSheafIso` preserves identity isomorphisms. -/
@[simp]
theorem isoOfPointsSheafIso_refl (X : Over (Spec (CommRingCat.of R))) :
    isoOfPointsSheafIso (Iso.refl (pointsSheaf X)) = Iso.refl X := by
  ext : 1
  exact homOfPointsSheafHom_id X

/-- `isoOfPointsSheafIso` commutes with symmetry of isomorphisms. -/
@[simp]
theorem isoOfPointsSheafIso_symm {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) :
    isoOfPointsSheafIso e.symm = (isoOfPointsSheafIso e).symm :=
  (rfl)

/-- `isoOfPointsSheafIso` preserves composition of sheaf isomorphisms. -/
@[simp]
theorem isoOfPointsSheafIso_trans {X Y Z : Over (Spec (CommRingCat.of R))}
    (e₁ : pointsSheaf X ≅ pointsSheaf Y) (e₂ : pointsSheaf Y ≅ pointsSheaf Z) :
    isoOfPointsSheafIso (e₁ ≪≫ e₂) = isoOfPointsSheafIso e₁ ≪≫ isoOfPointsSheafIso e₂ := by
  ext : 1
  exact homOfPointsSheafHom_comp e₁.hom e₂.hom

/-- **Local surjectivity on fppf point sheaves implies surjectivity on underlying schemes.**
If `f : X ⟶ Y` over `Spec R` induces a locally surjective morphism `pointsSheaf X ⟶ pointsSheaf Y`,
then `f.left : X.left ⟶ Y.left` is surjective. -/
theorem surjective_left_of_isLocallySurjective_pointsSheafMap
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Sheaf.IsLocallySurjective (pointsSheafMap f)] :
    Surjective f.left := by
  refine ⟨fun y ↦ ?_⟩
  let φ₀ : CommRingCat.of R ⟶ Y.left.residueField y :=
    Spec.preimage (Y.left.fromSpecResidueField y ≫ Y.hom)
  let _ : Algebra R (Y.left.residueField y) := φ₀.hom.toAlgebra
  have hφ₀ : Spec.map (CommRingCat.ofHom (algebraMap R (Y.left.residueField y))) =
      Y.left.fromSpecResidueField y ≫ Y.hom :=
    Spec.map_preimage _
  let A : CommAlgCat.{u} R := CommAlgCat.of R (Y.left.residueField y)
  let yPt : (algSpec (CommRingCat.of R)).obj (op A) ⟶ Y :=
    Over.homMk (Y.left.fromSpecResidueField y) hφ₀.symm
  let ySection : (pointsSheaf Y).obj.obj (op (op A)) := ULift.up yPt
  let S : Sieve (op A) := Presheaf.imageSieve (pointsSheafMap f).hom ySection
  have hS : S ∈ fppfTopology R (op A) :=
    Presheaf.imageSieve_mem (CA := fun X ↦ X) (fppfTopology R) (pointsSheafMap f).hom
      (U := op (op A)) ySection
  let _ : (algSpec (CommRingCat.of R)).Full :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (algSpec (CommRingCat.of R)).Faithful :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  have : Scheme.fppfPrecoverage.HasIsos := ⟨fun g _ ↦ g.singleton_mem_fppfPrecoverage⟩
  rw [fppfTopology_def, Functor.mem_inducedTopology_iff_of_isCoverDense,
    GrothendieckTopology.mem_over_iff,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨P, ⟨hsurj, -⟩, hPS⟩ := hS
  let z₀ : Spec (Y.left.residueField y) := IsLocalRing.closedPoint (Y.left.residueField y)
  obtain ⟨_, _, hg, z, hgz⟩ := hsurj z₀
  cases hg with
  | @of Z g hg =>
  have hgS := hPS Z g hg
  rw [Sieve.overEquiv_iff] at hgS
  obtain ⟨B, ψ, hB, hψS, hfac⟩ := hgS
  obtain ⟨⟨xPt⟩, hxPt⟩ := hψS
  rw [pointsSheafMap_hom_app_apply] at hxPt
  have hxEq : xPt ≫ f = (algSpec (CommRingCat.of R)).map ψ ≫ yPt :=
    congrArg ULift.down hxPt
  let z' : Z := z
  let g' : Z ⟶ Spec (Y.left.residueField y) := g
  have hgz' : g' z' = z₀ := hgz
  have hcomp :
      (hB.left : Z ⟶ _) ≫ xPt.left ≫ f.left = g' ≫ Y.left.fromSpecResidueField y := by
    have h := congrArg Over.Hom.left (show hB ≫ xPt ≫ f = Over.homMk g _ ≫ yPt by
      rw [hxEq, ← Category.assoc, hfac])
    dsimp [yPt] at h
    exact h
  have hz : ((hB.left : Z ⟶ _) ≫ xPt.left ≫ f.left) z' =
      (g' ≫ Y.left.fromSpecResidueField y) z' :=
    congrArg (fun m : Z ⟶ Y.left ↦ m z') hcomp
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hgz',
    Scheme.fromSpecResidueField_apply] at hz
  exact ⟨xPt.left ((hB.left : Z ⟶ _) z'), hz⟩

/-- Descending a locally surjective morphism of fppf point sheaves yields a surjective morphism on
underlying schemes. -/
instance instSurjectiveHomOfPointsSheafHomLeft
    {X Y : Over (Spec (CommRingCat.of R))} (α : pointsSheaf X ⟶ pointsSheaf Y)
    [Sheaf.IsLocallySurjective α] :
    Surjective (homOfPointsSheafHom α).left := by
  have : Sheaf.IsLocallySurjective (pointsSheafMap (homOfPointsSheafHom α)) := by
    rwa [pointsSheafMap_homOfPointsSheafHom]
  exact surjective_left_of_isLocallySurjective_pointsSheafMap (homOfPointsSheafHom α)

end Functor

end CommAlgCat

end TauCeti
