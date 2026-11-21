/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.Fppf
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Lifting
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.Canonical

/-!
# Full faithfulness and descent for affine fppf points sheaves

For a commutative ring `R`, sending a scheme `X` over `Spec R` to its fppf sheaf of affine-valued
points `CommAlgCat.pointsSheaf X` defines a functor from schemes over `Spec R` to sheaves on the
affine fppf site `(CommAlgCat R)ᵒᵖ`.

Because the fppf topology on schemes over `Spec R` is subcanonical and affine `Spec R`-schemes
form a full, faithful, cover-dense subsite (`CommAlgCat.isCoverDense_algSpec`), this functor is
fully faithful. Consequently, scheme morphisms and isomorphisms over `Spec R` are uniquely
determined by, and descend from, morphisms and isomorphisms of their affine fppf points sheaves.
Equivariance of a scheme morphism under an internal monoid-scheme action is likewise detected on
affine-valued points, and fppf morphisms of schemes induce locally surjective maps of points
sheaves.

## Main declarations

* `TauCeti.CommAlgCat.pointsSheafMap` and `TauCeti.CommAlgCat.pointsSheafFunctor`: the functor
  sending a scheme over `Spec R` to its affine fppf sheaf of points.
* `TauCeti.CommAlgCat.fullyFaithfulPointsSheafFunctor`: the affine fppf points-sheaf functor is
  fully faithful.
* `TauCeti.CommAlgCat.pointsSheafHomEquiv` and `TauCeti.CommAlgCat.pointsSheafIsoEquiv`:
  scheme morphisms and isomorphisms over `Spec R` correspond to morphisms and isomorphisms of
  their affine fppf points sheaves.
* `TauCeti.CommAlgCat.hom_ext_pointsSheaf`: morphisms of schemes over `Spec R` agree when they
  agree on all affine-valued points.
* `TauCeti.CommAlgCat.isLocallySurjective_pointsSheafMap`: an fppf morphism of schemes over
  `Spec R` induces a locally surjective map of affine fppf points sheaves.
* `TauCeti.CommAlgCat.isModHom_iff_pointsSheaf`: equivariance of a scheme morphism over `Spec R`
  is detected on affine-valued points.
* `TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_comp`: equivariance descends along an
  equivariant fppf-locally surjective map of schemes.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.CommAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- Restriction along a morphism of opposite commutative `R`-algebras acts on `pointsSheaf X` by
precomposition with the induced morphism of affine schemes. -/
theorem pointsSheaf_obj_map_apply {X : Over (Spec (CommRingCat.of R))}
    {A B : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} (φ : A ⟶ B)
    (p : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X) :
    (pointsSheaf X).obj.map φ (ULift.up p) =
      ULift.up ((algSpec (CommRingCat.of R)).map φ.unop ≫ p) :=
  (rfl)

/-- The morphism of affine fppf points sheaves induced by a morphism of schemes over `Spec R`. -/
noncomputable def pointsSheafMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    pointsSheaf X ⟶ pointsSheaf Y :=
  ⟨Functor.whiskerRight
    (Functor.whiskerLeft (algSpec (CommRingCat.of R)).op (yoneda.map f))
    uliftFunctor.{u + 1, u}⟩

/-- The functor sending a scheme over `Spec R` to its affine fppf sheaf of points. -/
noncomputable def pointsSheafFunctor (R : Type u) [CommRing R] :
    Over (Spec (CommRingCat.of R)) ⥤ Sheaf (fppfTopology R) (Type (u + 1)) where
  obj := pointsSheaf
  map := pointsSheafMap
  map_id X := by
    ext A ⟨p⟩
    exact congrArg ULift.up (Category.comp_id p)
  map_comp f g := by
    ext A ⟨p⟩
    exact congrArg ULift.up (Category.assoc p f g)

/-- On objects, `pointsSheafFunctor` is `pointsSheaf`. -/
@[simp]
theorem pointsSheafFunctor_obj (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctor R).obj X = pointsSheaf X :=
  (rfl)

/-- `pointsSheafMap` preserves identity morphisms. -/
@[simp]
theorem pointsSheafMap_id (X : Over (Spec (CommRingCat.of R))) :
    pointsSheafMap (𝟙 X) = 𝟙 (pointsSheaf X) :=
  (pointsSheafFunctor R).map_id X

/-- `pointsSheafMap` preserves composition of scheme morphisms. -/
@[simp]
theorem pointsSheafMap_comp {X Y Z : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointsSheafMap (f ≫ g) = pointsSheafMap f ≫ pointsSheafMap g :=
  (pointsSheafFunctor R).map_comp f g

/-- On morphisms, `pointsSheafMap` acts by postcomposition on affine-valued points. -/
theorem pointsSheafMap_hom_app_apply {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (p : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X) :
    (pointsSheafMap f).hom.app A (ULift.up p) = ULift.up (p ≫ f) :=
  (rfl)

/-- `pointsSheafMap` sends scheme isomorphisms to isomorphisms of points sheaves. -/
instance isIso_pointsSheafMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsIso f] :
    IsIso (pointsSheafMap f) :=
  (pointsSheafFunctor R).map_isIso f

/-- `pointsSheafFunctor` agrees naturally with the universe-lifted Yoneda embedding followed by
restriction along relative `Spec`. -/
private noncomputable def pointsSheafFunctorIsoUliftYoneda (R : Type u) [CommRing R] :
    pointsSheafFunctor R ≅
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).uliftYoneda.{u + 1} ⋙
        (algSpec (CommRingCat.of R)).sheafPushforwardContinuous (Type (u + 1))
          (fppfTopology R) (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) :=
  NatIso.ofComponents
    (fun X ↦ (fullyFaithfulSheafToPresheaf (fppfTopology R) (Type (u + 1))).preimageIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
        ext ⟨p⟩
        rfl)))
    (fun _ ↦ by
      ext A ⟨p⟩
      rfl)

/-- **The affine fppf points-sheaf functor is fully faithful.** Morphisms between schemes over
`Spec R` are determined by, and uniquely descend from, morphisms between their fppf sheaves of
affine-valued points. -/
noncomputable def fullyFaithfulPointsSheafFunctor (R : Type u) [CommRing R] :
    (pointsSheafFunctor R).FullyFaithful := by
  let _ : (algSpec (CommRingCat.of R)).Full :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (algSpec (CommRingCat.of R)).Faithful :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  have hpush :
      ((algSpec (CommRingCat.of R)).sheafPushforwardContinuous (Type (u + 1))
        (fppfTopology R) (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  let F := (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).uliftYoneda.{u + 1}
  have hF : F.FullyFaithful :=
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).fullyFaithfulUliftYoneda.{u + 1}
  exact (hF.comp hpush).ofIso (pointsSheafFunctorIsoUliftYoneda R).symm

instance (R : Type u) [CommRing R] : (pointsSheafFunctor R).Full :=
  (fullyFaithfulPointsSheafFunctor R).full

instance (R : Type u) [CommRing R] : (pointsSheafFunctor R).Faithful :=
  (fullyFaithfulPointsSheafFunctor R).faithful

/-- Scheme morphisms over `Spec R` correspond bijectively to morphisms of their affine fppf
points sheaves. -/
noncomputable def pointsSheafHomEquiv {X Y : Over (Spec (CommRingCat.of R))} :
    (X ⟶ Y) ≃ (pointsSheaf X ⟶ pointsSheaf Y) :=
  (fullyFaithfulPointsSheafFunctor R).homEquiv

/-- The forward direction of `pointsSheafHomEquiv` is `pointsSheafMap`. -/
@[simp]
theorem pointsSheafHomEquiv_apply {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    pointsSheafHomEquiv f = pointsSheafMap f :=
  (rfl)

/-- Applying `pointsSheafMap` to the scheme morphism recovered from a morphism of points sheaves
returns that morphism of points sheaves. -/
@[simp]
theorem pointsSheafMap_pointsSheafHomEquiv_symm {X Y : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) :
    pointsSheafMap (pointsSheafHomEquiv.symm α) = α :=
  pointsSheafHomEquiv.apply_symm_apply α

/-- Evaluating the scheme morphism recovered from a morphism of points sheaves on an
affine-valued point recovers that morphism of points sheaves. -/
@[simp]
theorem comp_pointsSheafHomEquiv_symm {X Y : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) (A : CommAlgCat.{u} R)
    (p : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X) :
    p ≫ pointsSheafHomEquiv.symm α = (α.hom.app (op (op A)) (ULift.up p)).down :=
  congrArg (fun β : pointsSheaf X ⟶ pointsSheaf Y ↦
    (β.hom.app (op (op A)) (ULift.up p)).down)
    (pointsSheafHomEquiv.apply_symm_apply α)

/-- Scheme isomorphisms over `Spec R` correspond bijectively to isomorphisms of their affine fppf
points sheaves. -/
noncomputable def pointsSheafIsoEquiv {X Y : Over (Spec (CommRingCat.of R))} :
    (X ≅ Y) ≃ (pointsSheaf X ≅ pointsSheaf Y) :=
  (fullyFaithfulPointsSheafFunctor R).isoEquiv

/-- The forward map of `pointsSheafIsoEquiv e` is `pointsSheafMap e.hom`. -/
@[simp]
theorem pointsSheafIsoEquiv_hom {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    (pointsSheafIsoEquiv e).hom = pointsSheafMap e.hom :=
  (rfl)

/-- The inverse map of `pointsSheafIsoEquiv e` is `pointsSheafMap e.inv`. -/
@[simp]
theorem pointsSheafIsoEquiv_inv {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    (pointsSheafIsoEquiv e).inv = pointsSheafMap e.inv :=
  (rfl)

/-- Applying `pointsSheafMap` to the forward direction of a descended scheme isomorphism recovers
the forward morphism of points sheaves. -/
@[simp]
theorem pointsSheafMap_pointsSheafIsoEquiv_symm_hom {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) :
    pointsSheafMap (pointsSheafIsoEquiv.symm e).hom = e.hom :=
  congrArg Iso.hom (pointsSheafIsoEquiv.apply_symm_apply e)

/-- Applying `pointsSheafMap` to the inverse direction of a descended scheme isomorphism recovers
the inverse morphism of points sheaves. -/
@[simp]
theorem pointsSheafMap_pointsSheafIsoEquiv_symm_inv {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) :
    pointsSheafMap (pointsSheafIsoEquiv.symm e).inv = e.inv :=
  congrArg Iso.inv (pointsSheafIsoEquiv.apply_symm_apply e)

/-- Evaluating the forward direction of the scheme isomorphism recovered from an isomorphism of
points sheaves on an affine-valued point recovers that isomorphism on points. -/
@[simp]
theorem comp_pointsSheafIsoEquiv_symm_hom {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) (A : CommAlgCat.{u} R)
    (p : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X) :
    p ≫ (pointsSheafIsoEquiv.symm e).hom = (e.hom.hom.app (op (op A)) (ULift.up p)).down :=
  congrArg (fun i : pointsSheaf X ≅ pointsSheaf Y ↦
    (i.hom.hom.app (op (op A)) (ULift.up p)).down)
    (pointsSheafIsoEquiv.apply_symm_apply e)

/-- Evaluating the inverse direction of the scheme isomorphism recovered from an isomorphism of
points sheaves on an affine-valued point recovers the inverse isomorphism on points. -/
@[simp]
theorem comp_pointsSheafIsoEquiv_symm_inv {X Y : Over (Spec (CommRingCat.of R))}
    (e : pointsSheaf X ≅ pointsSheaf Y) (A : CommAlgCat.{u} R)
    (q : (algSpec (CommRingCat.of R)).obj (op A) ⟶ Y) :
    q ≫ (pointsSheafIsoEquiv.symm e).inv = (e.inv.hom.app (op (op A)) (ULift.up q)).down :=
  congrArg (fun i : pointsSheaf X ≅ pointsSheaf Y ↦
    (i.inv.hom.app (op (op A)) (ULift.up q)).down)
    (pointsSheafIsoEquiv.apply_symm_apply e)

/-- `pointsSheafMap` is injective on morphisms of schemes over `Spec R`. -/
theorem pointsSheafMap_injective {X Y : Over (Spec (CommRingCat.of R))} {f g : X ⟶ Y}
    (h : pointsSheafMap f = pointsSheafMap g) :
    f = g :=
  pointsSheafHomEquiv.injective h

/-- Two morphisms of schemes over `Spec R` are equal if they induce the same map on all
affine-valued points. -/
theorem hom_ext_pointsSheaf {X Y : Over (Spec (CommRingCat.of R))} {f g : X ⟶ Y}
    (h : ∀ (A : CommAlgCat.{u} R) (p : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X),
      p ≫ f = p ≫ g) :
    f = g := by
  apply pointsSheafMap_injective
  ext A ⟨p⟩
  exact congrArg ULift.up (h A.unop.unop p)

/-- **Fppf morphisms induce locally surjective maps on affine points sheaves.** Every
affine-valued point of the target lifts after a faithfully flat, finitely presented extension of
the value algebra. -/
instance isLocallySurjective_pointsSheafMap
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left] :
    Presheaf.IsLocallySurjective (fppfTopology R) (pointsSheafMap f).hom where
  imageSieve_mem {U} s := by
    obtain ⟨y⟩ := s
    let y' : Spec (CommRingCat.of U.unop) ⟶ Y.left := y.left
    obtain ⟨B, φ, z, hflat, hfp, hz⟩ := f.left.exists_faithfullyFlat_lift y'
    let _ : Algebra R B := (φ.hom.comp (algebraMap R U.unop)).toAlgebra
    let φ' : U.unop ⟶ CommAlgCat.of R B :=
      CommAlgCat.ofHom { φ.hom with commutes' := fun _ ↦ rfl }
    have hbase : z ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      have hscalar : CommRingCat.ofHom (algebraMap R B) =
          CommRingCat.ofHom (algebraMap R U.unop) ≫ φ := rfl
      rw [hscalar, Spec.map_comp, ← Over.w f, ← Category.assoc, hz, Category.assoc]
      exact congrArg (Spec.map φ ≫ ·) (Over.w y)
    refine GrothendieckTopology.superset_covering _ ?_
      (generate_singleton_op_mem_fppfTopology φ' hflat hfp)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨ULift.up (Over.homMk z hbase), ?_⟩
    exact congrArg ULift.up (Over.OverMorphism.ext hz)

/-- Equivariance of a scheme morphism over `Spec R` is detected on all affine-valued points. -/
theorem isModHom_iff_pointsSheaf {G X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G X] [ModObj G Y] (f : X ⟶ Y) :
    IsModHom G f ↔
      ∀ (A : CommAlgCat.{u} R) (g : (algSpec (CommRingCat.of R)).obj (op A) ⟶ G)
        (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X),
        (g • x) ≫ f = g • (x ≫ f) := by
  refine ⟨fun _ A g x ↦ IsModHom.map_smul f g x, fun h ↦ ⟨?_⟩⟩
  apply hom_ext_pointsSheaf
  intro A p
  have hp : p = lift (p ≫ fst G X) (p ≫ snd G X) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [hp, ← Category.assoc, ← Hom.smul_def, h, Hom.smul_def, ← lift_whiskerLeft_assoc]
  rfl

/-- Equivariance descends along an equivariant morphism whose map on affine points sheaves is
fppf locally surjective. -/
theorem isModHom_of_isLocallySurjective_comp {G Z X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G Z] [ModObj G X] [ModObj G Y] (p : Z ⟶ X)
    [Presheaf.IsLocallySurjective (fppfTopology R) (pointsSheafMap p).hom]
    [IsModHom G p] (f : X ⟶ Y) [IsModHom G (p ≫ f)] :
    IsModHom G f := by
  rw [isModHom_iff_pointsSheaf]
  intro A g x
  let x' : (pointsSheaf X).obj.obj (op (op A)) := ULift.up x
  have hcov := Presheaf.imageSieve_mem (fppfTopology R) (pointsSheafMap p).hom x'
  have heq : (ULift.up ((g • x) ≫ f) : (pointsSheaf Y).obj.obj (op (op A))) =
      ULift.up (g • (x ≫ f)) := by
    refine (((isSheaf_iff_isSheaf_of_type _ _).mp (pointsSheaf Y).property).isSeparated _ hcov).ext
      fun B φ hφ ↦ ?_
    obtain ⟨⟨h⟩, hh⟩ := hφ
    have hx : h ≫ p = (algSpec (CommRingCat.of R)).map φ ≫ x := congrArg ULift.down hh
    rw [pointsSheaf_obj_map_apply, pointsSheaf_obj_map_apply, Quiver.Hom.unop_op]
    apply congrArg ULift.up
    rw [← Category.assoc, ModObj.comp_smul, ← hx, ← IsModHom.map_smul p, Category.assoc,
      IsModHom.map_smul (p ≫ f), ← Category.assoc, hx, Category.assoc, ← ModObj.comp_smul]
  exact congrArg ULift.down heq

/-- Equivariance descends along an fppf-locally surjective morphism out of `G` that intertwines
left multiplication with the target actions. -/
theorem isModHom_of_isLocallySurjective_mul_comp {G X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G X] [ModObj G Y] (p : G ⟶ X)
    [Presheaf.IsLocallySurjective (fppfTopology R) (pointsSheafMap p).hom]
    (hp : μ[G] ≫ p = G ◁ p ≫ γ[G,X]) (f : X ⟶ Y)
    (hpf : μ[G] ≫ (p ≫ f) = G ◁ (p ≫ f) ≫ γ[G,Y]) :
    IsModHom G f := by
  let _ : ModObj G G := ModObj.regular G
  have _ : IsModHom G p := ⟨hp⟩
  have _ : IsModHom G (p ≫ f) := ⟨hpf⟩
  exact isModHom_of_isLocallySurjective_comp p f

end TauCeti.CommAlgCat
