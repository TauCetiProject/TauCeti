/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import TauCeti.AlgebraicGeometry.Sites.Fpqc

/-!
# The affine fppf site

For a commutative ring `R`, this file equips `(CommAlgCat R)ᵒᵖ` with the topology induced by
Mathlib's fppf topology on schemes over `Spec R`. This is the category of affine schemes over
`Spec R`, presented contravariantly through their coordinate algebras.

The induced affine topology is subcanonical by full faithfulness of the relative spectrum functor.
Since relative spectra are cover-dense, a scheme over `Spec R` is determined by its fppf sheaf of
affine points: the functor of points is fully faithful, so morphisms between sheaves represented
by schemes, such as homogeneous quotients, are morphisms of schemes. A morphism whose map of
points is fppf locally surjective is surjective, because fppf covers are jointly surjective.

## Main declarations

* `TauCeti.CommAlgCat.fppfTopology`: the fppf topology on opposite commutative `R`-algebras.
* `TauCeti.CommAlgCat.fppfTopology_subcanonical`: affine representable functors are fppf sheaves.
* `TauCeti.CommAlgCat.isContinuous_algSpec`: fppf sheaves on schemes over `Spec R` restrict to
  affine fppf sheaves; in particular every scheme over `Spec R` has an fppf sheaf of points.
* `TauCeti.CommAlgCat.isCoverDense_algSpec`: relative spectra of `R`-algebras are cover-dense
  among schemes over `Spec R`, so a sieve is an affine fppf cover exactly when its image is.
* `TauCeti.CommAlgCat.isDenseSubsite_algSpec`: the affine fppf site is a dense subsite of
  schemes over `Spec R` with the fppf topology.
* `TauCeti.CommAlgCat.fppfSheafEquiv`: equivalence between `A`-valued affine fppf sheaves and
  `A`-valued fppf sheaves on schemes over `Spec R`.
* `TauCeti.CommAlgCat.pointsSheaf`: the fppf sheaf of points of a scheme over `Spec R`.
* `TauCeti.CommAlgCat.pointsSheafFunctor` and `TauCeti.CommAlgCat.fullyFaithfulPointsSheafFunctor`:
  the functor of points to affine fppf sheaves is fully faithful, so morphisms between schemes
  over `Spec R` are morphisms of sheaves of points.
* `TauCeti.CommAlgCat.isLocallySurjective_pointsSheafFunctor_map`: fppf morphisms over
  `Spec R` induce locally surjective maps on affine fppf sheaves of points.
* `TauCeti.CommAlgCat.surjective_of_isLocallySurjective_pointsSheafFunctor_map`: a morphism
  inducing a locally surjective map of fppf sheaves of points is surjective.
* `TauCeti.CommAlgCat.generate_singleton_op_mem_fppfTopology`: a faithfully flat, finitely
  presented algebra map is an affine fppf cover.
* `AlgebraicGeometry.algSpec_obj_left`,
  `AlgebraicGeometry.eqToHom_algSpec_obj_left_comp_Spec_map`: the underlying scheme of
  `(algSpec R).obj X` is `Spec X.unop`, compatibly with the structure morphism to `Spec R`.
* `TauCeti.CommAlgCat.exists_over_comp_left_eq_of_mem_fppfTopology`: scheme points lift along an
  affine fppf covering sieve to a scheme morphism factoring in `Over (Spec R)` through the sieve.
* `AlgHom.exists_faithfullyFlat_lift`: points lift along a faithfully flat, finitely presented
  algebra map after a faithfully flat, finitely presented extension of the value algebra.

## References

* P. T. Johnstone, *Sketches of an Elephant*, C2.2, the comparison lemma for dense subsites.
* J. S. Milne, *Algebraic Groups* (2017), §5, functors of points and fppf sheaves.
* [The Stacks Project, Tag 01JF](https://stacks.math.columbia.edu/tag/01JF), schemes as functors
  on rings.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace TauCeti

universe u

namespace CommAlgCat

/-- The fppf topology on affine schemes over `Spec R`, expressed on the equivalent category
`(CommAlgCat R)ᵒᵖ`.

It is the topology induced along the relative spectrum functor from the fppf topology on schemes
over `Spec R`. -/
noncomputable def fppfTopology (R : Type u) [CommRing R] :
    GrothendieckTopology (CommAlgCat.{u} R)ᵒᵖ :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).inducedTopology
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))

/-- The affine fppf topology is induced from the fppf topology on schemes over `Spec R`. -/
theorem fppfTopology_def (R : Type u) [CommRing R] :
    fppfTopology R =
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).inducedTopology
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) :=
  by
    unfold fppfTopology
    rfl

/-- **The affine fppf topology is subcanonical.** Every presheaf represented by an affine scheme
over `Spec R` is an fppf sheaf. -/
noncomputable instance fppfTopology_subcanonical (R : Type u) [CommRing R] :
    (fppfTopology R).Subcanonical := by
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Full :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Faithful :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  rw [fppfTopology_def]
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (AlgebraicGeometry.algSpec (CommRingCat.of R)) _
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))

/-- The relative spectrum functor is continuous for the affine fppf topology: restricting an fppf
sheaf on schemes over `Spec R` to affine schemes gives an affine fppf sheaf. -/
instance isContinuous_algSpec (R : Type u) [CommRing R] :
    (AlgebraicGeometry.algSpec (CommRingCat.of R)).IsContinuous (fppfTopology R)
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) := by
  rw [fppfTopology_def]
  infer_instance

/-- Every scheme over `Spec R` is covered by affine opens, and an affine open, with the
`R`-algebra structure induced by its structure morphism, is the relative spectrum of an
`R`-algebra. So relative spectra are cover-dense for the fppf topology over `Spec R`. -/
instance isCoverDense_algSpec (R : Type u) [CommRing R] :
    (algSpec (CommRingCat.of R)).IsCoverDense
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) where
  is_cover U := by
    rw [GrothendieckTopology.mem_over_iff]
    let 𝒰 := U.left.affineOpenCover
    refine GrothendieckTopology.superset_covering _ ?_
      (Precoverage.generate_mem_toGrothendieck
        (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ 𝒰.openCover.mem₀))
    rw [Sieve.generate_le_iff]; rintro _ _ ⟨i⟩; rw [Sieve.overEquiv_iff]
    let φ : CommRingCat.of R ⟶ 𝒰.X i := Spec.preimage (𝒰.f i ≫ U.hom)
    let _ : Algebra R (𝒰.X i) := φ.hom.toAlgebra
    -- The structure morphism of the relative spectrum is `Spec.map` of the algebra map, which
    -- for the algebra structure induced by `φ` is `φ` itself.
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i))) = 𝒰.f i ≫ U.hom :=
      Spec.map_preimage _
    exact ⟨⟨Opposite.op (CommAlgCat.of R (𝒰.X i)),
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hφ), Over.homMk (𝒰.f i) hφ.symm,
        by ext; exact Category.id_comp _⟩⟩

/-- Relative spectra of commutative `R`-algebras form a dense subsite of schemes over `Spec R`
for the fppf topology. -/
instance isDenseSubsite_algSpec (R : Type u) [CommRing R] :
    (algSpec (CommRingCat.of R)).IsDenseSubsite (fppfTopology R)
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) := by
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  rw [fppfTopology_def]; infer_instance

section

variable (R : Type u) [CommRing R] (A : Type*) [Category* A]
  [((algSpec (CommRingCat.of R)).sheafPushforwardContinuous A
    (fppfTopology R) (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).IsEquivalence]

/-- **Comparison lemma for the affine fppf site.** Sheaves valued in `A` on the affine fppf site
`(CommAlgCat R)ᵒᵖ` are equivalent to `A`-valued fppf sheaves on all schemes over `Spec R`
whenever pushforward along `algSpec` is an equivalence (for instance when `A` has limits of shape
`StructuredArrow X (algSpec (CommRingCat.of R)).op` for all `X`). -/
noncomputable def fppfSheafEquiv :
    Sheaf (fppfTopology R) A ≌
      Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) A :=
  Functor.IsDenseSubsite.sheafEquiv (fppfTopology R)
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (algSpec (CommRingCat.of R)) A

/-- The inverse of `fppfSheafEquiv` restricts an fppf sheaf on schemes over `Spec R` to affine
`R`-schemes along `algSpec`. -/
@[simp] theorem fppfSheafEquiv_inverse :
    (fppfSheafEquiv R A).inverse =
      (algSpec (CommRingCat.of R)).sheafPushforwardContinuous A
        (fppfTopology R) (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) := (rfl)

/-- The underlying presheaf of a sheaf restricted along `(fppfSheafEquiv R A).inverse` is
precomposition with `(algSpec (CommRingCat.of R)).op`. -/
theorem fppfSheafEquiv_inverse_obj_obj
    (F : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) A) :
    ((fppfSheafEquiv R A).inverse.obj F).obj = (algSpec (CommRingCat.of R)).op ⋙ F.obj := by
  rw [fppfSheafEquiv_inverse]; rfl

/-- On morphisms of affine `R`-schemes, the underlying presheaf of a sheaf restricted along
`(fppfSheafEquiv R A).inverse` applies `F.obj.map` to the image under `(algSpec _).op`. -/
theorem fppfSheafEquiv_inverse_obj_obj_map
    (F : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) A)
    {U V : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} (φ : U ⟶ V) :
    ((fppfSheafEquiv R A).inverse.obj F).obj.map φ =
      eqToHom (Functor.congr_obj (fppfSheafEquiv_inverse_obj_obj R A F) U) ≫
        F.obj.map ((algSpec (CommRingCat.of R)).map φ.unop).op ≫
        eqToHom (Functor.congr_obj (fppfSheafEquiv_inverse_obj_obj R A F) V).symm :=
  Functor.congr_hom (fppfSheafEquiv_inverse_obj_obj R A F) φ

/-- On morphisms, `(fppfSheafEquiv R A).inverse` restricts the underlying natural transformation by
whiskering with `(algSpec (CommRingCat.of R)).op`. -/
theorem fppfSheafEquiv_inverse_map_hom
    {F G : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) A} (f : F ⟶ G) :
    ((fppfSheafEquiv R A).inverse.map f).hom =
      eqToHom (fppfSheafEquiv_inverse_obj_obj R A F) ≫
        Functor.whiskerLeft (algSpec (CommRingCat.of R)).op f.hom ≫
        eqToHom (fppfSheafEquiv_inverse_obj_obj R A G).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Evaluating a restricted sheaf morphism `((fppfSheafEquiv R A).inverse.map f).hom` at an affine
`R`-scheme `U` agrees with `f.hom.app` at `(algSpec (CommRingCat.of R)).obj U.unop`. -/
theorem fppfSheafEquiv_inverse_map_hom_app
    {F G : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) A} (f : F ⟶ G)
    (U : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    ((fppfSheafEquiv R A).inverse.map f).hom.app U =
      eqToHom (Functor.congr_obj (fppfSheafEquiv_inverse_obj_obj R A F) U) ≫
        f.hom.app (Opposite.op ((algSpec (CommRingCat.of R)).obj U.unop)) ≫
        eqToHom (Functor.congr_obj (fppfSheafEquiv_inverse_obj_obj R A G) U).symm := by
  simp only [fppfSheafEquiv_inverse_map_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    eqToHom_app, Functor.comp_obj, Functor.op_obj]

end

/-- **A faithfully flat, finitely presented algebra map is an fppf cover.** If `φ : A ⟶ B` is
faithfully flat and of finite presentation, then the sieve generated by the corresponding
morphism `Spec B ⟶ Spec A` covers `Spec A` in the affine fppf topology. -/
theorem generate_singleton_op_mem_fppfTopology {R : Type u} [CommRing R]
    {A B : CommAlgCat.{u} R} (φ : A ⟶ B) (hflat : φ.hom.toRingHom.FaithfullyFlat)
    (hfp : φ.hom.toRingHom.FinitePresentation) :
    Sieve.generate (Presieve.singleton φ.op) ∈ fppfTopology R (Opposite.op A) := by
  let ψ := ((AlgebraicGeometry.algSpec (CommRingCat.of R)).map φ.op).left
  have hψ : Flat ψ ∧ Surjective ψ := (flat_and_surjective_SpecMap_iff _).2 hflat
  have : Flat ψ := hψ.1
  have : Surjective ψ := hψ.2
  have : LocallyOfFinitePresentation ψ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hfp
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Full :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Faithful :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  rw [fppfTopology_def, Functor.mem_inducedTopology_iff_of_isCoverDense,
    ← Presieve.ofArrows_pUnit.{0}]
  -- `Sieve.ofArrows` is by definition the sieve generated by the presieve of arrows.
  change Sieve.functorPushforward _ (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Presieve.ofArrows_pUnit]
  exact ψ.singleton_mem_fppfPrecoverage

/-- The underlying scheme of `(algSpec R).obj X` is `Spec X.unop`. -/
@[simp] theorem _root_.AlgebraicGeometry.algSpec_obj_left {R : CommRingCat.{u}}
    (X : (CommAlgCat.{u} R)ᵒᵖ) :
    ((algSpec R).obj X).left = Spec (CommRingCat.of X.unop) := (rfl)

/-- Composing `eqToHom (algSpec_obj_left (op A))` with the structure map `Spec A ⟶ Spec R` gives
`((algSpec R).obj (op A)).hom`. -/
@[reassoc (attr := simp)] theorem _root_.AlgebraicGeometry.eqToHom_algSpec_obj_left_comp_Spec_map
    {R : CommRingCat.{u}} (A : CommAlgCat.{u} R) :
    eqToHom (algSpec_obj_left (R := R) (Opposite.op A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      ((algSpec R).obj (Opposite.op A)).hom :=
  (congrArg (· ≫ _) (eqToHom_refl (Spec (CommRingCat.of A)) _)).trans (Category.id_comp _)

/-- **Scheme points lift along affine fppf covering sieves.** Given `S ∈ fppfTopology R (op A)` and
a point `z₀ : Spec A`, there exist an `R`-scheme `(Z, hZ)`, a point `z : Z`, a morphism
`g : Z ⟶ Spec A` sending `z` to `z₀`, an arrow `ψ : B ⟶ op A` in `S`, and an `Over (Spec R)`
morphism `hB : Over.mk hZ ⟶ (algSpec R).obj B` factoring `g` through `(algSpec R).map ψ`. -/
theorem exists_over_comp_left_eq_of_mem_fppfTopology {R : Type u} [CommRing R]
    {A : CommAlgCat.{u} R} {S : Sieve (Opposite.op A)}
    (hS : S ∈ fppfTopology R (Opposite.op A)) (z₀ : Spec (CommRingCat.of A)) :
    ∃ (Z : Scheme.{u}) (hZ : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
      (g : Z ⟶ Spec (CommRingCat.of A)) (B : (CommAlgCat.{u} R)ᵒᵖ) (ψ : B ⟶ Opposite.op A)
      (hB : Over.mk hZ ⟶ (algSpec (CommRingCat.of R)).obj B),
      g z = z₀ ∧ S ψ ∧
        (hB ≫ (algSpec (CommRingCat.of R)).map ψ).left ≫
          eqToHom (algSpec_obj_left (R := CommRingCat.of R) (Opposite.op A)) = g := by
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  have : Scheme.fppfPrecoverage.HasIsos := ⟨fun g _ ↦ g.singleton_mem_fppfPrecoverage⟩
  rw [fppfTopology_def, Functor.mem_inducedTopology_iff_of_isCoverDense,
    GrothendieckTopology.mem_over_iff,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨P, ⟨hsurj, -⟩, hPS⟩ := hS
  rw [Scheme.jointlySurjectivePrecoverage,
    Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hsurj
  have hleftA := algSpec_obj_left (R := CommRingCat.of R) (Opposite.op A)
  obtain ⟨Z, g, hgP, hz⟩ := hsurj ((Scheme.forget_obj _).symm ▸ eqToHom hleftA.symm z₀)
  simp only [Scheme.forget_obj, Scheme.forget_map, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    Set.mem_range] at hz
  obtain ⟨z, hgz⟩ := hz
  obtain ⟨B, ψ, hB, hψS, hfac⟩ := (Sieve.overEquiv_iff _ _).mp (hPS Z g hgP)
  refine ⟨Z, g ≫ ((algSpec (CommRingCat.of R)).obj (Opposite.op A)).hom, z,
    g ≫ eqToHom hleftA, B, ψ, hB, ?_, hψS, ?_⟩
  · rw [Scheme.Hom.comp_apply, hgz, ← Scheme.Hom.comp_apply, eqToHom_trans, eqToHom_refl]; rfl
  · rw [← congrArg Over.Hom.left hfac]; rfl

variable (R : Type u) [CommRing R]

/-- **The functor of points on the affine fppf site.** A scheme `X` over `Spec R` is sent to its
fppf sheaf of points `pointsSheaf X`, and a morphism over `Spec R` acts by postcomposition. It is
the Yoneda embedding into fppf sheaves on schemes over `Spec R`, followed by restriction to
affine schemes.

The body is exposed so that the points of `X` can be computed as morphisms into `X`. -/
@[expose] noncomputable def pointsSheafFunctor :
    Over (Spec (CommRingCat.of R)) ⥤ Sheaf (fppfTopology R) (Type (u + 1)) :=
  GrothendieckTopology.uliftYoneda.{u + 1} (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) ⋙
    (algSpec (CommRingCat.of R)).sheafPushforwardContinuous (Type (u + 1)) (fppfTopology R)
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))

variable {R}

/-- **The fppf sheaf of points of a scheme over `Spec R`.** An affine scheme `Spec A` over
`Spec R` is sent to the morphisms `Spec A ⟶ X` over `Spec R`. The values are lifted to
`Type (u + 1)`, the universe of fppf quotient sheaves of affine groups, so that the two can be
compared. It is the value of `pointsSheafFunctor` at `X`.

It is an abbreviation, so that morphisms into the points sheaf can be written as natural maps
into the underlying functor of points. -/
noncomputable abbrev pointsSheaf (X : Over (Spec (CommRingCat.of R))) :
    Sheaf (fppfTopology R) (Type (u + 1)) :=
  (pointsSheafFunctor R).obj X

/-- The points of a scheme `X` over `Spec R` with values in `A` are its morphisms from `Spec A`
over `Spec R`. -/
theorem pointsSheaf_obj (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheaf X).obj =
      ((algSpec (CommRingCat.of R)).op ⋙ yoneda.obj X) ⋙ uliftFunctor.{u + 1, u} := (rfl)

/-- Restricting the subcanonical `uliftYoneda` sheaf of an `R`-scheme along `algSpec` gives
`pointsSheaf`. -/
@[simp] theorem sheafPushforwardContinuous_algSpec_obj_uliftYoneda {R : Type u} [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) :
    (Functor.sheafPushforwardContinuous (C := (CommAlgCat.{u} R)ᵒᵖ)
        (algSpec (CommRingCat.of R)) (Type (u + 1))
        (fppfTopology R) (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).obj
      ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).uliftYoneda.{u + 1}.obj X) =
      pointsSheaf X := (rfl)

/-- Restricting the subcanonical `uliftYoneda` sheaf of an `R`-scheme along
`(fppfSheafEquiv R (Type (u + 1))).inverse` gives `pointsSheaf`. -/
theorem fppfSheafEquiv_inverse_obj_uliftYoneda {R : Type u} [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) :
    (fppfSheafEquiv R (Type (u + 1))).inverse.obj
        ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).uliftYoneda.{u + 1}.obj X) =
      pointsSheaf X := by
  rw [fppfSheafEquiv_inverse, sheafPushforwardContinuous_algSpec_obj_uliftYoneda]

/-- Changing the value algebra along `φ` restricts a point along the corresponding morphism of
affine schemes. -/
@[simp]
theorem pointsSheaf_obj_map (X : Over (Spec (CommRingCat.of R)))
    {A B : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} (φ : A ⟶ B) (x : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X) :
    (pointsSheaf X).obj.map φ (ULift.up x) =
      ULift.up ((algSpec (CommRingCat.of R)).map φ.unop ≫ x) :=
  (rfl)

/-- A morphism of schemes over `Spec R` acts on points by postcomposition. -/
@[simp]
theorem pointsSheafFunctor_map_hom_app {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (x : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X) :
    ((pointsSheafFunctor R).map f).hom.app A (ULift.up x) = ULift.up (x ≫ f) :=
  (rfl)

/-- On morphisms, `pointsSheafFunctor` restricts the subcanonical `uliftYoneda` morphism along
`(fppfSheafEquiv R (Type (u + 1))).inverse`. -/
theorem pointsSheafFunctor_map {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    (pointsSheafFunctor R).map f =
      eqToHom (fppfSheafEquiv_inverse_obj_uliftYoneda X).symm ≫
        (fppfSheafEquiv R (Type (u + 1))).inverse.map
          ((GrothendieckTopology.uliftYoneda.{u + 1}
            (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map f) ≫
        eqToHom (fppfSheafEquiv_inverse_obj_uliftYoneda Y) :=
  Functor.congr_hom (fppfSheafEquiv_inverse R (Type (u + 1))).symm
    ((GrothendieckTopology.uliftYoneda.{u + 1}
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map f)

variable (R)

/-- **Schemes are determined by their fppf sheaves of affine points.** The functor of points
from schemes over `Spec R` to fppf sheaves on affine `R`-schemes is fully faithful: every
morphism of fppf sheaves of points comes from a unique morphism of schemes over `Spec R`. -/
noncomputable def fullyFaithfulPointsSheafFunctor : (pointsSheafFunctor R).FullyFaithful :=
  (GrothendieckTopology.fullyFaithfulUliftYoneda _).comp (Functor.FullyFaithful.ofFullyFaithful _)

instance : (pointsSheafFunctor R).Full := (fullyFaithfulPointsSheafFunctor R).full

instance : (pointsSheafFunctor R).Faithful := (fullyFaithfulPointsSheafFunctor R).faithful

variable {R} in
/-- **Fppf morphisms induce locally surjective maps on affine points sheaves.** Every
affine-valued point of the target lifts after a faithfully flat, finitely presented extension of
the value algebra. -/
instance isLocallySurjective_pointsSheafFunctor_map
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left] :
    Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map f).hom := by
  have hcov : Sieve.ofArrows (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ f) ∈
      Scheme.fppfTopology.over (Spec (CommRingCat.of R)) Y := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [Presieve.ofArrows_pUnit]
    exact f.left.singleton_mem_fppfPrecoverage
  let c : Limits.Cofan (fun _ : PUnit.{1} ↦ uliftYoneda.{u + 1}.obj X) :=
    Limits.Cofan.mk (uliftYoneda.{u + 1}.obj X) (fun _ ↦ 𝟙 _)
  let hc : Limits.IsColimit c :=
    Limits.Cofan.IsColimit.mk c (fun s ↦ s.inj PUnit.unit)
      (fun _ _ ↦ Category.id_comp _) (fun _ _ h ↦ by simpa [c] using h PUnit.unit)
  have hloc : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (uliftYoneda.{u + 1}.map f) :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (fun _ : PUnit.{1} ↦ f) hc).mp hcov
  have : Sheaf.IsLocallySurjective ((GrothendieckTopology.uliftYoneda.{u + 1}
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map f) :=
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).1 hloc
  have hepi : Epi ((GrothendieckTopology.uliftYoneda.{u + 1}
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map f) :=
    Sheaf.epi_of_isLocallySurjective _
  have : Epi ((fppfSheafEquiv R (Type (u + 1))).inverse.map
      ((GrothendieckTopology.uliftYoneda.{u + 1}
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map f)) :=
    (fppfSheafEquiv R (Type (u + 1))).inverse.map_epi _
  have hepi' : Epi ((pointsSheafFunctor R).map f) := by
    rw [pointsSheafFunctor_map]
    infer_instance
  exact (Sheaf.isLocallySurjective_iff_epi ((pointsSheafFunctor R).map f)).mpr hepi'

variable {R} in
/-- **Fppf morphisms induce locally surjective maps on affine points sheaves (sheaf form).** -/
instance isLocallySurjective_sheaf_pointsSheafFunctor_map
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left] :
    Sheaf.IsLocallySurjective ((pointsSheafFunctor R).map f) :=
  (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).2
    (isLocallySurjective_pointsSheafFunctor_map f)

variable {R} in
/-- **Locally surjective maps of points come from surjective morphisms.** If a morphism of
schemes over `Spec R` induces an fppf locally surjective map of sheaves of points, then it is
surjective. -/
theorem surjective_of_isLocallySurjective_pointsSheafFunctor_map
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Sheaf.IsLocallySurjective ((pointsSheafFunctor R).map f)] : Surjective f.left := by
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Full :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Faithful :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  refine ⟨fun y ↦ ?_⟩
  -- The point `y` is the image of the closed point of its residue field `κ(y)`, so it suffices
  -- to lift the `κ(y)`-valued point of `Y` given by `Spec κ(y) ⟶ Y` to `X` after an fppf
  -- extension of `κ(y)`. First make `κ(y)` an `R`-algebra through the structure morphism of `Y`.
  let p := Y.left.fromSpecResidueField y
  let φ : CommRingCat.of R ⟶ Y.left.residueField y := Spec.preimage (p ≫ Y.hom)
  let _ : Algebra R (Y.left.residueField y) := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R (Y.left.residueField y))) = p ≫ Y.hom :=
    Spec.map_preimage _
  let s : (pointsSheaf Y).obj.obj (op (op (CommAlgCat.of R (Y.left.residueField y)))) :=
    ULift.up (Over.homMk p hφ.symm)
  -- The point `s` lifts to `X` on an fppf cover of the residue field; take any member of the
  -- cover through some point.
  have hs := (GrothendieckTopology.mem_over_iff _ _).mp
    ((Functor.mem_inducedTopology_iff_of_isCoverDense (algSpec (CommRingCat.of R))
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) _).mp
        (Presheaf.imageSieve_mem (fppfTopology R) ((pointsSheafFunctor R).map f).hom s))
  obtain ⟨Z, g, hg, z, -⟩ := Scheme.exists_mem_range_of_mem_fppfTopology hs
    (IsLocalRing.closedPoint (Y.left.residueField y))
  rw [Sieve.overEquiv_iff] at hg
  obtain ⟨B, ψ, h, ⟨⟨t⟩, ht⟩, -⟩ := hg
  rw [pointsSheafFunctor_map_hom_app, pointsSheaf_obj_map] at ht
  have ht' : t ≫ f = (algSpec (CommRingCat.of R)).map ψ ≫ Over.homMk p hφ.symm :=
    congrArg ULift.down ht
  refine ⟨t.left (h.left z), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ht', Over.comp_left, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

end CommAlgCat

end TauCeti

namespace AlgHom

open TauCeti

universe u

/-- **Points lift fppf locally along a faithfully flat, finitely presented algebra map.** If
`f : B →ₐ[R] K` is faithfully flat and of finite presentation, then every `A`-valued point `y` of
`Spec B` lifts to a point of `Spec K` after the faithfully flat, finitely presented base change
`A ⟶ A ⊗[B] K`. -/
theorem exists_faithfullyFlat_lift {R B K : Type u} [CommRing R] [CommRing B] [CommRing K]
    [Algebra R B] [Algebra R K] (f : B →ₐ[R] K) (hflat : f.toRingHom.FaithfullyFlat)
    (hfp : f.toRingHom.FinitePresentation) {A : CommAlgCat.{u} R} (y : B →ₐ[R] A) :
    ∃ (A' : CommAlgCat.{u} R) (φ : A ⟶ A') (z : K →ₐ[R] A'),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.toRingHom.FinitePresentation ∧
        z.comp f = φ.hom.comp y := by
  let _ : Algebra B A := y.toRingHom.toAlgebra
  let _ : Algebra B K := f.toRingHom.toAlgebra
  have : Module.FaithfullyFlat B K := hflat
  have : Algebra.FinitePresentation B K := hfp
  let _ : Algebra R (A ⊗[B] K) :=
    ((algebraMap A (A ⊗[B] K)).comp (algebraMap R A)).toAlgebra
  -- The pushout square `B ⟶ A ⟶ A ⊗[B] K ⟵ K ⟵ B`, evaluated at `b`.
  have hsq (b : B) : (1 : A) ⊗ₜ[B] f b = y b ⊗ₜ[B] (1 : K) :=
    (RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := B) (A := A) (B := K)) b).symm
  let φ : A →ₐ[R] A ⊗[B] K :=
    { Algebra.TensorProduct.includeLeftRingHom with commutes' := fun _ ↦ rfl }
  let z : K →ₐ[R] A ⊗[B] K :=
    { Algebra.TensorProduct.includeRight.toRingHom with
      commutes' := fun r ↦ by
        -- Unfold `includeRight` and the `R`-algebra structure on `A ⊗[B] K`, which was defined
        -- through `includeLeft`, to their values on pure tensors.
        change (1 : A) ⊗ₜ[B] algebraMap R K r = algebraMap R A r ⊗ₜ[B] (1 : K)
        rw [← f.commutes r, hsq, AlgHom.commutes] }
  refine ⟨CommAlgCat.of R (A ⊗[B] K), CommAlgCat.ofHom φ, z, ?_, ?_, ?_⟩
  · exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  · exact RingHom.finitePresentation_algebraMap.2 inferInstance
  · exact AlgHom.ext hsq

end AlgHom
