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
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.FiniteStability

/-!
# The affine fppf site

For a commutative ring `R`, this file equips `(CommAlgCat R)ᵒᵖ` with the topology induced by
Mathlib's fppf topology on schemes over `Spec R`. This is the category of affine schemes over
`Spec R`, presented contravariantly through their coordinate algebras.

The induced affine topology is subcanonical by full faithfulness of the relative spectrum functor.
Because affine schemes over `Spec R` are cover-dense for the fppf topology, restricting the
fppf sheaf of points of a scheme over `Spec R` to affine `R`-schemes defines a fully faithful
functor `pointsSheafFunctor`. Morphisms over `Spec R` whose induced map on affine fppf points is
locally surjective are epimorphisms in `Over (Spec R)` and surjective on underlying schemes; the
converse fails for nilpotent thickenings such as `Spec k ⟶ Spec (k[ε]/(ε²))`.

## Main declarations

* `TauCeti.CommAlgCat.fppfTopology`: the fppf topology on opposite commutative `R`-algebras.
* `TauCeti.CommAlgCat.fppfTopology_subcanonical`: affine representable functors are fppf sheaves.
* `TauCeti.CommAlgCat.isContinuous_algSpec`: fppf sheaves on schemes over `Spec R` restrict to
  affine fppf sheaves; in particular every scheme over `Spec R` has an fppf sheaf of points.
* `TauCeti.CommAlgCat.isCoverDense_algSpec`: relative spectra of `R`-algebras are cover-dense
  among schemes over `Spec R`, so a sieve is an affine fppf cover exactly when its image is.
* `TauCeti.CommAlgCat.pointsSheaf`: the fppf sheaf of points of a scheme over `Spec R`, with
  action on morphisms `TauCeti.CommAlgCat.pointsSheafMap`.
* `TauCeti.CommAlgCat.pointsSheafFunctor`: the fully faithful functor sending a scheme over
  `Spec R` to its fppf sheaf of affine points, with hom and iso equivalences
  `TauCeti.CommAlgCat.pointsSheafHomEquiv` and `TauCeti.CommAlgCat.pointsSheafIsoEquiv`.
* `TauCeti.CommAlgCat.epi_of_isLocallySurjective_pointsSheafMap` and
  `TauCeti.CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap`: fppf local
  surjectivity on affine points implies epimorphism in `Over (Spec R)` and topological surjectivity
  on underlying schemes.
* `TauCeti.CommAlgCat.generate_singleton_op_mem_fppfTopology`: a faithfully flat, finitely
  presented algebra map is an affine fppf cover.
* `AlgHom.exists_faithfullyFlat_lift`: points lift along a faithfully flat, finitely presented
  algebra map after a faithfully flat, finitely presented extension of the value algebra.
-/

public section

open CategoryTheory AlgebraicGeometry
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
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    rw [Sieve.overEquiv_iff]
    let φ : CommRingCat.of R ⟶ 𝒰.X i := Spec.preimage (𝒰.f i ≫ U.hom)
    let _ : Algebra R (𝒰.X i) := φ.hom.toAlgebra
    -- The structure morphism of the relative spectrum is `Spec.map` of the algebra map, which
    -- for the algebra structure induced by `φ` is `φ` itself.
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i))) = 𝒰.f i ≫ U.hom :=
      Spec.map_preimage _
    exact ⟨⟨Opposite.op (CommAlgCat.of R (𝒰.X i)),
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hφ), Over.homMk (𝒰.f i) hφ.symm,
        by ext; exact Category.id_comp _⟩⟩

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

/-- **The fppf sheaf of points of a scheme over `Spec R`.** An affine scheme `Spec A` over
`Spec R` is sent to the morphisms `Spec A ⟶ X` over `Spec R`. The values are lifted to
`Type (u + 1)`, the universe of fppf quotient sheaves of affine groups, so that the two can be
compared.

The body is exposed so that morphisms into the points sheaf can be written as natural maps into
the underlying functor of points. -/
@[expose] noncomputable def pointsSheaf {R : Type u} [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) :
    Sheaf (fppfTopology R) (Type (u + 1)) :=
  ⟨((algSpec (CommRingCat.of R)).op ⋙ yoneda.obj X) ⋙ uliftFunctor.{u + 1, u},
    (isSheaf_iff_isSheaf_of_type _ _).mpr <| Presieve.isSheaf_comp_uliftFunctor _ <|
      (isSheaf_iff_isSheaf_of_type _ _).mp <| (algSpec (CommRingCat.of R)).op_comp_isSheaf _ _
        ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).yoneda.obj X)⟩

/-- The points of a scheme `X` over `Spec R` with values in `A` are its morphisms from `Spec A`
over `Spec R`. -/
theorem pointsSheaf_obj {R : Type u} [CommRing R] (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheaf X).obj =
      ((algSpec (CommRingCat.of R)).op ⋙ yoneda.obj X) ⋙ uliftFunctor.{u + 1, u} :=
  (rfl)

/-- **Action of a scheme morphism over `Spec R` on fppf sheaves of affine points.** Postcomposing
affine points with `f : X ⟶ Y` defines a morphism `pointsSheaf X ⟶ pointsSheaf Y`. -/
@[expose] noncomputable def pointsSheafMap {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    pointsSheaf X ⟶ pointsSheaf Y :=
  ⟨Functor.whiskerLeft (algSpec (CommRingCat.of R)).op
    (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u})⟩

-- Deliberately not `@[simp]`: `simpNF` unfolds the presheaf evaluation on the left-hand side.
/-- `pointsSheafMap f` postcomposes an `A`-point with `f`. -/
theorem pointsSheafMap_hom_app_apply {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (p : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X) :
    (pointsSheafMap f).hom.app A (ULift.up p) = ULift.up (p ≫ f) :=
  (rfl)

/-- `pointsSheafMap` sends the identity morphism to the identity sheaf morphism. -/
@[simp]
theorem pointsSheafMap_id {R : Type u} [CommRing R] (X : Over (Spec (CommRingCat.of R))) :
    pointsSheafMap (𝟙 X) = 𝟙 (pointsSheaf X) := by
  ext _ _
  rfl

/-- `pointsSheafMap` preserves composition of morphisms over `Spec R`. -/
@[simp, reassoc]
theorem pointsSheafMap_comp {R : Type u} [CommRing R]
    {X Y Z : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointsSheafMap (f ≫ g) = pointsSheafMap f ≫ pointsSheafMap g := by
  ext _ _
  rfl

/-- **The functor of fppf points of schemes over `Spec R`.** A scheme `X` over `Spec R` is sent
to its fppf sheaf of affine `R`-points `pointsSheaf X`, and a morphism `f : X ⟶ Y` over `Spec R`
is sent to `pointsSheafMap f`. -/
@[expose] noncomputable def pointsSheafFunctor (R : Type u) [CommRing R] :
    Over (Spec (CommRingCat.of R)) ⥤ Sheaf (fppfTopology R) (Type (u + 1)) where
  obj := pointsSheaf
  map := pointsSheafMap
  map_id := pointsSheafMap_id
  map_comp := pointsSheafMap_comp

/-- On objects, `pointsSheafFunctor` is `pointsSheaf`. -/
@[simp]
theorem pointsSheafFunctor_obj {R : Type u} [CommRing R] (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafFunctor R).obj X = pointsSheaf X :=
  (rfl)

/-- On morphisms, `pointsSheafFunctor` is `pointsSheafMap`. -/
@[simp]
theorem pointsSheafFunctor_map {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    (pointsSheafFunctor R).map f = pointsSheafMap f :=
  (rfl)

/-- **Affine fppf points determine schemes over `Spec R` up to canonical isomorphism:**
`pointsSheafFunctor R` is fully faithful. -/
noncomputable def pointsSheafFunctorFullyFaithful (R : Type u) [CommRing R] :
    (pointsSheafFunctor R).FullyFaithful := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let G := algSpec (CommRingCat.of R)
  let _ : G.Full := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : G.Faithful := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  have hff : (GrothendieckTopology.uliftYoneda.{u + 1} J ⋙
      G.sheafPushforwardContinuous (Type (u + 1)) (fppfTopology R) J).FullyFaithful :=
    J.fullyFaithfulUliftYoneda.comp
      (Functor.FullyFaithful.ofFullyFaithful
        (G.sheafPushforwardContinuous (Type (u + 1)) (fppfTopology R) J))
  exact hff.ofIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by ext _ _; rfl)

/-- Every morphism between fppf sheaves of affine points of `R`-schemes comes from a morphism of
`R`-schemes. -/
noncomputable instance instFullPointsSheafFunctor (R : Type u) [CommRing R] :
    (pointsSheafFunctor R).Full :=
  (pointsSheafFunctorFullyFaithful R).full

/-- Morphisms of schemes over `Spec R` are determined by their induced maps on affine fppf
points. -/
instance instFaithfulPointsSheafFunctor (R : Type u) [CommRing R] :
    (pointsSheafFunctor R).Faithful :=
  (pointsSheafFunctorFullyFaithful R).faithful

/-- **Morphisms of schemes over `Spec R` are morphisms of their fppf sheaves of affine points.** -/
noncomputable def pointsSheafHomEquiv {R : Type u} [CommRing R]
    (X Y : Over (Spec (CommRingCat.of R))) :
    (X ⟶ Y) ≃ (pointsSheaf X ⟶ pointsSheaf Y) :=
  (pointsSheafFunctorFullyFaithful R).homEquiv

/-- The forward map of `pointsSheafHomEquiv` is `pointsSheafMap`. -/
@[simp]
theorem pointsSheafHomEquiv_apply {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    pointsSheafHomEquiv X Y f = pointsSheafMap f :=
  (rfl)

/-- Applying `pointsSheafMap` to the scheme morphism recovered from a sheaf map returns that
sheaf map. -/
@[simp]
theorem pointsSheafMap_pointsSheafHomEquiv_symm {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (α : pointsSheaf X ⟶ pointsSheaf Y) :
    pointsSheafMap ((pointsSheafHomEquiv X Y).symm α) = α :=
  (pointsSheafFunctorFullyFaithful R).map_preimage α

/-- Recovering a scheme morphism from the identity sheaf map yields the identity morphism. -/
@[simp]
theorem pointsSheafHomEquiv_symm_id {R : Type u} [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafHomEquiv X X).symm (𝟙 (pointsSheaf X)) = 𝟙 X := by
  apply (pointsSheafHomEquiv X X).injective
  simp

/-- Recovering scheme morphisms from fppf-sheaf maps preserves composition. -/
@[reassoc (attr := simp)]
theorem pointsSheafHomEquiv_symm_comp {R : Type u} [CommRing R]
    {X Y Z : Over (Spec (CommRingCat.of R))}
    (α : pointsSheaf X ⟶ pointsSheaf Y) (β : pointsSheaf Y ⟶ pointsSheaf Z) :
    (pointsSheafHomEquiv X Y).symm α ≫ (pointsSheafHomEquiv Y Z).symm β =
      (pointsSheafHomEquiv X Z).symm (α ≫ β) := by
  apply (pointsSheafHomEquiv X Z).injective
  simp

/-- **Isomorphisms of schemes over `Spec R` are isomorphisms of their fppf sheaves of points.** -/
noncomputable def pointsSheafIsoEquiv {R : Type u} [CommRing R]
    (X Y : Over (Spec (CommRingCat.of R))) :
    (X ≅ Y) ≃ (pointsSheaf X ≅ pointsSheaf Y) where
  toFun e :=
    { hom := pointsSheafMap e.hom
      inv := pointsSheafMap e.inv
      hom_inv_id := by rw [← pointsSheafMap_comp, e.hom_inv_id, pointsSheafMap_id]
      inv_hom_id := by rw [← pointsSheafMap_comp, e.inv_hom_id, pointsSheafMap_id] }
  invFun := (pointsSheafFunctorFullyFaithful R).preimageIso
  left_inv e := by ext1; exact (pointsSheafFunctorFullyFaithful R).preimage_map e.hom
  right_inv e := by ext1; exact (pointsSheafFunctorFullyFaithful R).map_preimage e.hom

/-- The forward morphism of `pointsSheafIsoEquiv X Y e` is `pointsSheafMap e.hom`. -/
@[simp]
theorem pointsSheafIsoEquiv_apply_hom {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    (pointsSheafIsoEquiv X Y e).hom = pointsSheafMap e.hom :=
  (rfl)

/-- The inverse morphism of `pointsSheafIsoEquiv X Y e` is `pointsSheafMap e.inv`. -/
@[simp]
theorem pointsSheafIsoEquiv_apply_inv {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    (pointsSheafIsoEquiv X Y e).inv = pointsSheafMap e.inv :=
  (rfl)

/-- The forward morphism of `(pointsSheafIsoEquiv X Y).symm e` is recovered from `e.hom`. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_hom {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (e : pointsSheaf X ≅ pointsSheaf Y) :
    ((pointsSheafIsoEquiv X Y).symm e).hom = (pointsSheafHomEquiv X Y).symm e.hom :=
  (rfl)

/-- The inverse morphism of `(pointsSheafIsoEquiv X Y).symm e` is recovered from `e.inv`. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_inv {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (e : pointsSheaf X ≅ pointsSheaf Y) :
    ((pointsSheafIsoEquiv X Y).symm e).inv = (pointsSheafHomEquiv Y X).symm e.inv :=
  (rfl)

/-- Recovering a scheme isomorphism from the identity sheaf isomorphism gives `Iso.refl`. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_refl {R : Type u} [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) :
    (pointsSheafIsoEquiv X X).symm (Iso.refl (pointsSheaf X)) = Iso.refl X := by
  ext1
  simp

/-- Recovering scheme isomorphisms from sheaf isomorphisms preserves composition. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_trans {R : Type u} [CommRing R]
    {X Y Z : Over (Spec (CommRingCat.of R))}
    (e₁ : pointsSheaf X ≅ pointsSheaf Y) (e₂ : pointsSheaf Y ≅ pointsSheaf Z) :
    (pointsSheafIsoEquiv X Z).symm (e₁ ≪≫ e₂) =
      (pointsSheafIsoEquiv X Y).symm e₁ ≪≫ (pointsSheafIsoEquiv Y Z).symm e₂ := by
  ext1
  simp

/-- Recovering scheme isomorphisms from sheaf isomorphisms commutes with symmetry. -/
@[simp]
theorem pointsSheafIsoEquiv_symm_symm {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (e : pointsSheaf X ≅ pointsSheaf Y) :
    (pointsSheafIsoEquiv Y X).symm e.symm = ((pointsSheafIsoEquiv X Y).symm e).symm := by
  ext1
  rfl

/-- **Fppf locally surjective morphisms over `Spec R` are epimorphisms.** If `f : X ⟶ Y` over
`Spec R` induces a locally surjective morphism on affine fppf points, then `f` is an epimorphism
in `Over (Spec R)`. -/
theorem epi_of_isLocallySurjective_pointsSheafMap {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Presheaf.IsLocallySurjective (fppfTopology R) (pointsSheafMap f).hom] :
    Epi f := by
  have : Sheaf.IsLocallySurjective ((pointsSheafFunctor R).map f) := ‹_›
  exact (pointsSheafFunctor R).epi_of_epi_map inferInstance

/-- **Fppf locally surjective morphisms over `Spec R` are surjective on underlying schemes.** If
`f : X ⟶ Y` over `Spec R` induces a locally surjective morphism on affine fppf points, then
`f.left : X.left ⟶ Y.left` is surjective on scheme points. The converse does not hold in general,
as shown by nilpotent closed immersions `Spec k ⟶ Spec (k[ε]/(ε²))`. -/
theorem surjective_left_of_isLocallySurjective_pointsSheafMap {R : Type u} [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Presheaf.IsLocallySurjective (fppfTopology R) (pointsSheafMap f).hom] :
    Surjective f.left := by
  refine ⟨fun y ↦ ?_⟩
  let 𝒰 := Y.left.affineOpenCover
  let i := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  let φ : CommRingCat.of R ⟶ 𝒰.X i := Spec.preimage (𝒰.f i ≫ Y.hom)
  let _ : Algebra R (𝒰.X i) := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i))) = 𝒰.f i ≫ Y.hom :=
    Spec.map_preimage _
  let A : CommAlgCat.{u} R := CommAlgCat.of R (𝒰.X i)
  let yA : (algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶ Y := Over.homMk (𝒰.f i) hφ.symm
  let _ : (algSpec (CommRingCat.of R)).Full :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (algSpec (CommRingCat.of R)).Faithful :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  let s : ToType ((pointsSheaf Y).obj.obj (Opposite.op (Opposite.op A))) := ULift.up yA
  let S := Presheaf.imageSieve (pointsSheafMap f).hom s
  have hS : S ∈ fppfTopology R (Opposite.op A) :=
    Presheaf.IsLocallySurjective.imageSieve_mem (J := fppfTopology R)
      (f := (pointsSheafMap f).hom) s
  rw [fppfTopology_def, Functor.mem_inducedTopology_iff_of_isCoverDense,
    GrothendieckTopology.mem_over_iff] at hS
  have : Scheme.fppfPrecoverage.HasIsos := ⟨fun g _ ↦ g.singleton_mem_fppfPrecoverage⟩
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨P, ⟨hsurj, -⟩, hPS⟩ := hS
  obtain ⟨_, _, hg, w, rfl⟩ := hsurj z
  cases hg with
  | @of W g hg =>
  obtain ⟨B, ψ, u, ⟨⟨xB⟩, hxB⟩, hu⟩ := (Sieve.overEquiv_iff _ _).mp (hPS W g hg)
  have hxB' : xB ≫ f = (algSpec (CommRingCat.of R)).map ψ ≫ yA := congrArg ULift.down hxB
  have hfac : (u.left ≫ xB.left) ≫ f.left = g ≫ yA.left := by
    rw [Category.assoc, ← Over.comp_left, hxB', Over.comp_left, ← Category.assoc,
      ← Over.comp_left, ← hu]
    rfl
  exact ⟨(u.left ≫ xB.left) w, (congrArg (fun m : W ⟶ Y.left ↦ m w) hfac).trans hz⟩

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
