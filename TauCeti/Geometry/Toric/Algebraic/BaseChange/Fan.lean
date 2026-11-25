/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import TauCeti.AlgebraicGeometry.Scheme.LocallyDirected
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.AffineChart

/-!
# Toric schemes of finite fans over an arbitrary commutative ring

For a finite fan `Φ` and a commutative ring `R`, the affine charts `Spec R[P_σ]` of the cones
of `Φ` form a diagram indexed by the cones ordered by inclusion, whose maps are the face chart
morphisms. These are open immersions, singular cones included, and the diagram is locally
directed: the charts of two faces of a cone meet in the chart of their intersection. Mathlib glues
such a diagram to its colimit, the toric scheme `X_{Φ,R}` of the fan over `R`. Each affine chart
is an open subscheme, the charts cover `X_{Φ,R}`, and morphisms out of `X_{Φ,R}` are exactly the
families of morphisms out of the charts compatible with the face maps.

For an `R`-algebra `S`, changing coefficients in the charts glues to a morphism
`X_{Φ,S} ⟶ X_{Φ,R}`, compatible with identities and composites of coefficient changes. The square
formed with `Spec S ⟶ Spec R` is cartesian, so `X_{Φ,S}` is the base change of `X_{Φ,R}` along
every ring homomorphism: no flatness, reducedness or noetherian hypothesis is needed, and
nilpotent coefficients are kept. The chart of a cone over `S` is the inverse image of its chart
over `R`. The proof exhibits `X_{Φ,S}` as glued relative to the chart cover of `X_{Φ,R}`
(Mathlib's `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`), and checks the cartesian
square chart by chart, where it is the base change of an affine semigroup scheme.

## Main declarations

* `TauCeti.Toric.Fan.finiteFanScheme`: the toric scheme of a finite fan over `R`.
* `TauCeti.Toric.Fan.affineChartι`: the open immersion of the affine chart of a cone.
* `TauCeti.Toric.Fan.isColimitAffineChartCocone`: the toric scheme is the colimit of the charts.
* `TauCeti.Toric.Fan.finiteFanSchemeDesc`: gluing compatible morphisms out of the charts.
* `TauCeti.Toric.Fan.affineChartOpenCover`: the locally directed affine open cover by the charts.
* `TauCeti.Toric.Fan.finiteFanSchemeToSpec`: the structure morphism to `Spec R`.
* `TauCeti.Toric.Fan.finiteFanSchemeMap`: the coefficient change morphism `X_{Φ,S} ⟶ X_{Φ,R}`.
* `TauCeti.Toric.Fan.isPullback_finiteFanSchemeMap`: `X_{Φ,S}` is the base change of `X_{Φ,R}`
  along `Spec S ⟶ Spec R`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* K.-W. Lan, *Arithmetic Compactifications of PEL-Type Shimura Varieties*, 6.1.1–6.1.2.
* The Stacks Project, Tag 01LH, for relative gluing.
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraMonoidAlgebra

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (Φ : Fan i)

/-! ### The diagram of affine charts -/

/-- The diagram of affine charts of a fan over `R`, indexed by its cones ordered by inclusion. An
inclusion `τ ≤ σ` acts by the face chart morphism from the chart of `τ` to the chart of `σ`. -/
@[expose] noncomputable def affineChartDiagram : Φ.cones ⥤ Scheme.{u} where
  obj σ := affineChart R Φ.lattice σ
  map {τ σ} f := faceAffineChartMap R Φ.lattice
    (Φ.isFaceOf_of_le σ.property τ.property (leOfHom f))
  map_id _ := faceAffineChartMap_id ..
  map_comp _ _ := (faceAffineChartMap_comp ..).symm

/-- The diagram of affine charts sends a cone to its affine chart. -/
@[simp]
theorem affineChartDiagram_obj (σ : Φ.cones) :
    (Φ.affineChartDiagram R).obj σ = affineChart R Φ.lattice σ :=
  (rfl)

/-- The diagram of affine charts sends an inclusion of cones to the face chart morphism. -/
@[simp]
theorem affineChartDiagram_map {τ σ : Φ.cones} (f : τ ⟶ σ) :
    (Φ.affineChartDiagram R).map f =
      faceAffineChartMap R Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property (leOfHom f)) :=
  (rfl)

variable {Φ}

/-- Every morphism of the diagram of affine charts is an open immersion. -/
instance isOpenImmersion_affineChartDiagram_map {τ σ : Φ.cones} (f : τ ⟶ σ) :
    IsOpenImmersion ((Φ.affineChartDiagram R).map f) := by
  rw [affineChartDiagram_map]
  exact (Φ.isToricCone σ.property).rational.isOpenImmersion_faceAffineChartMap R _ _

/-- The diagram of affine charts of a fan is locally directed: if points of the charts of two
faces `τ` and `υ` of a cone `σ` have the same image in the chart of `σ`, they come from a common
point of the chart of `τ ⊓ υ`. -/
instance isLocallyDirected_affineChartDiagram :
    (Φ.affineChartDiagram R ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.IsLocallyDirected.isLocallyDirected_of_range_inter_subset _ fun {τ υ σ} fτ fυ ↦
    ((Φ.isToricCone σ.property).rational.range_faceAffineChartMap_inf R Φ.lattice
      (Φ.isFaceOf_of_le σ.property τ.property (leOfHom fτ))
      (Φ.isFaceOf_of_le σ.property υ.property (leOfHom fυ))).ge

/-! ### The toric scheme of a finite fan -/

variable (Φ)

/-- The toric scheme `X_{Φ,R}` of a finite fan `Φ` over a commutative ring `R`: the colimit of its
diagram of affine charts, which glues the charts `Spec R[P_σ]` along the open immersions of their
faces. No regularity of the cones and no hypothesis on `R` is required. -/
noncomputable def finiteFanScheme : Scheme.{u} :=
  colimit (Φ.affineChartDiagram R)

/-- The inclusion of the affine chart of a cone into the toric scheme of a finite fan. -/
noncomputable def affineChartι (σ : Φ.cones) :
    affineChart R Φ.lattice σ ⟶ Φ.finiteFanScheme R :=
  colimit.ι (Φ.affineChartDiagram R) σ

/-- Glue morphisms out of the affine charts of a fan that are compatible with the face maps to a
morphism out of its toric scheme. -/
noncomputable def finiteFanSchemeDesc {X : Scheme.{u}}
    (g : ∀ σ : Φ.cones, affineChart R Φ.lattice σ ⟶ X)
    (hg : ∀ {τ σ : Φ.cones} (h : τ ≤ σ),
      faceAffineChartMap R Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property h) ≫ g σ = g τ) :
    Φ.finiteFanScheme R ⟶ X :=
  colimit.desc (Φ.affineChartDiagram R)
    { pt := X
      ι := { app := g
             naturality := fun _ _ f ↦ (hg (leOfHom f)).trans (Category.comp_id _).symm } }

/-- The glued morphism restricts to the given morphism on each affine chart. -/
@[reassoc (attr := simp)]
theorem affineChartι_finiteFanSchemeDesc {X : Scheme.{u}}
    (g : ∀ σ : Φ.cones, affineChart R Φ.lattice σ ⟶ X)
    (hg : ∀ {τ σ : Φ.cones} (h : τ ≤ σ),
      faceAffineChartMap R Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property h) ≫ g σ = g τ)
    (σ : Φ.cones) :
    Φ.affineChartι R σ ≫ Φ.finiteFanSchemeDesc R g hg = g σ :=
  colimit.ι_desc _ σ

/-- Morphisms out of the toric scheme of a fan are determined by their restrictions to the affine
charts. -/
@[ext]
theorem finiteFanScheme_hom_ext {X : Scheme.{u}} {g h : Φ.finiteFanScheme R ⟶ X}
    (H : ∀ σ, Φ.affineChartι R σ ≫ g = Φ.affineChartι R σ ≫ h) : g = h :=
  colimit.hom_ext H

variable {Φ}

/-- Each affine chart is an open subscheme of the toric scheme of a finite fan. -/
instance isOpenImmersion_affineChartι (σ : Φ.cones) : IsOpenImmersion (Φ.affineChartι R σ) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (Φ.affineChartDiagram R) σ))

/-- The inclusion of the chart of a face factors through the face chart morphism into the chart
of the ambient cone. -/
@[reassoc (attr := simp)]
theorem faceAffineChartMap_comp_affineChartι {τ σ : Φ.cones} (h : τ.val.IsFaceOf σ.val) :
    faceAffineChartMap R Φ.lattice h ≫ Φ.affineChartι R σ = Φ.affineChartι R τ :=
  colimit.w (Φ.affineChartDiagram R) (homOfLE h.le)

variable (Φ)

/-- The colimit cocone from the affine charts of a fan to its toric scheme. -/
-- Expose the cocone so that its point and legs reduce to the named scheme and chart inclusions.
@[expose] noncomputable def affineChartCocone : Cocone (Φ.affineChartDiagram R) where
  pt := Φ.finiteFanScheme R
  ι := { app := Φ.affineChartι R
         naturality := fun _ _ _ ↦ (faceAffineChartMap_comp_affineChartι R _).trans
           (Category.comp_id _).symm }

/-- The point of the chart cocone is the toric scheme. -/
@[simp]
theorem affineChartCocone_pt : (Φ.affineChartCocone R).pt = Φ.finiteFanScheme R := (rfl)

/-- The legs of the chart cocone are the chart inclusions. -/
@[simp]
theorem affineChartCocone_ι_app (σ : Φ.cones) :
    (Φ.affineChartCocone R).ι.app σ = Φ.affineChartι R σ := (rfl)

/-- The toric scheme of a fan is the colimit of its affine charts. -/
noncomputable def isColimitAffineChartCocone : IsColimit (Φ.affineChartCocone R) :=
  colimit.isColimit (Φ.affineChartDiagram R)

variable {Φ}

/-- Every point of the toric scheme of a finite fan lies in one of its affine charts. -/
theorem exists_affineChartι_apply_eq (x : Φ.finiteFanScheme R) :
    ∃ (σ : Φ.cones) (y : affineChart R Φ.lattice σ), Φ.affineChartι R σ y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (Φ.affineChartDiagram R) x

/-- Points of the affine charts of two cones `σ` and `τ` have the same image in the toric scheme
exactly when they come from a common point of the chart of `σ ⊓ τ`. -/
theorem affineChartι_apply_eq_affineChartι_apply_iff {σ τ : Φ.cones}
    (x : affineChart R Φ.lattice σ) (y : affineChart R Φ.lattice τ) :
    Φ.affineChartι R σ x = Φ.affineChartι R τ y ↔
      ∃ z : affineChart R Φ.lattice (σ.val ⊓ τ.val),
        faceAffineChartMap R Φ.lattice (Φ.inf_isFaceOf_left σ.property τ.property) z = x ∧
          faceAffineChartMap R Φ.lattice (Φ.inf_isFaceOf_right σ.property τ.property) z = y :=
  Scheme.IsLocallyDirected.ι_eq_ι_iff_inf (Φ.affineChartDiagram R)

variable (Φ)

/-- The canonical affine open cover of the toric scheme of a finite fan, indexed by its cones. -/
-- Expose the cover so that its index type is the cone type in importing modules.
@[expose]
noncomputable def affineChartOpenCover : (Φ.finiteFanScheme R).OpenCover :=
  Scheme.Cover.mkOfCovers Φ.cones (fun σ ↦ affineChart R Φ.lattice σ) (Φ.affineChartι R)
    (Φ.exists_affineChartι_apply_eq R)

/-- The members of the chart cover are the affine charts. -/
@[simp]
theorem affineChartOpenCover_X (σ : Φ.cones) :
    (Φ.affineChartOpenCover R).X σ = affineChart R Φ.lattice σ := (rfl)

/-- The maps of the chart cover are the chart inclusions. -/
@[simp]
theorem affineChartOpenCover_f (σ : Φ.cones) :
    (Φ.affineChartOpenCover R).f σ = Φ.affineChartι R σ := (rfl)

/-- The cones of a fan index its affine chart open cover, ordered by inclusion. -/
instance : Category (Φ.affineChartOpenCover R).I₀ := inferInstanceAs (Category Φ.cones)

/-- The index category of the chart cover is a preorder, hence thin. -/
instance : Quiver.IsThin (Φ.affineChartOpenCover R).I₀ := inferInstanceAs (Quiver.IsThin Φ.cones)

/-- A fan has finitely many cones, so its chart cover has a small index type. -/
instance : Small.{u} (Φ.affineChartOpenCover R).I₀ := inferInstanceAs (Small.{u} Φ.cones)

/-- The affine chart open cover is locally directed: its transition maps are the face chart
morphisms, and the overlap of the charts of `σ` and `τ` is covered by the chart of `σ ⊓ τ`. -/
noncomputable instance : (Φ.affineChartOpenCover R).LocallyDirected where
  trans f := (Φ.affineChartDiagram R).map f
  trans_id σ := (Φ.affineChartDiagram R).map_id σ
  trans_comp f g := (Φ.affineChartDiagram R).map_comp f g
  w {τ σ} f := faceAffineChartMap_comp_affineChartι R (τ := τ) (σ := σ) _
  directed x := by
    -- The chart inclusions are by definition the colimit inclusions of the chart diagram.
    exact Scheme.IsLocallyDirected.exists_pullback_lift_eq (Φ.affineChartDiagram R) x
  property_trans f := isOpenImmersion_affineChartDiagram_map R f

/-- The transition maps of the affine chart open cover are the face chart morphisms. -/
@[simp]
theorem affineChartOpenCover_trans {τ σ : Φ.cones} (f : τ ⟶ σ) :
    (Φ.affineChartOpenCover R).trans f =
      faceAffineChartMap R Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property (leOfHom f)) :=
  (rfl)

/-! ### The structure morphism -/

-- The structure morphisms of the charts are compatible with the face chart morphisms.
private theorem faceAffineChartMap_comp_specAlgebraMap_of_le {τ σ : Φ.cones} (h : τ ≤ σ) :
    faceAffineChartMap R Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property h) ≫
      Spec.algebraMap R (affineChartRing R Φ.lattice σ) =
        Spec.algebraMap R (affineChartRing R Φ.lattice τ) :=
  faceAffineChartMap_comp_specAlgebraMap ..

/-- The structure morphism from the toric scheme of a fan over `R` to `Spec R`. -/
noncomputable def finiteFanSchemeToSpec : Φ.finiteFanScheme R ⟶ Spec (.of R) :=
  Φ.finiteFanSchemeDesc R (fun σ ↦ Spec.algebraMap R (affineChartRing R Φ.lattice σ))
    (Φ.faceAffineChartMap_comp_specAlgebraMap_of_le R)

/-- On each affine chart, the structure morphism is the structure morphism of `Spec R[P_σ]`. -/
@[reassoc (attr := simp)]
theorem affineChartι_finiteFanSchemeToSpec (σ : Φ.cones) :
    Φ.affineChartι R σ ≫ Φ.finiteFanSchemeToSpec R =
      Spec.algebraMap R (affineChartRing R Φ.lattice σ) :=
  Φ.affineChartι_finiteFanSchemeDesc R _ (Φ.faceAffineChartMap_comp_specAlgebraMap_of_le R) σ

/-! ### Change of coefficients -/

variable (S : Type u) [CommRing S] [Algebra R S]

-- Changing coefficients in the charts is compatible with the face chart morphisms.
private theorem faceAffineChartMap_comp_specAlgebraMap_comp_affineChartι_of_le {τ σ : Φ.cones}
    (h : τ ≤ σ) :
    faceAffineChartMap S Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property h) ≫
      Spec.algebraMap (affineChartRing R Φ.lattice σ) (affineChartRing S Φ.lattice σ) ≫
        Φ.affineChartι R σ =
      Spec.algebraMap (affineChartRing R Φ.lattice τ) (affineChartRing S Φ.lattice τ) ≫
        Φ.affineChartι R τ := by
  rw [faceAffineChartMap_comp_specAlgebraMap_affineChartRing_assoc,
    faceAffineChartMap_comp_affineChartι]

/-- The morphism `X_{Φ,S} ⟶ X_{Φ,R}` of toric schemes induced by an `R`-algebra `S`: on each
affine chart it changes coefficients from `R` to `S`. -/
noncomputable def finiteFanSchemeMap : Φ.finiteFanScheme S ⟶ Φ.finiteFanScheme R :=
  Φ.finiteFanSchemeDesc S
    (fun σ ↦ Spec.algebraMap (affineChartRing R Φ.lattice σ) (affineChartRing S Φ.lattice σ) ≫
      Φ.affineChartι R σ)
    (Φ.faceAffineChartMap_comp_specAlgebraMap_comp_affineChartι_of_le R S)

/-- On each affine chart, the coefficient change morphism is the coefficient change of the chart
followed by the inclusion of the chart. -/
@[reassoc (attr := simp)]
theorem affineChartι_finiteFanSchemeMap (σ : Φ.cones) :
    Φ.affineChartι S σ ≫ Φ.finiteFanSchemeMap R S =
      Spec.algebraMap (affineChartRing R Φ.lattice σ) (affineChartRing S Φ.lattice σ) ≫
        Φ.affineChartι R σ :=
  Φ.affineChartι_finiteFanSchemeDesc S _
    (Φ.faceAffineChartMap_comp_specAlgebraMap_comp_affineChartι_of_le R S) σ

/-- The coefficient change morphism lies over `Spec S ⟶ Spec R`. -/
@[reassoc]
theorem finiteFanSchemeMap_comp_finiteFanSchemeToSpec :
    Φ.finiteFanSchemeMap R S ≫ Φ.finiteFanSchemeToSpec R =
      Φ.finiteFanSchemeToSpec S ≫ Spec.algebraMap R S := by
  ext σ : 1
  rw [affineChartι_finiteFanSchemeMap_assoc, affineChartι_finiteFanSchemeToSpec,
    affineChartι_finiteFanSchemeToSpec_assoc]
  exact (AlgebraicGeometry.isPullback_addMonoidAlgebraSpec R S
    (dualSemigroup Φ.lattice σ.val)).w

/-- Changing coefficients along the identity of `R` is the identity morphism. -/
@[simp]
theorem finiteFanSchemeMap_self : Φ.finiteFanSchemeMap R R = 𝟙 (Φ.finiteFanScheme R) := by
  ext σ : 1
  rw [affineChartι_finiteFanSchemeMap, Category.comp_id]
  -- The algebra structure of `R[P_σ]` over itself used here is coefficient change along `𝟙 R`.
  convert Category.id_comp (Φ.affineChartι R σ)
  rw [Spec.algebraMap, ← Spec.map_id]
  congr 1
  ext : 1
  apply AddMonoidAlgebra.ringHom_ext <;> simp

/-- Changing coefficients along `R → S → T` is the composite of the two coefficient changes. -/
@[reassoc (attr := simp)]
theorem finiteFanSchemeMap_comp_finiteFanSchemeMap (T : Type u) [CommRing T] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] :
    Φ.finiteFanSchemeMap S T ≫ Φ.finiteFanSchemeMap R S = Φ.finiteFanSchemeMap R T := by
  ext σ : 1
  simp only [affineChartι_finiteFanSchemeMap_assoc, affineChartι_finiteFanSchemeMap]
  rw [← Category.assoc, Spec.algebraMap, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 3
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp [← IsScalarTower.algebraMap_apply]
  · intro m
    simp

/-- The toric scheme over `S` is glued relative to the affine chart cover of the toric scheme
over `R`: its charts map to the charts over `R` by coefficient change, and these maps form
cartesian squares with the face chart morphisms. -/
private noncomputable def relativeGluingData :
    (Φ.affineChartOpenCover R).RelativeGluingData where
  functor := Φ.affineChartDiagram S
  natTrans :=
    { app := fun (σ : Φ.cones) ↦
        Spec.algebraMap (affineChartRing R Φ.lattice σ) (affineChartRing S Φ.lattice σ)
      naturality := fun (τ σ : Φ.cones) f ↦
        faceAffineChartMap_comp_specAlgebraMap_affineChartRing R Φ.lattice S
          (Φ.isFaceOf_of_le σ.property τ.property (leOfHom f)) }
  equifibered := fun (τ σ : Φ.cones) f ↦
    isPullback_faceAffineChartMap R Φ.lattice S (Φ.isFaceOf_of_le σ.property τ.property (leOfHom f))

private theorem finiteFanSchemeMap_eq_toBase :
    Φ.finiteFanSchemeMap R S = (Φ.relativeGluingData R S).toBase := by
  ext σ : 1
  rw [affineChartι_finiteFanSchemeMap]
  exact ((Φ.relativeGluingData R S).ι_toBase σ).symm

/-- The chart of a cone over `S` is the inverse image of its chart over `R` under the coefficient
change morphism. -/
theorem isPullback_affineChartι_finiteFanSchemeMap (σ : Φ.cones) :
    IsPullback (Spec.algebraMap (affineChartRing R Φ.lattice σ) (affineChartRing S Φ.lattice σ))
      (Φ.affineChartι S σ) (Φ.affineChartι R σ) (Φ.finiteFanSchemeMap R S) := by
  rw [finiteFanSchemeMap_eq_toBase]
  exact (Φ.relativeGluingData R S).isPullback_natTrans_ι_toBase σ

/-- The toric scheme of a fan over an `R`-algebra `S` is the base change of its toric scheme over
`R`: the square formed by coefficient change and the structure morphisms is cartesian. -/
theorem isPullback_finiteFanSchemeMap :
    IsPullback (Φ.finiteFanSchemeMap R S) (Φ.finiteFanSchemeToSpec S)
      (Φ.finiteFanSchemeToSpec R) (Spec.algebraMap R S) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Φ.affineChartOpenCover R)
    fun (σ : Φ.cones) ↦ ?_
  -- Restate the chart square with the cover's own leg, so that it matches the pulled-back cover.
  have hσ : IsPullback (Φ.affineChartι S σ)
      (Spec.algebraMap (affineChartRing R Φ.lattice σ) (affineChartRing S Φ.lattice σ))
      (Φ.finiteFanSchemeMap R S) ((Φ.affineChartOpenCover R).f σ) :=
    (Φ.isPullback_affineChartι_finiteFanSchemeMap R S σ).flip
  refine IsPullback.of_iso
    (AlgebraicGeometry.isPullback_addMonoidAlgebraSpec R S (dualSemigroup Φ.lattice σ.val))
    hσ.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  -- The legs of the pulled-back cover are the pullback projections, and identity isomorphisms
  -- have identity homs; the four squares are unit laws and the defining chart equations.
  · exact (Category.comp_id _).trans hσ.isoPullback_hom_snd.symm
  · exact (Φ.affineChartι_finiteFanSchemeToSpec S σ).symm.trans
      (hσ.isoPullback_hom_fst_assoc _).symm
  · exact (Category.comp_id _).trans ((Φ.affineChartι_finiteFanSchemeToSpec R σ).symm.trans
      (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm


end TauCeti.Toric.Fan
