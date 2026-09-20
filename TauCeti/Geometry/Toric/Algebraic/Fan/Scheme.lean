/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization

/-!
# The toric scheme of a regular fan

The affine toric schemes of the cones of a fan form a diagram indexed by the cones ordered by
inclusion: an inclusion `τ ≤ σ` of cones of a fan is a face inclusion, and it acts by the face
morphism from the affine toric scheme of `τ` to that of `σ`. When the fan is regular every face
morphism is an open immersion. Moreover, the images of the charts of two faces `τ` and `υ` of a
cone `σ` meet exactly in the image of the chart of `τ ⊓ υ`, which is again a cone of the fan, so
the diagram is locally directed in the sense of `CategoryTheory.Functor.IsLocallyDirected`.

Mathlib glues such a diagram of open immersions along the overlaps of its members
(`AlgebraicGeometry.Scheme.IsLocallyDirected`), and identifies the result with the colimit of the
diagram. This colimit is the toric scheme of the fan. Each affine toric chart is an open
subscheme of it, the charts cover it, and two points of the charts of `σ` and `τ` are identified
exactly when they come from a common point of the chart of `σ ⊓ τ`.

## Main declarations

* `TauCeti.Toric.Fan.affineToricDiagram`: the diagram of affine toric charts of a fan.
* `TauCeti.Toric.Fan.isLocallyDirected_affineToricDiagram`: for a regular fan, this diagram is
  locally directed.
* `TauCeti.Toric.Fan.algebraicRealization`: the toric scheme of a regular fan, the colimit of its
  diagram of affine toric charts.
* `TauCeti.Toric.Fan.affineToricChartι`: the open immersion of an affine toric chart into the
  toric scheme.
* `TauCeti.Toric.Fan.exists_affineToricChartι_apply_eq`: the affine toric charts cover the toric
  scheme.
* `TauCeti.Toric.Fan.affineToricChartι_eq_affineToricChartι_iff`: points of two
  charts are identified exactly along the chart of the intersection of the two cones.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)

/-! ### The diagram of affine toric charts -/

/-- The diagram of affine toric charts of a fan, indexed by its cones ordered by inclusion. An
inclusion `τ ≤ σ` acts by the face morphism from the chart of `τ` to the chart of `σ`. -/
@[expose] noncomputable def affineToricDiagram : Φ.cones ⥤ Scheme where
  obj σ := Φ.affineToricChart σ
  map {τ σ} f := faceAffineToricSchemeMap Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f))
  map_id _ := faceAffineToricSchemeMap_id _
  map_comp _ _ := (faceAffineToricSchemeMap_comp ..).symm

/-- The diagram of affine toric charts sends a cone to its affine toric chart. -/
@[simp]
theorem affineToricDiagram_obj (σ : Φ.cones) :
    Φ.affineToricDiagram.obj σ = Φ.affineToricChart σ :=
  (rfl)

/-- The diagram of affine toric charts sends an inclusion of cones to the face morphism. -/
@[simp]
theorem affineToricDiagram_map {τ σ : Φ.cones} (f : τ ⟶ σ) :
    Φ.affineToricDiagram.map f =
      faceAffineToricSchemeMap Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)) :=
  (rfl)

variable {Φ}

/-- A morphism of the diagram of affine toric charts whose target cone is regular is an open
immersion. -/
theorem isOpenImmersion_affineToricDiagram_map {τ σ : Φ.cones} (hσ : IsRegularCone i σ.1)
    (f : τ ⟶ σ) : IsOpenImmersion (Φ.affineToricDiagram.map f) := by
  rw [affineToricDiagram_map]
  exact hσ.isOpenImmersion_faceAffineToricSchemeMap _ _

/-- The diagram of affine toric charts of a regular fan is locally directed: if points of the
charts of two faces `τ` and `υ` of a cone `σ` have the same image in the chart of `σ`, they come
from a common point of the chart of `τ ⊓ υ`. -/
theorem isLocallyDirected_affineToricDiagram (hΦ : Φ.IsRegular) :
    (Φ.affineToricDiagram ⋙ Scheme.forget).IsLocallyDirected := by
  refine ⟨fun {τ υ σ} fτ fυ xτ xυ h ↦ ?_⟩
  have hτσ := Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom fτ)
  have hυσ := Φ.isFaceOf_of_le σ.2 υ.2 (leOfHom fυ)
  -- On points, the functor `Φ.affineToricDiagram ⋙ Scheme.forget` applies the face morphisms.
  have h' : faceAffineToricSchemeMap Φ.lattice hτσ xτ =
      faceAffineToricSchemeMap Φ.lattice hυσ xυ := h
  have hσ := isRegular_iff.1 hΦ _ σ.2
  have := hσ.isOpenImmersion_faceAffineToricSchemeMap Φ.lattice hτσ
  have := hσ.isOpenImmersion_faceAffineToricSchemeMap Φ.lattice hυσ
  -- The common image lies in the image of the chart of `τ ⊓ υ`.
  obtain ⟨x, hx⟩ : faceAffineToricSchemeMap Φ.lattice hτσ xτ ∈
      Set.range (faceAffineToricSchemeMap Φ.lattice (hτσ.inf_left hυσ)) := by
    rw [hσ.range_faceAffineToricSchemeMap_inf Φ.lattice hτσ hυσ]
    exact ⟨⟨xτ, rfl⟩, ⟨xυ, h'.symm⟩⟩
  have hτ : faceAffineToricSchemeMap Φ.lattice (Φ.isFaceOf_of_le τ.2 (Φ.inf_mem τ.2 υ.2)
      inf_le_left) x = xτ := by
    apply (faceAffineToricSchemeMap Φ.lattice hτσ).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp, hx]
  have hυ : faceAffineToricSchemeMap Φ.lattice (Φ.isFaceOf_of_le υ.2 (Φ.inf_mem τ.2 υ.2)
      inf_le_right) x = xυ := by
    apply (faceAffineToricSchemeMap Φ.lattice hυσ).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp, hx, h']
  exact ⟨⟨τ.1 ⊓ υ.1, Φ.inf_mem τ.2 υ.2⟩, homOfLE (Subtype.coe_le_coe.1 inf_le_left),
    homOfLE (Subtype.coe_le_coe.1 inf_le_right), x, hτ, hυ⟩

/-! ### The toric scheme of a regular fan -/

variable (Φ)

/-- The toric scheme of a regular fan: the colimit of its diagram of affine toric charts, which
glues the charts along the open immersions of their faces. -/
@[expose] noncomputable def algebraicRealization (hΦ : Φ.IsRegular) : Scheme :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram hΦ
  colimit Φ.affineToricDiagram

/-- The inclusion of the affine toric chart of a cone into the toric scheme of a regular fan. -/
noncomputable def affineToricChartι (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    Φ.affineToricChart σ ⟶ Φ.algebraicRealization hΦ :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram hΦ
  colimit.ι Φ.affineToricDiagram σ

/-- The colimit cocone from the affine toric charts to the toric scheme of a regular fan. -/
@[expose] noncomputable def affineToricCocone (hΦ : Φ.IsRegular) :
    Cocone Φ.affineToricDiagram :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram hΦ
  colimit.cocone Φ.affineToricDiagram

/-- The point of the affine toric cocone is the toric scheme. -/
@[simp]
theorem affineToricCocone_pt (hΦ : Φ.IsRegular) :
    (Φ.affineToricCocone hΦ).pt = Φ.algebraicRealization hΦ :=
  by simp only [affineToricCocone, algebraicRealization, colimit.cocone_x]

/-- The legs of the affine toric cocone are the affine chart inclusions. -/
@[simp]
theorem affineToricCocone_ι_app (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    (Φ.affineToricCocone hΦ).ι.app σ = Φ.affineToricChartι hΦ σ :=
  by
    unfold affineToricCocone affineToricChartι
    rfl

/-- The affine toric cocone is a colimit cocone. -/
noncomputable def isColimitAffineToricCocone (hΦ : Φ.IsRegular) :
    IsColimit (Φ.affineToricCocone hΦ) :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram hΦ
  colimit.isColimit Φ.affineToricDiagram

variable {Φ}

/-- Each affine toric chart is an open subscheme of the toric scheme of a regular fan. -/
instance isOpenImmersion_affineToricChartι (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    IsOpenImmersion (Φ.affineToricChartι hΦ σ) :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram hΦ
  inferInstanceAs (IsOpenImmersion (colimit.ι Φ.affineToricDiagram σ))

/-- The inclusion of the chart of a face factors through the face morphism into the chart of the
ambient cone. -/
@[reassoc (attr := simp)]
theorem faceAffineToricSchemeMap_comp_affineToricChartι (hΦ : Φ.IsRegular) {τ σ : Φ.cones}
    (h : τ.1.IsFaceOf σ.1) :
    faceAffineToricSchemeMap Φ.lattice h ≫ Φ.affineToricChartι hΦ σ =
      Φ.affineToricChartι hΦ τ :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram hΦ
  colimit.w Φ.affineToricDiagram (homOfLE h.le)

/-- The left overlap map followed by its chart inclusion is the inclusion of the overlap chart. -/
@[reassoc]
theorem affineToricOverlapLeft_comp_affineToricChartι (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    Φ.affineToricOverlapLeft σ τ ≫ Φ.affineToricChartι hΦ σ =
      Φ.affineToricChartι hΦ ⟨σ.1 ⊓ τ.1, Φ.inf_mem σ.2 τ.2⟩ := by
  simpa only [affineToricOverlapLeft_def] using
    faceAffineToricSchemeMap_comp_affineToricChartι hΦ
      (τ := ⟨σ.1 ⊓ τ.1, Φ.inf_mem σ.2 τ.2⟩) (σ := σ)
      (Φ.inf_isFaceOf_left σ.2 τ.2)

/-- The right overlap map followed by its chart inclusion is the inclusion of the overlap chart. -/
@[reassoc]
theorem affineToricOverlapRight_comp_affineToricChartι (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    Φ.affineToricOverlapRight σ τ ≫ Φ.affineToricChartι hΦ τ =
      Φ.affineToricChartι hΦ ⟨σ.1 ⊓ τ.1, Φ.inf_mem σ.2 τ.2⟩ := by
  simpa only [affineToricOverlapRight_def] using
    faceAffineToricSchemeMap_comp_affineToricChartι hΦ
      (τ := ⟨σ.1 ⊓ τ.1, Φ.inf_mem σ.2 τ.2⟩) (σ := τ)
      (Φ.inf_isFaceOf_right σ.2 τ.2)

/-- The two inclusions of a pairwise overlap into the toric scheme agree. -/
theorem affineToricOverlap_comp_affineToricChartι (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    Φ.affineToricOverlapLeft σ τ ≫ Φ.affineToricChartι hΦ σ =
      Φ.affineToricOverlapRight σ τ ≫ Φ.affineToricChartι hΦ τ := by
  rw [affineToricOverlapLeft_comp_affineToricChartι,
    affineToricOverlapRight_comp_affineToricChartι]

/-- Every point of the toric scheme of a regular fan lies in one of its affine toric charts. -/
theorem exists_affineToricChartι_apply_eq (hΦ : Φ.IsRegular) (x : Φ.algebraicRealization hΦ) :
    ∃ (σ : Φ.cones) (y : Φ.affineToricChart σ), Φ.affineToricChartι hΦ σ y = x :=
  haveI := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  haveI := isLocallyDirected_affineToricDiagram hΦ
  Scheme.IsLocallyDirected.ι_jointly_surjective Φ.affineToricDiagram x

/-- Points of the affine toric charts of two cones `σ` and `τ` of a regular fan have the same
image in the toric scheme exactly when they come from a common point of the chart of `σ ⊓ τ`. -/
theorem affineToricChartι_eq_affineToricChartι_iff (hΦ : Φ.IsRegular)
    {σ τ : Φ.cones} (x : Φ.affineToricChart σ) (y : Φ.affineToricChart τ) :
    Φ.affineToricChartι hΦ σ x = Φ.affineToricChartι hΦ τ y ↔
      ∃ z : Φ.affineToricOverlap σ τ,
        Φ.affineToricOverlapLeft σ τ z = x ∧ Φ.affineToricOverlapRight σ τ z = y := by
  have := fun {τ σ : Φ.cones} (f : τ ⟶ σ) ↦
    isOpenImmersion_affineToricDiagram_map (isRegular_iff.1 hΦ _ σ.2) f
  have := isLocallyDirected_affineToricDiagram hΦ
  let στ : Φ.cones := ⟨σ.1 ⊓ τ.1, Φ.inf_mem σ.2 τ.2⟩
  refine ⟨fun h ↦ ?_, fun ⟨z, hzx, hzy⟩ ↦ ?_⟩
  · obtain ⟨κ, fσ, fτ, (w : Φ.affineToricChart κ), hwx, hwy⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff Φ.affineToricDiagram).1 h
    have hκ : κ.1.IsFaceOf στ.1 := Φ.isFaceOf_of_le στ.2 κ.2 (le_inf (leOfHom fσ) (leOfHom fτ))
    refine ⟨faceAffineToricSchemeMap Φ.lattice hκ w, ?_, ?_⟩
    -- `hwx` and `hwy` are stated with the diagram maps, which are the face morphisms.
    · rw [affineToricOverlapLeft_def, ← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp]
      exact hwx
    · rw [affineToricOverlapRight_def, ← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp]
      exact hwy
  · rw [← hzx, ← hzy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      affineToricOverlapLeft_comp_affineToricChartι,
      affineToricOverlapRight_comp_affineToricChartι]

end TauCeti.Toric.Fan
