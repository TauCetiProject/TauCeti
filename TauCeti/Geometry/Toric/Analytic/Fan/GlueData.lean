/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import TauCeti.Geometry.Toric.Analytic.Fan.Cocycle
public import TauCeti.Geometry.Toric.Analytic.Fan.Transition

/-!
# The analytic realization of a regular fan

The affine analytic charts of a regular fan, their pairwise overlap loci and the transitions
between them form gluing data for topological spaces in the sense of `TopCat.GlueData`. This
file assembles that gluing data and defines the analytic realization of the fan as the glued
space `TopCat.GlueData.glued`. Every affine chart is an open subspace of the realization, the
charts cover it, and points of two charts are identified exactly when they come from a common
point of the chart of the intersection cone.

## Main declarations

* `TauCeti.Toric.Fan.analyticGlueData`: the gluing data of the affine analytic charts of a
  regular fan along their overlap transitions.
* `TauCeti.Toric.Fan.analyticRealization`: the analytic realization of a regular fan, the glued
  space of this gluing data.
* `TauCeti.Toric.Fan.analyticAffineChartι`: the inclusion of an affine analytic chart into the
  realization, an open embedding by `TauCeti.Toric.Fan.isOpenEmbedding_analyticAffineChartι`.
* `TauCeti.Toric.Fan.exists_analyticAffineChartι_apply_eq`: the affine charts cover the
  realization.
* `TauCeti.Toric.Fan.analyticAffineChartι_eq_analyticAffineChartι_iff`: points of two charts are
  identified exactly along the chart of the intersection cone.
* `TauCeti.Toric.Fan.isOpen_iff_forall_preimage_analyticAffineChartι`: a subset of the
  realization is open exactly when its preimage in every chart is open.

## Implementation notes

The gluing data is built with `TopCat.GlueData.mk'`, whose index type and spaces live in one
universe, so the lattice `N` and the real vector space `V` are taken in a common universe here.
The gluing data is exposed so that its index type and charts are definitionally the cones and the
affine analytic charts, which is what lets the chart inclusions be stated on the objects of
`TauCeti.Toric.Fan.analyticAffineChartDiagram` and lets the `TopCat.GlueData` API be applied at a
cone.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open CategoryTheory Topology TopologicalSpace

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-! ### The gluing data -/

/-- The gluing data of the affine analytic charts of a regular fan along their overlap
transitions: the charts, their overlap loci and the overlap transitions, together with the
identity, triple-overlap and cocycle laws. -/
@[expose] noncomputable def analyticGlueData : TopCat.GlueData :=
  TopCat.GlueData.mk'
    { J := Φ.cones
      U σ := (Φ.analyticAffineChartDiagram hΦ).obj σ
      V σ τ := Φ.analyticOverlapOpens hΦ σ τ
      t σ τ := Φ.analyticOverlapTransition hΦ σ τ
      V_id := Φ.analyticOverlapOpens_self hΦ
      t_id σ := by rw [analyticOverlapTransition_self, TopCat.coe_id]
      t_inter {σ τ} υ x h := by
        -- `x` is a point of the overlap open set, and the transition is stated on the
        -- corresponding `TopCat` object; these agree only up to unfolding `Opens.toTopCat`.
        erw [analyticOverlapTransition_apply]
        exact Φ.analyticOverlapHomeomorph_mem hΦ σ τ υ x h
      cocycle σ τ υ x h := by
        -- Restate the transition formula on points of the overlap open sets, the form in which
        -- `TopCat.GlueData.MkCore` phrases the cocycle law.
        have e : ∀ (σ τ : Φ.cones) (y : Φ.analyticOverlapOpens hΦ σ τ),
            Subtype.val (Φ.analyticOverlapTransition hΦ σ τ y) =
              Subtype.val (Φ.analyticOverlapHomeomorph hΦ σ τ y) := fun σ τ y ↦ by
          erw [analyticOverlapTransition_apply]
        simp only [e]
        exact Φ.analyticOverlapHomeomorph_cocycle hΦ σ τ υ x h }

/-- The gluing data is indexed by the cones of the fan. -/
@[simp] theorem analyticGlueData_J : (Φ.analyticGlueData hΦ).J = Φ.cones := (rfl)

/-- The space of the gluing data at a cone is its affine analytic chart. -/
@[simp] theorem analyticGlueData_U (σ : Φ.cones) :
    (Φ.analyticGlueData hΦ).U σ = (Φ.analyticAffineChartDiagram hΦ).obj σ := (rfl)

/-- The overlap space of the gluing data at two cones is the overlap open set of the first
chart with the second. -/
@[simp] theorem analyticGlueData_V (σ τ : Φ.cones) :
    (Φ.analyticGlueData hΦ).V (σ, τ) =
      (Opens.toTopCat _).obj (Φ.analyticOverlapOpens hΦ σ τ) := (rfl)

/-- The overlap space of the gluing data embeds into the first chart as an open subset. -/
@[simp] theorem analyticGlueData_f (σ τ : Φ.cones) :
    (Φ.analyticGlueData hΦ).f σ τ = (Φ.analyticOverlapOpens hΦ σ τ).inclusion' := (rfl)

/-- The transition of the gluing data is the overlap transition of the two charts. -/
@[simp] theorem analyticGlueData_t (σ τ : Φ.cones) :
    (Φ.analyticGlueData hΦ).t σ τ = Φ.analyticOverlapTransition hΦ σ τ := (rfl)

/-! ### The analytic realization -/

/-- The analytic realization of a regular fan: the space obtained by gluing its affine analytic
charts along their overlap transitions. -/
noncomputable abbrev analyticRealization : TopCat := (Φ.analyticGlueData hΦ).glued

/-- The inclusion of the affine analytic chart of a cone into the analytic realization. -/
noncomputable def analyticAffineChartι (σ : Φ.cones) :
    (Φ.analyticAffineChartDiagram hΦ).obj σ ⟶ Φ.analyticRealization hΦ :=
  (Φ.analyticGlueData hΦ).ι σ

/-- The chart inclusion is the inclusion of the gluing data at the cone. -/
theorem analyticAffineChartι_def (σ : Φ.cones) :
    Φ.analyticAffineChartι hΦ σ = (Φ.analyticGlueData hΦ).ι σ := (rfl)

/-- Each affine analytic chart is an open subspace of the analytic realization. -/
theorem isOpenEmbedding_analyticAffineChartι (σ : Φ.cones) :
    IsOpenEmbedding (Φ.analyticAffineChartι hΦ σ) :=
  (Φ.analyticGlueData hΦ).ι_isOpenEmbedding σ

/-- Every point of the analytic realization lies in one of the affine analytic charts. -/
theorem exists_analyticAffineChartι_apply_eq (x : Φ.analyticRealization hΦ) :
    ∃ (σ : Φ.cones) (y : (Φ.analyticAffineChartDiagram hΦ).obj σ),
      Φ.analyticAffineChartι hΦ σ y = x :=
  (Φ.analyticGlueData hΦ).ι_jointly_surjective x

/-- Two maps out of the analytic realization agree when they agree on every affine analytic
chart. -/
theorem analyticRealization_hom_ext {Z : TopCat} {g g' : Φ.analyticRealization hΦ ⟶ Z}
    (h : ∀ σ, Φ.analyticAffineChartι hΦ σ ≫ g = Φ.analyticAffineChartι hΦ σ ≫ g') : g = g' := by
  ext x
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  exact ConcreteCategory.congr_hom (h σ) y

/-- A subset of the analytic realization is open exactly when its preimage in every affine
analytic chart is open. -/
theorem isOpen_iff_forall_preimage_analyticAffineChartι (s : Set (Φ.analyticRealization hΦ)) :
    IsOpen s ↔ ∀ σ, IsOpen (Φ.analyticAffineChartι hΦ σ ⁻¹' s) :=
  (Φ.analyticGlueData hΦ).isOpen_iff s

/-- Points of the affine analytic charts of two cones `σ` and `τ` have the same image in the
analytic realization exactly when they come from a common point of the chart of `σ ⊓ τ`. -/
theorem analyticAffineChartι_eq_analyticAffineChartι_iff {σ τ : Φ.cones}
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ)
    (y : (Φ.analyticAffineChartDiagram hΦ).obj τ) :
    Φ.analyticAffineChartι hΦ σ x = Φ.analyticAffineChartι hΦ τ y ↔
      ∃ z : (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ),
        Φ.analyticOverlapLeft hΦ σ τ z = x ∧ Φ.analyticOverlapRight hΦ σ τ z = y := by
  -- `TopCat.GlueData.ι_eq_iff_rel` is stated over the index type of the gluing data, which is
  -- `Φ.cones` only after unfolding `analyticGlueData`; apply it rather than rewriting with it.
  refine ((Φ.analyticGlueData hΦ).ι_eq_iff_rel σ τ x y).trans ?_
  -- On a point of the intersection chart, the transition of the gluing data is the opposite
  -- overlap inclusion. The gluing data is phrased on `TopCat` objects, whose points agree with
  -- those of the overlap open sets only after unfolding `Opens.toTopCat`, hence `erw`.
  have key : ∀ (z : (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ)) (hz),
      Subtype.val ((Φ.analyticGlueData hΦ).t σ τ ⟨Φ.analyticOverlapLeft hΦ σ τ z, hz⟩) =
        Φ.analyticOverlapRight hΦ σ τ z := fun z hz ↦ by
    erw [analyticGlueData_t, analyticOverlapTransition_apply, analyticOverlapHomeomorph_apply]
  constructor
  · rintro ⟨v, hx, hy⟩
    obtain ⟨z, hz⟩ := (Φ.mem_analyticOverlapOpens hΦ σ τ v.1).1 v.2
    obtain rfl : v = ⟨Φ.analyticOverlapLeft hΦ σ τ z, Φ.analyticOverlapLeft_mem hΦ σ τ z⟩ :=
      Subtype.ext hz.symm
    exact ⟨z, hx, (key z _).symm.trans hy⟩
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨⟨Φ.analyticOverlapLeft hΦ σ τ z, Φ.analyticOverlapLeft_mem hΦ σ τ z⟩, rfl, key z _⟩

/-- The inclusion of the chart of a face factors through the chart diagram map into the chart of
the ambient cone. -/
-- This is not a simp lemma: `analyticAffineChartDiagram_map` rewrites the diagram map to the
-- analytic face map first. The simp form is `analyticFaceMap_comp_analyticAffineChartι` below.
@[reassoc]
theorem analyticAffineChartDiagram_map_comp_analyticAffineChartι {τ σ : Φ.cones} (f : τ ⟶ σ) :
    (Φ.analyticAffineChartDiagram hΦ).map f ≫ Φ.analyticAffineChartι hΦ σ =
      Φ.analyticAffineChartι hΦ τ := by
  apply TopCat.ext
  intro x
  rw [TopCat.comp_app, analyticAffineChartι_eq_analyticAffineChartι_iff]
  refine ⟨(Φ.analyticAffineChartDiagram hΦ).map (homOfLE (le_inf (leOfHom f) le_rfl)) x, ?_, ?_⟩
  · rw [analyticOverlapLeft_def, analyticChartMap_comp]
    congr 1
  · rw [analyticOverlapRight_def, analyticChartMap_comp]
    have : (homOfLE (le_inf (leOfHom f) le_rfl) : τ ⟶ σ ⊓ τ) ≫ homOfLE inf_le_right = 𝟙 τ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, TopCat.id_app]

/-- The inclusion of the chart of a face factors through the analytic face map into the chart of
the ambient cone. -/
-- The composite is formed on the objects of the chart diagram, which is the form that
-- `analyticAffineChartDiagram_map` produces; a type ascription on the face map would not survive
-- elaboration, so the objects are passed explicitly. The face map is well-typed at these objects
-- only after unfolding the diagram, which `Category.assoc` cannot do while matching, so the
-- associated form is stated by hand rather than by `reassoc`.
@[simp]
theorem analyticFaceMap_comp_analyticAffineChartι {τ σ : Φ.cones} (f : τ ⟶ σ) :
    CategoryStruct.comp (X := (Φ.analyticAffineChartDiagram hΦ).obj τ)
        (Y := (Φ.analyticAffineChartDiagram hΦ).obj σ)
        (Φ.analyticFaceMap ((isRegular_iff.mp hΦ) τ.1 τ.2) ((isRegular_iff.mp hΦ) σ.1 σ.2) f)
        (Φ.analyticAffineChartι hΦ σ) =
      Φ.analyticAffineChartι hΦ τ :=
  Φ.analyticAffineChartDiagram_map_comp_analyticAffineChartι hΦ f

/-- The associated form of `analyticFaceMap_comp_analyticAffineChartι`. -/
@[simp]
theorem analyticFaceMap_comp_analyticAffineChartι_assoc {τ σ : Φ.cones} (f : τ ⟶ σ) {Z : TopCat}
    (h : Φ.analyticRealization hΦ ⟶ Z) :
    CategoryStruct.comp (X := (Φ.analyticAffineChartDiagram hΦ).obj τ)
        (Y := (Φ.analyticAffineChartDiagram hΦ).obj σ)
        (Φ.analyticFaceMap ((isRegular_iff.mp hΦ) τ.1 τ.2) ((isRegular_iff.mp hΦ) σ.1 σ.2) f)
        (Φ.analyticAffineChartι hΦ σ ≫ h) =
      Φ.analyticAffineChartι hΦ τ ≫ h :=
  Φ.analyticAffineChartDiagram_map_comp_analyticAffineChartι_assoc hΦ f h

/-- The left overlap inclusion followed by its chart inclusion is the inclusion of the chart of
the intersection cone. -/
@[reassoc (attr := simp)]
theorem analyticOverlapLeft_comp_analyticAffineChartι (σ τ : Φ.cones) :
    Φ.analyticOverlapLeft hΦ σ τ ≫ Φ.analyticAffineChartι hΦ σ =
      Φ.analyticAffineChartι hΦ (σ ⊓ τ) := by
  rw [analyticOverlapLeft_def, analyticAffineChartDiagram_map_comp_analyticAffineChartι]

/-- The right overlap inclusion followed by its chart inclusion is the inclusion of the chart of
the intersection cone. -/
@[reassoc (attr := simp)]
theorem analyticOverlapRight_comp_analyticAffineChartι (σ τ : Φ.cones) :
    Φ.analyticOverlapRight hΦ σ τ ≫ Φ.analyticAffineChartι hΦ τ =
      Φ.analyticAffineChartι hΦ (σ ⊓ τ) := by
  rw [analyticOverlapRight_def, analyticAffineChartDiagram_map_comp_analyticAffineChartι]

/-- The preimage in the chart of `τ` of the chart of `σ` is the overlap locus of `τ` with `σ`. -/
@[simp]
theorem analyticAffineChartι_preimage_range (σ τ : Φ.cones) :
    Φ.analyticAffineChartι hΦ τ ⁻¹' Set.range (Φ.analyticAffineChartι hΦ σ) =
      Φ.analyticOverlapOpens hΦ τ σ := by
  -- `TopCat.GlueData.preimage_range` is stated over the index type of the gluing data; see
  -- `analyticAffineChartι_eq_analyticAffineChartι_iff`. The map `f τ σ` of the gluing data is
  -- the inclusion of the overlap open set, whose range is that open set.
  exact ((Φ.analyticGlueData hΦ).preimage_range σ τ).trans (Opens.set_range_inclusion' _)

/-- Two affine analytic charts meet in the realization exactly in the image of the chart of the
intersection cone. -/
@[simp]
theorem range_analyticAffineChartι_inter_range_analyticAffineChartι (σ τ : Φ.cones) :
    Set.range (Φ.analyticAffineChartι hΦ σ) ∩ Set.range (Φ.analyticAffineChartι hΦ τ) =
      Set.range (Φ.analyticAffineChartι hΦ (σ ⊓ τ)) := by
  -- `TopCat.GlueData.image_inter` is stated over the index type of the gluing data; see
  -- `analyticAffineChartι_eq_analyticAffineChartι_iff`.
  refine ((Φ.analyticGlueData hΦ).image_inter σ τ).trans ?_
  rw [← analyticOverlapLeft_comp_analyticAffineChartι, TopCat.coe_comp, TopCat.coe_comp,
    Set.range_comp, Set.range_comp, analyticAffineChartι_def]
  -- The map `f σ τ` of the gluing data is the inclusion of the overlap open set, whose range
  -- is the range of the left overlap inclusion.
  exact congrArg _ ((Opens.set_range_inclusion' _).trans (Φ.coe_analyticOverlapOpens hΦ σ τ))

end TauCeti.Toric.Fan
