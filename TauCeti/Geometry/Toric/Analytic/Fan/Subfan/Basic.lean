/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.GlueData

/-!
# The analytic realization of an open subfan

A face-closed set of cones of a regular fan is itself a regular fan, `TauCeti.Toric.Fan.subfan`.
The affine chart of one of its cones and the affine chart of the same cone in the ambient fan have
the same underlying complex points, and their monomial-embedding topologies agree because that
topology does not depend on the chosen finite generating family. These identity-on-points chart
comparisons commute with the face maps of the two chart diagrams, so they glue to a continuous map
from the realization of the subfan to the ambient realization.

Composed with the inclusion of the chart of a cone of the subfan, this map is the chart comparison
followed by the inclusion of the chart of the same cone in the ambient realization. It is an open
embedding whose image is the union of the ambient charts of the cones of the subfan. No
nonemptiness assumption is made on the set of cones of the subfan.

## Main declarations

* `TauCeti.Toric.Fan.subfanAnalyticChartMap`: the identity-on-points homeomorphism between the
  chart of a cone of a subfan and the chart of the same cone in the ambient fan.
* `TauCeti.Toric.Fan.subfanAnalyticMap`: the map from the analytic realization of a subfan to
  the ambient analytic realization.
* `TauCeti.Toric.Fan.analyticAffineChartι_comp_subfanAnalyticMap`: its chart formula.
* `TauCeti.Toric.Fan.range_subfanAnalyticMap`: its image is the union of the ambient charts of
  the cones of the subfan.
* `TauCeti.Toric.Fan.isOpenEmbedding_subfanAnalyticMap`: it is an open embedding.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
* The construction of the glued map and the proofs of injectivity, openness and the range follow
  Mathlib's `TopCat.GlueData.fromOpenSubsetsGlue` (`Mathlib.Topology.Gluing`).
-/

public section

open CategoryTheory Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

/-! ### Chart comparisons -/

/-- The chart of a cone of a subfan and the chart of the same cone in the ambient fan carry the
same topology. -/
theorem subfan_analyticAffineChartDiagram_obj_str (σ : (Φ.subfan S hS hface).cones) :
    (((Φ.subfan S hS hface).analyticAffineChartDiagram).obj σ).str =
      ((Φ.analyticAffineChartDiagram).obj
        ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩).str := by
  let g := Φ.analyticChartGenerators ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩
  exact ((Φ.subfan S hS hface).analyticAffineChart_str_eq σ g.2).trans
    (Φ.analyticAffineChart_str_eq _ g.2).symm

/-- The identity-on-points homeomorphism from the chart of a cone of a subfan to the chart of the
same cone in the ambient fan. -/
noncomputable def subfanAnalyticChartMap (σ : (Φ.subfan S hS hface).cones) :
    ((Φ.subfan S hS hface).analyticAffineChartDiagram).obj σ ≃ₜ
      (Φ.analyticAffineChartDiagram).obj
        ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩ where
  toEquiv := Equiv.refl _
  continuous_toFun :=
    continuous_id_iff_le.mpr (Φ.subfan_analyticAffineChartDiagram_obj_str S hS hface σ).le
  continuous_invFun :=
    continuous_id_iff_le.mpr (Φ.subfan_analyticAffineChartDiagram_obj_str S hS hface σ).ge

/-- The chart comparison of a subfan is the identity on complex points. -/
@[simp]
theorem subfanAnalyticChartMap_apply (σ : (Φ.subfan S hS hface).cones)
    (x : ((Φ.subfan S hS hface).analyticAffineChartDiagram).obj σ) :
    (Φ.subfanAnalyticChartMap S hS hface σ x :
      AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) = x :=
  (rfl)

/-- The inverse chart comparison of a subfan is the identity on complex points. -/
@[simp]
theorem subfanAnalyticChartMap_symm_apply (σ : (Φ.subfan S hS hface).cones)
    (x : (Φ.analyticAffineChartDiagram).obj
      ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩) :
    ((Φ.subfanAnalyticChartMap S hS hface σ).symm x :
      AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) = x :=
  (rfl)

/-- The chart comparisons of a subfan commute with the face maps of the two chart diagrams. -/
theorem subfanAnalyticChartMap_map {τ σ : (Φ.subfan S hS hface).cones} (f : τ ⟶ σ)
    (x : ((Φ.subfan S hS hface).analyticAffineChartDiagram).obj τ) :
    Φ.subfanAnalyticChartMap S hS hface σ
        (((Φ.subfan S hS hface).analyticAffineChartDiagram).map f x) =
      (Φ.analyticAffineChartDiagram).map
        (homOfLE (leOfHom f))
        (Φ.subfanAnalyticChartMap S hS hface τ x) := by
  -- Both face maps restrict a complex point along the same inclusion of dual semigroups, and the
  -- chart comparisons are the identity on complex points (`subfanAnalyticChartMap_apply`).
  rw [analyticAffineChartDiagram_map_apply, analyticAffineChartDiagram_map_apply]
  rfl

/-- Points of two charts of a subfan with the same image in the realization of the subfan have the
same image, after the chart comparisons, in the ambient realization. -/
private theorem analyticAffineChartι_subfanAnalyticChartMap_eq_of_eq
    {σ τ : (Φ.subfan S hS hface).cones}
    {x : ((Φ.subfan S hS hface).analyticAffineChartDiagram).obj σ}
    {y : ((Φ.subfan S hS hface).analyticAffineChartDiagram).obj τ}
    (h : (Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) σ x =
      (Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) τ y) :
    Φ.analyticAffineChartι hΦ _ (Φ.subfanAnalyticChartMap S hS hface σ x) =
      Φ.analyticAffineChartι hΦ _ (Φ.subfanAnalyticChartMap S hS hface τ y) := by
  obtain ⟨z, rfl, rfl⟩ := ((Φ.subfan S hS hface).analyticAffineChartι_eq_analyticAffineChartι_iff
    (hΦ.subfan S hS hface) x y).mp h
  rw [analyticOverlapLeft_def, analyticOverlapRight_def, subfanAnalyticChartMap_map,
    subfanAnalyticChartMap_map, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    analyticAffineChartDiagram_map_comp_analyticAffineChartι,
    analyticAffineChartDiagram_map_comp_analyticAffineChartι]

/-! ### The glued map -/

/-- The map from the analytic realization of a subfan to the analytic realization of the ambient
fan, glued from the chart comparisons followed by the ambient chart inclusions. -/
noncomputable def subfanAnalyticMap :
    (Φ.subfan S hS hface).analyticRealization (hΦ.subfan S hS hface) ⟶
      Φ.analyticRealization hΦ :=
  Limits.Multicoequalizer.desc
    ((Φ.subfan S hS hface).analyticGlueData (hΦ.subfan S hS hface)).diagram
    (Φ.analyticRealization hΦ)
    (fun σ ↦ (TopCat.isoOfHomeo (Φ.subfanAnalyticChartMap S hS hface σ)).hom ≫
      Φ.analyticAffineChartι hΦ _) (by
    rintro ⟨σ, τ⟩
    ext x
    let D := (Φ.subfan S hS hface).analyticGlueData (hΦ.subfan S hS hface)
    -- The glue condition of the subfan, restated on its chart inclusions; the cones are typed as
    -- cones of the subfan so that `analyticAffineChartι_def` applies.
    have h : ∀ (σ τ : (Φ.subfan S hS hface).cones) (x : D.V (σ, τ)),
        (Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) σ (D.f σ τ x) =
          (Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) τ
            (D.f τ σ (D.t σ τ x)) := fun σ τ x ↦ by
      rw [analyticAffineChartι_def, analyticAffineChartι_def]
      exact (ConcreteCategory.congr_hom (D.glue_condition σ τ) x).symm
    rw [GlueData.diagram_fst, GlueData.diagram_snd]
    exact Φ.analyticAffineChartι_subfanAnalyticChartMap_eq_of_eq hΦ S hS hface (h σ τ x))

/-- On the chart of a cone of a subfan, the subfan map is the chart comparison followed by the
inclusion of the chart of the same cone in the ambient realization. -/
@[reassoc]
theorem analyticAffineChartι_comp_subfanAnalyticMap (σ : (Φ.subfan S hS hface).cones) :
    (Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) σ ≫
        Φ.subfanAnalyticMap hΦ S hS hface =
      (TopCat.isoOfHomeo (Φ.subfanAnalyticChartMap S hS hface σ)).hom ≫
        Φ.analyticAffineChartι hΦ _ := by
  rw [analyticAffineChartι_def]
  exact Limits.Multicoequalizer.π_desc _ _ _ _ _

/-- On a point of the chart of a cone of a subfan, the subfan map is the inclusion of the same
complex point in the chart of that cone in the ambient realization. -/
@[simp]
theorem subfanAnalyticMap_analyticAffineChartι (σ : (Φ.subfan S hS hface).cones)
    (x : ((Φ.subfan S hS hface).analyticAffineChartDiagram).obj σ) :
    Φ.subfanAnalyticMap hΦ S hS hface
        ((Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) σ x) =
      Φ.analyticAffineChartι hΦ _ (Φ.subfanAnalyticChartMap S hS hface σ x) :=
  ConcreteCategory.congr_hom (Φ.analyticAffineChartι_comp_subfanAnalyticMap hΦ S hS hface σ) x

/-- The subfan map is injective. -/
theorem subfanAnalyticMap_injective : Function.Injective (Φ.subfanAnalyticMap hΦ S hS hface) := by
  intro x y hxy
  obtain ⟨σ, x, rfl⟩ :=
    (Φ.subfan S hS hface).exists_analyticAffineChartι_apply_eq (hΦ.subfan S hS hface) x
  obtain ⟨τ, y, rfl⟩ :=
    (Φ.subfan S hS hface).exists_analyticAffineChartι_apply_eq (hΦ.subfan S hS hface) y
  rw [subfanAnalyticMap_analyticAffineChartι, subfanAnalyticMap_analyticAffineChartι,
    analyticAffineChartι_eq_analyticAffineChartι_iff] at hxy
  obtain ⟨z, hzx, hzy⟩ := hxy
  refine ((Φ.subfan S hS hface).analyticAffineChartι_eq_analyticAffineChartι_iff
    (hΦ.subfan S hS hface) x y).mpr ⟨(Φ.subfanAnalyticChartMap S hS hface (σ ⊓ τ)).symm z,
      ?_, ?_⟩
  · apply (Φ.subfanAnalyticChartMap S hS hface σ).injective
    rw [analyticOverlapLeft_def, subfanAnalyticChartMap_map, ← hzx, analyticOverlapLeft_def,
      Homeomorph.apply_symm_apply]
  · apply (Φ.subfanAnalyticChartMap S hS hface τ).injective
    rw [analyticOverlapRight_def, subfanAnalyticChartMap_map, ← hzy, analyticOverlapRight_def,
      Homeomorph.apply_symm_apply]

/-- The image of the subfan map is the union of the ambient charts of the cones of the subfan. -/
theorem range_subfanAnalyticMap :
    Set.range (Φ.subfanAnalyticMap hΦ S hS hface) =
      ⋃ σ : (Φ.subfan S hS hface).cones,
        Set.range (Φ.analyticAffineChartι hΦ
          ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨σ, y, rfl⟩ :=
      (Φ.subfan S hS hface).exists_analyticAffineChartι_apply_eq (hΦ.subfan S hS hface) y
    rw [subfanAnalyticMap_analyticAffineChartι]
    exact Set.mem_iUnion.mpr ⟨σ, Set.mem_range_self _⟩
  · intro hx
    obtain ⟨σ, y, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) σ
      ((Φ.subfanAnalyticChartMap S hS hface σ).symm y), ?_⟩
    rw [subfanAnalyticMap_analyticAffineChartι, Homeomorph.apply_symm_apply]

/-- The subfan map is an open map. -/
theorem isOpenMap_subfanAnalyticMap : IsOpenMap (Φ.subfanAnalyticMap hΦ S hS hface) := by
  intro s hs
  -- Cover `s` by its traces on the charts of the subfan and map each trace through its chart.
  have hcover : s = ⋃ σ, (Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) σ ''
      ((Φ.subfan S hS hface).analyticAffineChartι (hΦ.subfan S hS hface) σ ⁻¹' s) := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨σ, y, rfl⟩ :=
        (Φ.subfan S hS hface).exists_analyticAffineChartι_apply_eq (hΦ.subfan S hS hface) x
      exact Set.mem_iUnion.mpr ⟨σ, y, hx, rfl⟩
    · obtain ⟨σ, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hy
  rw [hcover, Set.image_iUnion]
  refine isOpen_iUnion fun σ ↦ ?_
  rw [Set.image_image]
  simp only [subfanAnalyticMap_analyticAffineChartι]
  rw [← Set.image_image]
  exact (Φ.isOpenEmbedding_analyticAffineChartι hΦ _).isOpenMap _
    ((Φ.subfanAnalyticChartMap S hS hface σ).isOpenMap _
      (hs.preimage (TopCat.Hom.hom _).continuous))

/-- The map from the analytic realization of a subfan to the ambient analytic realization is an
open embedding. -/
theorem isOpenEmbedding_subfanAnalyticMap :
    IsOpenEmbedding (Φ.subfanAnalyticMap hΦ S hS hface) :=
  .of_continuous_injective_isOpenMap (Φ.subfanAnalyticMap hΦ S hS hface).hom.continuous
    (Φ.subfanAnalyticMap_injective hΦ S hS hface) (Φ.isOpenMap_subfanAnalyticMap hΦ S hS hface)

end TauCeti.Toric.Fan
