/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

/-!
# The open subscheme associated to a subfan

A collection of cones of a finite regular fan that is closed under faces determines an open
subscheme of the fan's toric scheme. On each cone chart, the inclusion is the usual chart
inclusion. This supplies the algebraic open-subfan restriction used by toric chart gluing and
comparison with complex points.

Reference: W. Fulton, *Introduction to Toric Varieties*, §1.4.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

namespace Fan

/-- On every affine cone chart, the map of toric schemes induced by a subfan inclusion is the
ordinary inclusion of that chart into the ambient fan scheme. -/
@[reassoc]
theorem affineToricChartι_comp_subfanInclusion_algebraicMap
    (hΦ : Φ.IsRegular) (σ : (Φ.subfan S hS hface).cones) :
    (Φ.subfan S hS hface).affineToricChartι
        (hΦ.subfan S hS hface) σ ≫
      (Φ.subfanInclusion S hS hface).algebraicMap (hΦ.subfan S hS hface) hΦ =
      Φ.affineToricChartι hΦ ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩ := by
  let f := Φ.subfanInclusion S hS hface
  have hσleast : σ.1.IsFaceOf (f.leastCone σ.2) := by
    rw [show f.leastCone σ.2 = σ.1 from subfanInclusion_leastCone Φ S hS hface σ]
  have hmap : f.affineToricChartMap σ =
      faceAffineToricSchemeMap Φ.lattice hσleast := by
    rw [FanHom.affineToricChartMap_def, faceAffineToricSchemeMap_eq_affineToricSchemeMap]
    simp only [f, subfanInclusion_latticeMap, subfanInclusion_realMap]
  rw [FanHom.affineToricChartι_comp_algebraicMap, hmap]
  exact faceAffineToricSchemeMap_comp_affineToricChartι hΦ
    (τ := ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩)
    (σ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩) hσleast

/-- The map of algebraic realizations induced by a subfan inclusion is injective on points. -/
theorem subfanInclusion_algebraicMap_injective (hΦ : Φ.IsRegular) :
    Function.Injective
      ((Φ.subfanInclusion S hS hface).algebraicMap (hΦ.subfan S hS hface) hΦ) := by
  intro x y hxy
  obtain ⟨σ, a, rfl⟩ :=
    (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq (hΦ.subfan S hS hface) x
  obtain ⟨τ, b, rfl⟩ :=
    (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq (hΦ.subfan S hS hface) y
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    affineToricChartι_comp_subfanInclusion_algebraicMap,
    affineToricChartι_comp_subfanInclusion_algebraicMap] at hxy
  apply ((Φ.subfan S hS hface).affineToricChartι_eq_affineToricChartι_iff
    (hΦ.subfan S hS hface) a b).2
  obtain ⟨z, hza, hzb⟩ :=
    (Φ.affineToricChartι_eq_affineToricChartι_iff hΦ
      (σ := ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩)
      (τ := ⟨τ.1, hS (by simpa only [subfan_cones] using τ.2)⟩) a b).1 hxy
  refine ⟨z, ?_, ?_⟩
  · simpa only [Fan.affineToricOverlapLeft_def, subfan_lattice] using hza
  · simpa only [Fan.affineToricOverlapRight_def, subfan_lattice] using hzb

/-- The image of a subfan's algebraic realization is the union of its cone charts in the
ambient fan scheme. -/
theorem range_subfanInclusion_algebraicMap (hΦ : Φ.IsRegular) :
    Set.range ((Φ.subfanInclusion S hS hface).algebraicMap
      (hΦ.subfan S hS hface) hΦ) =
      ⋃ σ : (Φ.subfan S hS hface).cones,
        Set.range (Φ.affineToricChartι hΦ
          ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨σ, z, rfl⟩ :=
      (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq (hΦ.subfan S hS hface) y
    refine Set.mem_iUnion.mpr ⟨σ, ⟨z, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, affineToricChartι_comp_subfanInclusion_algebraicMap]
  · intro hx
    obtain ⟨σ, z, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(Φ.subfan S hS hface).affineToricChartι
      (hΦ.subfan S hS hface) σ z, ?_⟩
    rw [← Scheme.Hom.comp_apply, affineToricChartι_comp_subfanInclusion_algebraicMap]

/-- A face-closed subfan of a regular finite fan defines an open subscheme of its algebraic
toric variety. Its map to the ambient scheme is the toric map induced by the inclusion of fans. -/
instance isOpenImmersion_subfanInclusion_algebraicMap (hΦ : Φ.IsRegular) :
    IsOpenImmersion
      ((Φ.subfanInclusion S hS hface).algebraicMap (hΦ.subfan S hS hface) hΦ) := by
  apply IsOpenImmersion.of_forall_source_exists _
    (Φ.subfanInclusion_algebraicMap_injective S hS hface hΦ)
  intro x
  obtain ⟨σ, y, hy⟩ :=
    (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq (hΦ.subfan S hS hface) x
  refine ⟨_, (Φ.subfan S hS hface).affineToricChartι (hΦ.subfan S hS hface) σ,
    inferInstance, ⟨y, hy⟩, ?_⟩
  rw [affineToricChartι_comp_subfanInclusion_algebraicMap]
  infer_instance

end Fan

end TauCeti.Toric
