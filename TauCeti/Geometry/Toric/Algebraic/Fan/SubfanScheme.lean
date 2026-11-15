/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import TauCeti.Geometry.Toric.Algebraic.Fan.Preimage
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

/-!
# The open subscheme associated to a subfan

A collection of cones of a finite fan that is closed under faces determines an open
subscheme of the fan's toric scheme. On each cone chart, the inclusion is the usual chart
inclusion. This supplies the algebraic open-subfan restriction used by toric chart gluing and
comparison with complex points.

A toric map restricts to open subfans. For a morphism of finite fans and a face-closed subfan
of the target, the toric scheme of the preimage subfan is the inverse image of the open subscheme
of the target subfan, and the restricted toric map is its base change: the square formed by the
two toric maps and the two open-subfan inclusions is a pullback of schemes. The proof is
chartwise. If a point of the chart of a source cone `σ` lands in the chart of a target cone `τ`,
then its image lies in the chart of the face `υ ⊓ τ` of the least target cone `υ` of `σ`. That
face is cut out of `υ` by a character, and the pullback of this character cuts out a face of `σ`
whose chart contains the point and whose least target cone is a face of `τ`. No regularity
assumption is needed.

## Main declarations

* `TauCeti.Toric.Fan.isOpenImmersion_subfanInclusion_algebraicMap`: the toric scheme of a subfan
  is an open subscheme, with image `TauCeti.Toric.Fan.range_subfanInclusion_algebraicMap`.
* `TauCeti.Toric.FanHom.preimageSubfanAlgebraicMap_comp_algebraicMap`: restriction to a preimage
  subfan commutes with the ambient toric map.
* `TauCeti.Toric.FanHom.range_preimageSubfanAlgebraicMap`: the open subscheme of the preimage
  subfan is the inverse image of the open subscheme of the target subfan.
* `TauCeti.Toric.FanHom.isPullback_preimageSubfan_algebraicMap`: the restriction square is a
  pullback of schemes.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

namespace Fan

/-- For a cone of a subfan, the affine chart map induced by the subfan inclusion, followed by the
ambient chart inclusion at the least containing cone, is the ambient chart inclusion of that
cone. -/
@[reassoc (attr := simp)]
theorem subfanInclusion_affineToricChartMap_comp_affineToricChartι
    (σ : (Φ.subfan S hS hface).cones) :
    (Φ.subfanInclusion S hS hface).affineToricChartMap σ ≫
      Φ.affineToricChartι ⟨(Φ.subfanInclusion S hS hface).leastCone σ.2,
        (Φ.subfanInclusion S hS hface).leastCone_mem σ.2⟩ =
      Φ.affineToricChartι ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩ := by
  let f := Φ.subfanInclusion S hS hface
  -- The let-bound `f` is definitionally the subfan inclusion.
  have hleast : f.leastCone σ.2 = σ.1 :=
    subfanInclusion_leastCone Φ S hS hface σ
  have hσleast : σ.1.IsFaceOf (f.leastCone σ.2) := by
    rw [hleast]
  have hmap : f.affineToricChartMap σ =
      faceAffineToricSchemeMap Φ.lattice hσleast := by
    rw [FanHom.affineToricChartMap_def, faceAffineToricSchemeMap_eq_affineToricSchemeMap]
    simp only [f, subfanInclusion_latticeMap, subfanInclusion_realMap]
  rw [hmap]
  exact faceAffineToricSchemeMap_comp_affineToricChartι
    (τ := ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩)
    (σ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩) hσleast

/-- On every affine cone chart, the map of toric schemes induced by a subfan inclusion is the
ordinary inclusion of that chart into the ambient fan scheme. -/
@[reassoc]
theorem affineToricChartι_comp_subfanInclusion_algebraicMap
    (σ : (Φ.subfan S hS hface).cones) :
    (Φ.subfan S hS hface).affineToricChartι σ ≫
      (Φ.subfanInclusion S hS hface).algebraicMap =
      Φ.affineToricChartι ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩ := by
  simp

/-- The map of algebraic realizations induced by a subfan inclusion is injective on points. -/
theorem subfanInclusion_algebraicMap_injective :
    Function.Injective (Φ.subfanInclusion S hS hface).algebraicMap := by
  intro x y hxy
  obtain ⟨σ, a, rfl⟩ :=
    (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq x
  obtain ⟨τ, b, rfl⟩ :=
    (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq y
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    affineToricChartι_comp_subfanInclusion_algebraicMap,
    affineToricChartι_comp_subfanInclusion_algebraicMap] at hxy
  apply ((Φ.subfan S hS hface).affineToricChartι_eq_affineToricChartι_iff a b).2
  obtain ⟨z, hza, hzb⟩ :=
    (Φ.affineToricChartι_eq_affineToricChartι_iff
      (σ := ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩)
      (τ := ⟨τ.1, hS (by simpa only [subfan_cones] using τ.2)⟩) a b).1 hxy
  refine ⟨z, ?_, ?_⟩
  · simpa only [Fan.affineToricOverlapLeft_def, subfan_lattice] using hza
  · simpa only [Fan.affineToricOverlapRight_def, subfan_lattice] using hzb

/-- The image of a subfan's algebraic realization is the union of its cone charts in the
ambient fan scheme. -/
theorem range_subfanInclusion_algebraicMap :
    Set.range (Φ.subfanInclusion S hS hface).algebraicMap =
      ⋃ σ : (Φ.subfan S hS hface).cones,
        Set.range (Φ.affineToricChartι
          ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨σ, z, rfl⟩ :=
      (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq y
    refine Set.mem_iUnion.mpr ⟨σ, ⟨z, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, affineToricChartι_comp_subfanInclusion_algebraicMap]
  · intro hx
    obtain ⟨σ, z, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(Φ.subfan S hS hface).affineToricChartι σ z, ?_⟩
    rw [← Scheme.Hom.comp_apply, affineToricChartι_comp_subfanInclusion_algebraicMap]

/-- A face-closed subfan of a finite fan defines an open subscheme of its algebraic
toric variety. Its map to the ambient scheme is the toric map induced by the inclusion of fans. -/
instance isOpenImmersion_subfanInclusion_algebraicMap :
    IsOpenImmersion (Φ.subfanInclusion S hS hface).algebraicMap := by
  apply IsOpenImmersion.of_forall_source_exists _
    (Φ.subfanInclusion_algebraicMap_injective S hS hface)
  intro x
  obtain ⟨σ, y, hy⟩ :=
    (Φ.subfan S hS hface).exists_affineToricChartι_apply_eq x
  refine ⟨_, (Φ.subfan S hS hface).affineToricChartι σ,
    inferInstance, ⟨y, hy⟩, ?_⟩
  rw [affineToricChartι_comp_subfanInclusion_algebraicMap]
  infer_instance

end Fan

end TauCeti.Toric

/-! ### Restricting toric maps to open subfans -/

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (f : FanHom Φ Ψ) (S : Set (PointedCone ℝ V')) (hS : S ⊆ Ψ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

/-- Restricting an algebraic toric map to the preimage of an open subfan commutes with the two
open-subfan inclusions. -/
@[reassoc]
theorem preimageSubfanAlgebraicMap_comp_algebraicMap :
    (Φ.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
          (f.preimageCones_closedUnderFaces S hface)).algebraicMap ≫ f.algebraicMap =
      (f.restrictToPreimage S hS hface).algebraicMap ≫
        (Ψ.subfanInclusion S hS hface).algebraicMap := by
  rw [← algebraicMap_comp, ← algebraicMap_comp, subfanInclusion_comp_restrictToPreimage]

/-- If the algebraic toric map sends a point of the chart of `σ` into the chart of a target cone
`τ`, then that point lies in the chart of a face of `σ` whose least target cone is a face of
`τ`. -/
private theorem exists_affineToricChartι_eq_of_algebraicMap_mem (σ : Φ.cones)
    (y : Φ.affineToricChart σ) (τ : Ψ.cones)
    (hy : f.algebraicMap (Φ.affineToricChartι σ y) ∈ Set.range (Ψ.affineToricChartι τ)) :
    ∃ (σ' : Φ.cones) (y' : Φ.affineToricChart σ'),
      Φ.affineToricChartι σ' y' = Φ.affineToricChartι σ y ∧
        (f.leastCone σ'.2).IsFaceOf τ.1 := by
  let υ : Ψ.cones := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
  have hυ := Ψ.isToricCone υ.2
  -- The image lies in the chart of `υ ⊓ τ`, which is cut out of the chart of `υ` by a character.
  obtain ⟨m, hm, hmυτ⟩ := hυ.rational.exists_mem_dualSemigroup_inf_ker_eq Ψ.lattice
    (Ψ.inf_isFaceOf_left υ.2 τ.2)
  have hρ : (υ.1 ⊓ PointedCone.ofSubmodule (LinearMap.ker (Ψ.lattice.realCharacter m))).IsFaceOf
      υ.1 := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup Ψ.lattice m).1 hm)
  have hy' : f.affineToricChartMap σ y ∈ Set.range (faceAffineToricSchemeMap Ψ.lattice hρ) := by
    rw [← Scheme.Hom.comp_apply, affineToricChartι_comp_algebraicMap, Scheme.Hom.comp_apply]
      at hy
    have hυτ : Ψ.affineToricChartι υ (f.affineToricChartMap σ y) ∈
        Set.range (Ψ.affineToricChartι (υ ⊓ τ)) := by
      rw [← Fan.range_affineToricChartι_inter_range_affineToricChartι]
      exact ⟨⟨_, rfl⟩, hy⟩
    have hinf : υ ⊓ τ = ⟨_, Ψ.mem_of_isFaceOf υ.2 hρ⟩ := Subtype.ext hmυτ.symm
    rw [hinf, ← Fan.faceAffineToricSchemeMap_comp_affineToricChartι hρ] at hυτ
    obtain ⟨z, hz⟩ := hυτ
    rw [Scheme.Hom.comp_apply] at hz
    exact ⟨z, (Ψ.affineToricChartι υ).isOpenEmbedding.injective hz⟩
  -- Pulling back along the affine chart map, `y` lies in the chart of the face of `σ` cut out
  -- by the pullback of that character.
  have hmaps : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V') :=
    fun x hx ↦ f.map_le_leastCone σ.2 ⟨x, hx, rfl⟩
  rw [← Set.mem_preimage, affineToricChartMap_def,
    preimage_range_faceAffineToricSchemeMap_inf_ker Φ.lattice Ψ.lattice _ _ _ hmaps
      (Φ.isToricCone σ.2).fg hυ.fg ⟨m, hm⟩] at hy'
  obtain ⟨y', hy'⟩ := hy'
  have hσ' := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup Φ.lattice _).1
    (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps
      ⟨m, hm⟩).2)
  refine ⟨⟨_, Φ.mem_of_isFaceOf σ.2 hσ'⟩, y', ?_, ?_⟩
  · rw [← hy', ← Scheme.Hom.comp_apply,
      Fan.faceAffineToricSchemeMap_comp_affineToricChartι (τ := ⟨_, Φ.mem_of_isFaceOf σ.2 hσ'⟩)]
  -- The face of `σ` maps into `υ ⊓ ker m = υ ⊓ τ`, so its least target cone is a face of `τ`.
  have hle : f.leastCone (Φ.mem_of_isFaceOf σ.2 hσ') ≤ υ.1 ⊓ τ.1 := by
    rw [← hmυτ]
    refine f.leastCone_le _ (Ψ.mem_of_isFaceOf υ.2 hρ) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨f.mapsTo_leastCone σ.2 hx.1, ?_⟩
    have hx₂ := LinearMap.mem_ker.1 hx.2
    rwa [coe_dualSemigroupMap,
      Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap f.realMap f.map_lattice] at hx₂
  exact (Ψ.isFaceOf_of_le (Ψ.inf_mem υ.2 τ.2) (f.leastCone_mem _) hle).trans
    (Ψ.inf_isFaceOf_right υ.2 τ.2)

/-- The open subscheme of the preimage subfan is exactly the inverse image of the open subscheme
of the target subfan under the algebraic toric map. -/
theorem range_preimageSubfanAlgebraicMap :
    Set.range (Φ.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
        (f.preimageCones_closedUnderFaces S hface)).algebraicMap =
      f.algebraicMap ⁻¹' Set.range (Ψ.subfanInclusion S hS hface).algebraicMap := by
  rw [Fan.range_subfanInclusion_algebraicMap, Fan.range_subfanInclusion_algebraicMap]
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨σ, y, rfl⟩
    have hσ := f.preimageSubfan_cones_subset S hface σ.2
    have hleast := (f.mem_preimageCones_iff S hσ).1 (by simpa only [Fan.subfan_cones] using σ.2)
    refine ⟨⟨f.leastCone hσ, by simpa only [Fan.subfan_cones] using hleast⟩,
      f.affineToricChartMap ⟨σ.1, hσ⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, affineToricChartι_comp_algebraicMap]
  · rintro ⟨τ, hx⟩
    obtain ⟨σ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
    have hτ : τ.1 ∈ S := by simpa only [Fan.subfan_cones] using τ.2
    obtain ⟨σ', y', hy', hσ'⟩ :=
      f.exists_affineToricChartι_eq_of_algebraicMap_mem σ y ⟨τ.1, hS hτ⟩ hx
    exact ⟨⟨σ'.1, by
      simpa only [Fan.subfan_cones] using
        (f.mem_preimageCones_iff S σ'.2).2 (hface hτ hσ')⟩, y', hy'⟩

/-- Restriction to an open subfan is a base change: the toric scheme of the preimage subfan is
the pullback of the open subscheme of the target subfan along the algebraic toric map. -/
theorem isPullback_preimageSubfan_algebraicMap :
    IsPullback
      (Φ.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
        (f.preimageCones_closedUnderFaces S hface)).algebraicMap
      (f.restrictToPreimage S hS hface).algebraicMap
      f.algebraicMap (Ψ.subfanInclusion S hS hface).algebraicMap :=
  (IsOpenImmersion.isPullback _ _ _ _ (f.preimageSubfanAlgebraicMap_comp_algebraicMap S hS hface)
    (TopologicalSpace.Opens.ext (f.range_preimageSubfanAlgebraicMap S hS hface).symm)).flip

end TauCeti.Toric.FanHom
