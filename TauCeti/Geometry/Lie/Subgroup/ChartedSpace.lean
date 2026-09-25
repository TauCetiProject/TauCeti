/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.TranslatedChart
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Charted spaces on subgroup slices

An ambient chart that identifies a subgroup with the coordinate slice `F × {0}` restricts to a
chart on the subgroup subtype with values in `F`.  Translating one such chart at the identity gives
enough charts to equip the subgroup with a charted-space structure.

The construction is topological.  Its atlas contains exactly the preferred charts obtained by
translating the supplied identity chart; it does not by itself assert smooth compatibility, a
manifold structure, or smoothness of the group operations.

## Main definitions

* `Subgroup.sliceChart` restricts an ambient zero-slice chart to the subgroup subtype.
* `Subgroup.preferredSliceChart` restricts the translated identity chart at a subgroup point.
* `Subgroup.chartedSpaceOfIsSliceChart` equips a subgroup with the resulting charted-space
  structure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* H. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
* `TauCeti.Geometry.Manifold.Boundary.Charts`, for an earlier coordinate-slice restriction
  construction now shared through `OpenPartialHomeomorph.subtypeCoord`.
-/

public section

namespace Subgroup

open Set Topology

variable {G F F' : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

private theorem sliceChart_inv_mem (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    {y : F} (hy : (y, (0 : F')) ∈ e.target) : e.symm (y, 0) ∈ K :=
  (he.mem_iff (e.map_target hy)).2 (by rw [e.right_inv hy]; simp)

private theorem sliceChart_param_proj (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    {x : G} (hx : x ∈ e.source) (hxK : x ∈ K) : ((e x).1, (0 : F')) = e x := by
  have hz := (he.mem_iff hx).1 hxK
  rw [Set.mem_prod] at hz
  rw [← hz.2]

/-- Restrict an ambient chart that flattens a subgroup onto `F × {0}` to a chart on the
subgroup subtype with values in `F`.

Outside the target, the inverse is assigned the subgroup identity.  Its value there is irrelevant
to an open partial homeomorphism. -/
noncomputable def sliceChart (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G)) :
    OpenPartialHomeomorph K F :=
  e.subtypeCoord (K : Set G) inferInstance (fun y : F => (y, (0 : F'))) Prod.fst
    (sliceChart_inv_mem K e he) (sliceChart_param_proj K e he) (fun _ _ => rfl)
    (continuous_id.prodMk continuous_const) continuous_fst.continuousOn

/-- The source of a subgroup slice chart is the part of the subgroup lying in the source of the
ambient chart. -/
@[simp]
theorem sliceChart_source (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G)) :
    (sliceChart K e he).source = Subtype.val ⁻¹' e.source := by
  unfold sliceChart
  exact e.subtypeCoord_source (K : Set G) inferInstance (fun y : F => (y, (0 : F'))) Prod.fst
    (sliceChart_inv_mem K e he) (sliceChart_param_proj K e he) (fun _ _ => rfl)
    (continuous_id.prodMk continuous_const) continuous_fst.continuousOn

/-- The target of a subgroup slice chart consists of the tangential coordinates whose zero-slice
points lie in the target of the ambient chart. -/
@[simp]
theorem sliceChart_target (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G)) :
    (sliceChart K e he).target = (fun y : F => (y, (0 : F'))) ⁻¹' e.target := by
  unfold sliceChart
  exact e.subtypeCoord_target (K : Set G) inferInstance (fun y : F => (y, (0 : F'))) Prod.fst
    (sliceChart_inv_mem K e he) (sliceChart_param_proj K e he) (fun _ _ => rfl)
    (continuous_id.prodMk continuous_const) continuous_fst.continuousOn

/-- A subgroup slice chart reads the tangential coordinate of the ambient chart. -/
@[simp]
theorem sliceChart_apply (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (x : K) :
    sliceChart K e he x = (e x.1).1 := by
  unfold sliceChart
  exact e.subtypeCoord_apply (K : Set G) inferInstance (fun y : F => (y, (0 : F'))) Prod.fst
    (sliceChart_inv_mem K e he) (sliceChart_param_proj K e he) (fun _ _ => rfl)
    (continuous_id.prodMk continuous_const) continuous_fst.continuousOn x

/-- On its target, the inverse of a subgroup slice chart is the ambient inverse evaluated on the
zero slice. -/
@[simp]
theorem coe_sliceChart_symm_apply (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    {y : F} (hy : (y, (0 : F')) ∈ e.target) :
    ((sliceChart K e he).symm y : G) = e.symm (y, 0) := by
  simp only [sliceChart]
  exact e.coe_subtypeCoord_symm_apply (K : Set G) inferInstance
    (fun y : F => (y, (0 : F'))) Prod.fst (sliceChart_inv_mem K e he)
    (sliceChart_param_proj K e he) (fun _ _ => rfl) (continuous_id.prodMk continuous_const)
    continuous_fst.continuousOn hy

section Translation

variable [ContinuousConstSMul G G]

/-- The preferred subgroup chart at `g`, obtained by translating the supplied identity chart and
then restricting it to the subgroup slice. -/
noncomputable def preferredSliceChart (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) : OpenPartialHomeomorph K F :=
  sliceChart K (K.translatedChart e g) (by
    rw [← Subtype.range_coe (s := (K : Set G))]
    exact K.isSliceChart_translatedChart e he g)

/-- The preferred subgroup chart at `g` sees exactly the subgroup points in the source of its
translated ambient chart. -/
@[simp]
theorem preferredSliceChart_source (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) :
    (preferredSliceChart K e he g).source =
      Subtype.val ⁻¹' (K.translatedChart e g).source := by
  simp [preferredSliceChart]

/-- The target of a preferred subgroup chart is the zero-slice part of the original ambient
target. -/
@[simp]
theorem preferredSliceChart_target (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) :
    (preferredSliceChart K e he g).target =
      (fun y : F => (y, (0 : F'))) ⁻¹' e.target := by
  simp [preferredSliceChart]

/-- A preferred subgroup chart first translates its argument back to the identity and then reads
the tangential coordinate of the original ambient chart. -/
@[simp]
theorem preferredSliceChart_apply (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g x : K) :
    preferredSliceChart K e he g x = (e ((g : G)⁻¹ * (x : G))).1 := by
  simp [preferredSliceChart]

/-- On its target, the inverse of a preferred subgroup chart applies the original ambient inverse
on the zero slice and then translates by the chart's base point. -/
@[simp]
theorem coe_preferredSliceChart_symm_apply (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) {y : F} (hy : (y, (0 : F')) ∈ e.target) :
    ((preferredSliceChart K e he g).symm y : G) = (g : G) * e.symm (y, 0) := by
  simp [preferredSliceChart, coe_sliceChart_symm_apply, hy]

/-- One zero-slice chart around the identity equips a subgroup with a charted-space structure.

The atlas is exactly the range of the preferred charts obtained by translating the supplied
identity chart. -/
@[instance_reducible]
noncomputable def chartedSpaceOfIsSliceChart (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ e.source) : ChartedSpace F K := by
  exact
    { atlas := Set.range (preferredSliceChart K e he)
      chartAt := preferredSliceChart K e he
      mem_chart_source := fun x => by
        rw [preferredSliceChart_source]
        exact K.mem_translatedChart_source e h1 x
      chart_mem_atlas := Set.mem_range_self }

/-- The atlas of `chartedSpaceOfIsSliceChart` is exactly the range of its preferred translated
slice charts. -/
@[simp]
theorem chartedSpaceOfIsSliceChart_atlas (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ e.source) :
    @atlas F _ K _ (chartedSpaceOfIsSliceChart K e he h1) =
      Set.range (preferredSliceChart K e he) := by
  unfold chartedSpaceOfIsSliceChart
  rfl

/-- The preferred chart installed by `chartedSpaceOfIsSliceChart` is the translated slice chart at
the given subgroup point. -/
@[simp]
theorem chartedSpaceOfIsSliceChart_chartAt (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ e.source) (g : K) :
    @chartAt F _ K _ (chartedSpaceOfIsSliceChart K e he h1) g =
      preferredSliceChart K e he g := by
  unfold chartedSpaceOfIsSliceChart
  rfl

end Translation

end Subgroup
