/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.TranslatedChart

/-!
# Charted spaces on subgroup slices

An ambient chart that identifies a subgroup with the coordinate slice `F × {0}` can first be
translated from the identity to any subgroup point and then restricted to the subgroup subtype with
values in `F`. These preferred charts equip the subgroup with a charted-space structure.

The construction is topological.  Its atlas contains exactly the preferred charts obtained by
translating the supplied identity chart; it does not by itself assert smooth compatibility, a
manifold structure, or smoothness of the group operations.

## Main definitions

* `Subgroup.preferredSliceChart` restricts the translated identity chart at a subgroup point.
* `Subgroup.chartedSpaceOfIsSliceChart` equips a subgroup with the resulting charted-space
  structure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* H. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

namespace Subgroup

open Set Topology

variable {G F F' : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

section Translation

variable [ContinuousConstSMul G G]

/-- The preferred subgroup chart at `g`: the slice chart of the subgroup induced by the given
ambient chart translated by `g`, as a linear slice chart of the family of all translates. -/
noncomputable def preferredSliceChart (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) : OpenPartialHomeomorph K F :=
  TauCeti.linearSliceChart
    (fun g : K ↦ (Homeomorph.smul (g : G)).symm.transOpenPartialHomeomorph e)
    (K.isSliceChart_smul_symm_transOpenPartialHomeomorph e he) g

/-- The preferred subgroup chart at `g` sees exactly the subgroup points in the source of its
translated ambient chart. -/
@[simp]
theorem preferredSliceChart_source (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) :
    (preferredSliceChart K e he g).source =
      Subtype.val ⁻¹'
        ((Homeomorph.smul (g : G)).symm.transOpenPartialHomeomorph e).source :=
  TauCeti.linearSliceChart_source _ _ g

/-- The target of a preferred subgroup chart is the zero-slice part of the original ambient
target. -/
@[simp]
theorem preferredSliceChart_target (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) :
    (preferredSliceChart K e he g).target =
      (fun y : F => (y, (0 : F'))) ⁻¹' e.target := by
  rw [preferredSliceChart, TauCeti.linearSliceChart_target,
    Homeomorph.transOpenPartialHomeomorph_target]

/-- A preferred subgroup chart first translates its argument back to the identity and then reads
the tangential coordinate of the original ambient chart. -/
@[simp]
theorem preferredSliceChart_apply (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g x : K) :
    preferredSliceChart K e he g x = (e ((g : G)⁻¹ * (x : G))).1 := by
  rw [preferredSliceChart, TauCeti.linearSliceChart_apply,
    Homeomorph.transOpenPartialHomeomorph_apply]
  rfl

/-- On its source, a preferred subgroup chart recovers the translated ambient coordinates by
reinserting the zero transverse coordinate. -/
theorem preferredSliceChart_mk_zero_eq (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) {x : K} (hx : x ∈ (preferredSliceChart K e he g).source) :
    (preferredSliceChart K e he g x, (0 : F')) = e ((g : G)⁻¹ * (x : G)) := by
  have h := TauCeti.linearSliceChart_mk_zero_eq _ _ g hx
  rwa [Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply,
    Homeomorph.smul_symm_apply, smul_eq_mul] at h

/-- On its target, the inverse of a preferred subgroup chart applies the original ambient inverse
on the zero slice and then translates by the chart's base point. -/
@[simp]
theorem coe_preferredSliceChart_symm_apply (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g : K) {y : F} (hy : (y, (0 : F')) ∈ e.target) :
    ((preferredSliceChart K e he g).symm y : G) = (g : G) * e.symm (y, 0) := by
  rw [preferredSliceChart, TauCeti.coe_linearSliceChart_symm_apply _ _ g (by simpa using hy),
    Homeomorph.transOpenPartialHomeomorph_symm_apply]
  rfl

/-- One zero-slice chart around the identity equips a subgroup with a charted-space structure:
the linear-slice charted space of the family of translates of the chart.

The atlas is exactly the range of the preferred charts obtained by translating the supplied
identity chart. -/
@[instance_reducible]
noncomputable def chartedSpaceOfIsSliceChart (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ e.source) : ChartedSpace F K :=
  TauCeti.linearSliceChartedSpace
    (fun g : K ↦ (Homeomorph.smul (g : G)).symm.transOpenPartialHomeomorph e)
    (K.isSliceChart_smul_symm_transOpenPartialHomeomorph e he) fun g ↦ by
      rw [Homeomorph.transOpenPartialHomeomorph_source]
      simpa [Homeomorph.smul_symm_apply, smul_eq_mul] using h1

/-- The atlas of `chartedSpaceOfIsSliceChart` is exactly the range of its preferred translated
slice charts. -/
@[simp]
theorem chartedSpaceOfIsSliceChart_atlas (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ e.source) :
    @atlas F _ K _ (chartedSpaceOfIsSliceChart K e he h1) =
      Set.range (preferredSliceChart K e he) :=
  TauCeti.linearSliceChartedSpace_atlas _ _ _

/-- The preferred chart installed by `chartedSpaceOfIsSliceChart` is the translated slice chart at
the given subgroup point. -/
@[simp]
theorem chartedSpaceOfIsSliceChart_chartAt (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ e.source) (g : K) :
    @chartAt F _ K _ (chartedSpaceOfIsSliceChart K e he h1) g =
      preferredSliceChart K e he g :=
  TauCeti.linearSliceChartedSpace_chartAt _ _ _ g

end Translation

end Subgroup
