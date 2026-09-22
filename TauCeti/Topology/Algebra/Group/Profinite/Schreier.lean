/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Schreier
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Generation

/-!
# Open finite-index subgroups of topologically finitely generated groups

Every open finite-index subgroup of a topologically finitely generated group is itself
topologically finitely generated. In particular, this applies to open subgroups of compact
topological groups. This is the qualitative part of the profinite Schreier theorem; the sharp rank
bound is a further step.

## Main results

* `IsTopologicallyFinitelyGenerated.of_openSubgroup_of_finiteIndex`: an open finite-index
  subgroup of a topologically finitely generated group is topologically finitely generated.
* `IsTopologicallyFinitelyGenerated.of_openSubgroup`: an open subgroup of a compact topological
  group with finitely many topological generators is topologically finitely generated.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 3.6.3.
* Mathlib's `Subgroup.fg_of_index_ne_zero` and
  `DenseRange.subset_closure_image_preimage_of_isOpen`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open finite-index subgroup of a topologically finitely generated group is topologically
finitely generated. -/
theorem IsTopologicallyFinitelyGenerated.of_openSubgroup_of_finiteIndex
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G)
    [hUindex : U.toSubgroup.FiniteIndex] :
    IsTopologicallyFinitelyGenerated (↥U.toSubgroup) := by
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp hG
  let D : Subgroup G := Subgroup.closure (s : Set G)
  have hD : Dense (D : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  let K : Subgroup D := U.toSubgroup.subgroupOf D
  have hKfg : Group.FG K := by
    have hDfg : Group.FG D := Group.closure_finset_fg s
    have hKindex : K.FiniteIndex :=
      @Subgroup.instFiniteIndex_subgroupOf G _ U.toSubgroup D inferInstance
    exact @Subgroup.fg_of_index_ne_zero D _ K hDfg hKindex
  let f : K →* ↥U.toSubgroup :=
    { toFun := fun x => ⟨(x : D), x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    -- The codomain topology on the open subgroup is induced from `G`.
    change Continuous (fun x : K => (x : G))
    exact continuous_subtype_val.comp continuous_subtype_val
  have hfrange : DenseRange f := by
    rw [DenseRange, Subtype.dense_iff]
    intro x hx
    have hx' : (x : G) ∈ closure ((D : Set G) ∩ (U : Set G)) := by
      simpa only [Set.image_preimage_eq_inter_range, Subtype.range_coe,
        Set.inter_comm] using
          hD.denseRange_val.subset_closure_image_preimage_of_isOpen U.isOpen hx
    have hrange_coe : (Subtype.val : ↥U.toSubgroup → G) '' Set.range f =
        (D : Set G) ∩ (U : Set G) := by
      ext g
      constructor
      · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
        exact ⟨y.1.2, y.2⟩
      · rintro ⟨hgD, hgU⟩
        refine ⟨⟨g, hgU⟩, ?_, rfl⟩
        refine ⟨⟨⟨g, hgD⟩, hgU⟩, ?_⟩
        exact Subtype.ext rfl
    rw [← hrange_coe] at hx'
    exact hx'
  obtain ⟨t, htgen, htfin⟩ := Group.fg_iff.mp hKfg
  have hK : IsTopologicallyFinitelyGenerated K := htfin.isTopologicallyFinitelyGenerated <| by
    rw [htgen]
    apply SetLike.coe_injective
    simp [Subgroup.topologicalClosure_coe]
  exact hK.of_denseRange hf hfrange

/-- An open subgroup of a topologically finitely generated compact topological group is
topologically finitely generated. -/
theorem IsTopologicallyFinitelyGenerated.of_openSubgroup [CompactSpace G]
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G) :
    IsTopologicallyFinitelyGenerated (↥U.toSubgroup) := by
  have hUindex : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact hG.of_openSubgroup_of_finiteIndex (U := U) (hUindex := hUindex)

end TauCeti
