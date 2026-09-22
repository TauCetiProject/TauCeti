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
# Open subgroups of topologically finitely generated profinite groups

The intersection of a dense finitely generated subgroup with an open subgroup has finite index
in the dense subgroup and remains dense in the open subgroup. Schreier's lemma therefore shows
that every open subgroup of a topologically finitely generated profinite group is itself
topologically finitely generated. This is the qualitative part of the profinite Schreier theorem;
the sharp rank bound is a further step.

## Main results

* `IsTopologicallyFinitelyGenerated.of_openSubgroup`: an open subgroup of a profinite group with
  finitely many topological generators also has finitely many topological generators.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 3.6.3.
* Mathlib's `Subgroup.fg_of_index_ne_zero` and `Subgroup.closure_mul_image_eq`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- An open subgroup of a topologically finitely generated profinite group is topologically
finitely generated. Its dense finitely generated abstract subgroup intersects the given open
subgroup in a finite-index subgroup, to which Schreier's lemma applies. -/
theorem IsTopologicallyFinitelyGenerated.of_openSubgroup
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G) :
    IsTopologicallyFinitelyGenerated (↥U.toSubgroup) := by
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp hG
  let D : Subgroup G := Subgroup.closure (s : Set G)
  have hD : Dense (D : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  let K : Subgroup D := U.toSubgroup.subgroupOf D
  have hKfg : Group.FG K := by
    have hDfg : Group.FG D := Group.closure_finset_fg s
    have hUindex : U.toSubgroup.FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    have hKindex : K.FiniteIndex :=
      @Subgroup.instFiniteIndex_subgroupOf G _ U.toSubgroup D hUindex
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
  have hfrange : DenseRange f := by
    rw [DenseRange, Subtype.dense_iff]
    intro x hx
    have hx' : (x : G) ∈ closure ((D : Set G) ∩ (U : Set G)) := by
      simpa [Set.inter_comm] using hD.open_subset_closure_inter U.isOpen hx
    change (x : G) ∈ closure ((Subtype.val : ↥U.toSubgroup → G) '' Set.range f)
    rw [hrange_coe]
    exact hx'
  obtain ⟨t, htgen, htfin⟩ := Group.fg_iff.mp hKfg
  have hK : IsTopologicallyFinitelyGenerated K := htfin.isTopologicallyFinitelyGenerated <| by
    rw [htgen]
    apply SetLike.coe_injective
    simp [Subgroup.topologicalClosure_coe]
  exact hK.of_denseRange hf hfrange

end TauCeti
