/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Indexed
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Cone
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction
public import TauCeti.Topology.Homotopy.HomotopyGroup.FundamentalGroupAction
public import TauCeti.Topology.Homotopy.Path

/-!
# Weak contractibility of indexed joins

Every map from a compact space into an indexed join uses only finitely many vertices.  If
nonempty members occur at infinitely many indices, a vertex over an unused index turns that
finite restriction into a cone.  This gives a nullhomotopy of the map inside the full join.
Applied to the inclusions of the images of loops and of cubes, it shows that such a join is
weakly contractible.

## Main results

* `TauCeti.isCone_restrict_indexedJoin_insert`: adjoining a vertex over a fresh index makes a
  finite vertex restriction of an indexed join a cone.
* `ContinuousMap.nullhomotopic_to_indexedJoin`: every map with compact image to such an
  indexed join is nullhomotopic.
* `TauCeti.pathConnectedSpace_realization_indexedJoin`: path-connectedness of the indexed join.
* `TauCeti.simplyConnectedSpace_realization_indexedJoin`: simple connectedness.
* `TauCeti.subsingleton_homotopyGroup_realization_indexedJoin`: vanishing homotopy groups.
-/

public section

noncomputable section

open Set Topology
open scoped Topology.Homotopy
open AbstractSimplicialComplex

universe u v w

variable {ι : Type u} {A : ι → Type v}

attribute [local instance] Classical.decEq
attribute [-instance] Sigma.instDecidableEqSigma instDecidableEqSigma

namespace TauCeti

/-- Adjoining a vertex over an index absent from a finite vertex set makes the corresponding
restriction of an indexed join a cone. -/
theorem isCone_restrict_indexedJoin_insert (V : Finset (Σ i, A i)) (i : ι) (a : A i)
    (hi : i ∉ V.image Sigma.fst) :
    PreAbstractSimplicialComplex.IsCone
      ((indexedJoin A).restrict ((V : Set (Σ i, A i)) ∪ {⟨i, a⟩})).toPreAbstractSimplicialComplex
      ⟨⟨i, a⟩, Set.mem_union_right _ (Set.mem_singleton _)⟩ := by
  refine ⟨singleton_mem _ _, fun σ hσ => ?_⟩
  rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
    mem_restrict_iff] at hσ ⊢
  rw [Finset.image_insert]
  by_cases hv : (⟨i, a⟩ : Σ i, A i) ∈ σ.image Subtype.val
  · rwa [Finset.insert_eq_of_mem hv]
  rw [mem_indexedJoin_iff] at hσ ⊢
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  rw [Finset.coe_insert, Set.injOn_insert (Finset.mem_coe.not.mpr hv)]
  refine ⟨hσ.2, ?_⟩
  rintro ⟨w, hw, hwi⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  rcases u.2 with huV | hua
  · exact hi (Finset.mem_image.mpr ⟨u, huV, hwi⟩)
  · exact hv (Finset.mem_image.mpr ⟨u, hu, hua⟩)

end TauCeti

namespace ContinuousMap

open TauCeti

variable {X : Type w} [TopologicalSpace X]

/-- Every continuous map with compact image into an indexed join is nullhomotopic when
nonempty family members occur at infinitely many indices. -/
theorem nullhomotopic_to_indexedJoin
    (f : C(X, (indexedJoin A).Realization))
    (hf : IsCompact (Set.range f))
    (hA : {i | Nonempty (A i)}.Infinite) : f.Nullhomotopic := by
  obtain ⟨V, g, rfl⟩ := (indexedJoin A).exists_finite_restrict_factorization f hf
  obtain ⟨i, ⟨a⟩, hiV⟩ := hA.exists_notMem_finset (V.image Sigma.fst)
  have hVS : (V : Set (Σ i, A i)) ⊆ V ∪ {⟨i, a⟩} := Set.subset_union_left
  have := contractibleSpace_realization_of_isCone (isCone_restrict_indexedJoin_insert V i a hiV)
  rw [← restrictInclusion_comp_restrictInclusionOfSubset _ hVS,
    PreAbstractSimplicialComplex.SimplicialMap.realizationMap_comp, ContinuousMap.comp_assoc]
  -- The middle factor lands in a contractible realization, so it is nullhomotopic.
  exact ((id_nullhomotopic _).comp_left
    (((indexedJoin A).restrictInclusionOfSubset hVS).realizationMap.comp g)).comp_right _

end ContinuousMap

namespace TauCeti

/-- An indexed join is path-connected if nonempty family members occur at infinitely many
indices. -/
theorem pathConnectedSpace_realization_indexedJoin
    (hA : {i | Nonempty (A i)}.Infinite) :
    PathConnectedSpace (indexedJoin A).Realization := by
  constructor
  · obtain ⟨i, hi⟩ := hA.nonempty
    obtain ⟨a⟩ := hi
    exact ⟨(indexedJoin A).vertex ⟨i, a⟩⟩
  · intro x y
    let f : C(Bool, (indexedJoin A).Realization) :=
      ⟨fun b => if b then y else x, continuous_of_discreteTopology⟩
    obtain ⟨c, ⟨H⟩⟩ := ContinuousMap.nullhomotopic_to_indexedJoin f
      (isCompact_range f.continuous) hA
    refine ⟨(H.evalAt false).trans (H.evalAt true).symm⟩

/-- An indexed join is simply connected if nonempty family members occur at infinitely many
indices. -/
theorem simplyConnectedSpace_realization_indexedJoin
    (hA : {i | Nonempty (A i)}.Infinite) :
    SimplyConnectedSpace (indexedJoin A).Realization := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨pathConnectedSpace_realization_indexedJoin hA, fun x γ => ?_⟩
  refine Path.Homotopic.refl_of_forall_mem_of_nullhomotopic
    (ContinuousMap.nullhomotopic_to_indexedJoin _ ?_ hA) γ Set.mem_range_self
  rw [ContinuousMap.coe_mk, Subtype.range_coe]
  exact isCompact_range γ.continuous

/-- Every positive-dimensional homotopy group of an indexed join is trivial if nonempty family
members occur at infinitely many indices. -/
theorem subsingleton_homotopyGroup_realization_indexedJoin
    (hA : {i | Nonempty (A i)}.Infinite) (N : Type*) [Finite N] [Nonempty N]
    (x : (indexedJoin A).Realization) :
    Subsingleton (HomotopyGroup N (indexedJoin A).Realization x) := by
  classical
  let _ : Fintype N := Fintype.ofFinite N
  let _ : SimplyConnectedSpace (indexedJoin A).Realization :=
    simplyConnectedSpace_realization_indexedJoin hA
  have h_one : ∀ a : HomotopyGroup N (indexedJoin A).Realization x, a = 1 := by
    intro a
    induction a using Quotient.inductionOn with | h p =>
    have hp : IsCompact (Set.range (Subtype.val : Set.range p → _)) := by
      rw [Subtype.range_coe]
      exact isCompact_range p.1.continuous
    obtain ⟨g, hg⟩ := one_mem_orbit_of_forall_mem_of_nullhomotopic
      (ContinuousMap.nullhomotopic_to_indexedJoin _ hp hA) p Set.mem_range_self
    exact (fundamentalGroup_smul_eq_self g _).symm.trans hg
  exact ⟨fun a b => (h_one a).trans (h_one b).symm⟩

end TauCeti
