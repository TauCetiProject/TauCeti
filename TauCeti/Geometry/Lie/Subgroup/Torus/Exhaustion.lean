/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus.Conjugacy
import TauCeti.Geometry.Lie.Exponential.Surjectivity

/-!
# Exhaustion by maximal tori

Every element of a compact connected finite-dimensional real Lie group lies in a maximal torus.
The conjugates of any fixed maximal torus cover the group. Both statements apply to arbitrary
models with corners and require no chosen Riemannian metric or Hausdorff hypothesis.

## Main results

* `TauCeti.Lie.exists_isMaximalTorus_mem`: every element belongs to a maximal torus.
* `TauCeti.Lie.IsMaximalTorus.iUnion_map_conj_eq_univ`: the conjugates of a fixed maximal torus
  cover the group.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Theorem 4.36, p.202,
  and Corollaries 4.46 and 4.48, p.205. We use the invariant-metric exponential-surjectivity
  theorem, rather than the induction argument of Theorem 4.36.
-/

public section

open scoped ContDiff Manifold
noncomputable section
namespace TauCeti.Lie
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [ConnectedSpace G]

include I in
/-- Every element of a compact connected finite-dimensional real Lie group belongs to a
maximal torus. -/
theorem exists_isMaximalTorus_mem (g : G) :
    ∃ T : Subgroup G, IsMaximalTorus T ∧ g ∈ T := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  -- Cartan's theorem gives the whole subgroup a vector-space model without changing its topology.
  let K : Subgroup G := ⊤
  let L := (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    (I := I) (K := K) (by simp [K])
  let _ : ChartedSpace L K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, L) ∞ K := d.lieGroup
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp
    (by simpa only [K, Subgroup.coe_top] using (isCompact_univ : IsCompact (Set.univ : Set G)))
  let _ : ConnectedSpace K := isConnected_iff_connectedSpace.mp
    (by simpa only [K, Subgroup.coe_top] using (isConnected_univ : IsConnected (Set.univ : Set G)))
  obtain ⟨T, hT⟩ := exists_isMaximalTorus (I := 𝓘(ℝ, L)) (G := K)
  -- Apply compact exponential surjectivity in that boundaryless model.
  have hexp : Function.Surjective (lieExp (I := 𝓘(ℝ, L)) (G := K)) :=
    lieExp_surjective_of_compact_connected
  let k : K := ⟨g, Subgroup.mem_top g⟩
  have hk : k ∈ ⋃ a : K, (T.map (MulAut.conj a).toMonoidHom : Set K) := by
    rw [hT.iUnion_map_conj_eq_range_lieExp (I := 𝓘(ℝ, L))]
    exact Set.mem_range.mpr (hexp k)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hk
  -- Its image in the original group is a torus containing the original element.
  have hmap := (hT.map_conj a).isTorus.map K.subtype continuous_subtype_val
  obtain ⟨S, hS, hle⟩ := hmap.exists_isMaximalTorus_le I
  exact ⟨S, hS, hle ⟨k, ha, rfl⟩⟩

include I in
/-- The conjugates of a maximal torus cover a compact connected finite-dimensional real
Lie group. -/
theorem IsMaximalTorus.iUnion_map_conj_eq_univ {T : Subgroup G} (hT : IsMaximalTorus T) :
    ⋃ a : G, (T.map (MulAut.conj a).toMonoidHom : Set G) = Set.univ := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨S, hS, hg⟩ := exists_isMaximalTorus_mem I g
  obtain ⟨a, ha⟩ := hT.exists_map_conj_eq I hS
  exact Set.mem_iUnion.mpr ⟨a, by rwa [ha]⟩

end TauCeti.Lie
