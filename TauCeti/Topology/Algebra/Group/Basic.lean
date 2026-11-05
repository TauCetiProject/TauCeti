/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuous multiplication on subgroups, closed centers, and compact conjugation

A subgroup inherits continuous or separately continuous multiplication for the subspace topology.
Mathlib provides these instances for submonoids, but instance search does not see a subgroup as a
submonoid, so the subgroup instances are registered separately.

In a Hausdorff semigroup with separately continuous multiplication the center is the centralizer
of everything, so it is closed, next to Mathlib's `Set.isClosed_centralizer`.

Over a compact subset of a topological group, conjugation is equicontinuous at the identity: for
every identity neighbourhood `U`, a smaller identity neighbourhood `V` satisfies
`x * y * x⁻¹ ∈ U` for all `x` in the compact set and `y ∈ V`.

## Main results

* `Subgroup.separatelyContinuousMul`: a subgroup inherits `SeparatelyContinuousMul`.
* `Subgroup.continuousMul`: a subgroup inherits `ContinuousMul`, without continuity of inversion.
* `Set.isClosed_center`: the center of a Hausdorff semigroup with separately continuous
  multiplication is closed.
* `IsCompact.exists_nhds_one_conj_subset` / `IsCompact.exists_nhds_zero_conj_subset`:
  equicontinuity of conjugation over a compact set at the identity.
-/

public section

/-- In a Hausdorff semigroup with separately continuous multiplication, the center is closed. -/
theorem Set.isClosed_center (M : Type*) [Semigroup M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (Set.center M) := by
  rw [← Set.centralizer_univ]
  exact Set.isClosed_centralizer _

/-- A subgroup of a group with continuous multiplication has continuous multiplication. -/
@[to_additive /-- An additive subgroup of an additive group with continuous addition has
continuous addition. -/]
instance Subgroup.continuousMul {G : Type*} [TopologicalSpace G] [Group G]
    [ContinuousMul G] (S : Subgroup G) : ContinuousMul S :=
  S.toSubmonoid.continuousMul

/-- A subgroup of a group with separately continuous multiplication has separately continuous
multiplication. -/
@[to_additive /-- An additive subgroup of an additive group with separately continuous addition has
separately continuous addition. -/]
instance Subgroup.separatelyContinuousMul {G : Type*} [TopologicalSpace G] [Group G]
    [SeparatelyContinuousMul G] (S : Subgroup G) : SeparatelyContinuousMul S :=
  S.toSubmonoid.separatelyContinuousMul

section

open Filter Set
open scoped Topology

/-- Over a compact subset `C` of a topological group, conjugation sends a sufficiently small
identity neighbourhood into any prescribed identity neighbourhood. -/
@[to_additive /-- Over a compact subset `C` of a topological additive group, conjugation sends a
sufficiently small neighbourhood of zero into any prescribed neighbourhood of zero. -/]
theorem IsCompact.exists_nhds_one_conj_subset {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {C U : Set G} (hC : IsCompact C) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ C, ∀ y ∈ V, x * y * x⁻¹ ∈ U := by
  let φ : G × G → G := fun p ↦ p.1 * p.2 * p.1⁻¹
  have hφ : Continuous φ := IsTopologicalGroup.continuous_conj_prod
  have hsub : C ×ˢ ({1} : Set G) ⊆ φ ⁻¹' interior U := by
    rintro ⟨x, y⟩ ⟨_, hy⟩
    simp only [mem_singleton_iff] at hy
    simpa [φ, hy] using mem_interior_iff_mem_nhds.mpr hU
  obtain ⟨A, B, _, hBo, hCA, h1B, hAB⟩ :=
    generalized_tube_lemma hC isCompact_singleton (isOpen_interior.preimage hφ) hsub
  refine ⟨B, hBo.mem_nhds (singleton_subset_iff.mp h1B), fun x hx y hy ↦ ?_⟩
  exact interior_subset (mem_preimage.mp (hAB (mk_mem_prod (hCA hx) hy)))

end
