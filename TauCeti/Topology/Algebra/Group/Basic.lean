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
submonoid, so the subgroup instances are registered separately. Likewise, every `SubgroupClass`
subobject of a topological group inherits `IsTopologicalGroup`.

In a Hausdorff magma with separately continuous multiplication the center is closed, next to
Mathlib's `Set.isClosed_centralizer`: each defining identity of a central element is an
equality of continuous functions of it.

Over a compact subset of a topological group, conjugation is equicontinuous at the identity: for
every identity neighbourhood `U`, a smaller identity neighbourhood `V` satisfies
`x * y * x⁻¹ ∈ U` for all `x` in the compact set and `y ∈ V`.

If the quotient `(x, y) ↦ u₁ x / u₂ y` of two maps from nonempty spaces is continuous, each map is
continuous, being recovered from it by fixing the other variable.

## Main results

* `Subgroup.separatelyContinuousMul`: a subgroup inherits `SeparatelyContinuousMul`.
* `Subgroup.continuousMul`: a subgroup inherits `ContinuousMul`, without continuity of inversion.
* `SubgroupClass.isTopologicalGroup` / `AddSubgroupClass.isTopologicalAddGroup`: every
  `SubgroupClass` (or `AddSubgroupClass`) subobject of a topological group inherits
  `IsTopologicalGroup` (or `IsTopologicalAddGroup`).
* `Set.isClosed_center`: the center of a Hausdorff magma with separately continuous
  multiplication is closed.
* `IsCompact.exists_nhds_one_conj_subset` / `IsCompact.exists_nhds_zero_conj_subset`:
  equicontinuity of conjugation over a compact set at the identity.
* `TauCeti.continuous_and_continuous_of_continuous_div` /
  `TauCeti.continuous_and_continuous_of_continuous_sub`: maps whose quotient (or difference) on a
  product of nonempty spaces is continuous are continuous.
-/

public section

/-- In a Hausdorff magma with separately continuous multiplication, the center is closed. -/
theorem Set.isClosed_center (M : Type*) [Mul M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (Set.center M) := by
  simp only [Set.center, isMulCentral_iff, commute_iff_eq, Set.ofPred_and, Set.ofPred_forall]
  refine .inter ?_ (.inter ?_ ?_) <;> repeat' refine isClosed_iInter fun _ ↦ ?_
  all_goals apply isClosed_eq <;> fun_prop

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

-- Prefer subclasses of `IsTopologicalGroup` over `SubgroupClass`, matching `SubgroupClass.toGroup`.
/-- Every subgroup-like subobject of a topological group is a topological group for the subspace
topology. -/
@[to_additive /-- Every additive-subgroup-like subobject of a topological additive group is a
topological additive group for the subspace topology. -/]
instance (priority := 75) SubgroupClass.isTopologicalGroup {G S : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SetLike S G] [SubgroupClass S G] (s : S) :
    IsTopologicalGroup s :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubmonoidClass.subtype s)

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

namespace TauCeti

/-- If `(x, y) ↦ u₁ x / u₂ y` is continuous on a product of nonempty spaces, then `u₁` and `u₂`
are continuous. -/
@[to_additive /-- If `(x, y) ↦ u₁ x - u₂ y` is continuous on a product of nonempty spaces, then
`u₁` and `u₂` are continuous. -/]
theorem continuous_and_continuous_of_continuous_div {X Y G : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [Nonempty Y] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {u₁ : X → G} {u₂ : Y → G}
    (h : Continuous fun p : X × Y ↦ u₁ p.1 / u₂ p.2) : Continuous u₁ ∧ Continuous u₂ := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  exact ⟨((h.comp (continuous_id.prodMk (continuous_const (y := y₀)))).mul
      (continuous_const (y := u₂ y₀))).congr fun x ↦ div_mul_cancel (u₁ x) (u₂ y₀),
    ((h.comp ((continuous_const (y := x₀)).prodMk continuous_id)).inv.mul
      (continuous_const (y := u₁ x₀))).congr fun y ↦ by simp⟩

end TauCeti
