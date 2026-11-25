/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Diagonal

/-!
# Restricted localization of a Selmer structure

If every global class satisfies a family of reference conditions at almost every index, the
localization maps of a Selmer structure assemble into a homomorphism to the corresponding
restricted product. The reference subgroups are caller-chosen: they need not coincide with the
Selmer structure's local conditions. The Selmer group is the pullback of the subgroup cut out by
the local conditions at every coordinate. In particular, choosing the local conditions as the
reference family identifies it with the pullback of the everywhere-integral subgroup.
-/

public noncomputable section

namespace TauCeti.ContCohomology.SelmerStructure

open scoped RestrictedProduct

variable {G : Type*} [Monoid G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {ι : Type*} {H : ι → Type*} [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, IsTopologicalAddGroup (N i)] [∀ i, DistribMulAction (H i) (N i)]
  [∀ i, ContinuousSMul (H i) (N i)]
  (𝓕 : SelmerStructure G M H N) (U : ∀ i, AddSubgroup (H1 (H i) (N i)))
  (h : ∀ c : H1 G M, ∀ᶠ i in Filter.cofinite, 𝓕.localization i c ∈ U i)

/-- The Selmer group is the pullback of the subgroup satisfying every local condition in the
restricted product with the caller's reference family. -/
theorem selmerGroup_eq_comap_addRationalDiagonal :
    𝓕.selmerGroup =
      (integralAddSubgroupOf U 𝓕.localCondition).comap
        (addRationalDiagonal 𝓕.localization U h) := by
  ext c
  simp only [mem_selmerGroup_iff, AddSubgroup.mem_comap, mem_integralAddSubgroupOf,
    addRationalDiagonal_apply]

end TauCeti.ContCohomology.SelmerStructure
