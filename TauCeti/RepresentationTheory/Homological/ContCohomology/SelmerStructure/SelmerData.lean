/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SelmerData
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Basic

/-!
# Discrete Selmer structures as Selmer data over `ℤ`

A Selmer structure `𝓕` on a discrete `G`-module `M` localises `H¹(G, M)` to the groups
`H¹(H i, N i)` and imposes subgroup conditions there. Viewing these abelian groups as
`ℤ`-modules gives Selmer data over `ℤ` (`TauCeti.SelmerData`) with the same localisation maps
and conditions, whose Selmer module is the Selmer group of `𝓕`. Replacing the local conditions
commutes with this passage. So the module-theoretic operations of `TauCeti.SelmerData`
(relaxed and strict conditions, the kernel description) apply to the discrete Selmer groups
without a second discrete carrier.

## Main definitions

* `TauCeti.ContCohomology.SelmerStructure.toSelmerData`: the Selmer data over `ℤ` of a Selmer
  structure.

## Main results

* `TauCeti.ContCohomology.SelmerStructure.selmerModule_toSelmerData`: its Selmer module is the
  Selmer group.
* `TauCeti.ContCohomology.SelmerStructure.toSelmerData_withLocalConditions` and
  `TauCeti.ContCohomology.SelmerStructure.toSelmerData_relax`: compatibility with replacing and
  relaxing the local conditions.
* `TauCeti.ContCohomology.SelmerStructure.selmerGroup_le_relax` and
  `TauCeti.ContCohomology.SelmerStructure.mem_selmerGroup_relax_iff`: derived from `SelmerData`.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.5.
-/

public section

noncomputable section

namespace TauCeti.ContCohomology.SelmerStructure

variable {G : Type*} [Monoid G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {ι : Type*} {H : ι → Type*} [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, IsTopologicalAddGroup (N i)] [∀ i, DistribMulAction (H i) (N i)]
  [∀ i, ContinuousSMul (H i) (N i)]
  (𝓕 : SelmerStructure G M H N)

/-- **The Selmer data over `ℤ` of a Selmer structure**: the localisation maps
`H¹(G, M) → H¹(H i, N i)` and the local conditions, viewed as `ℤ`-linear maps and
`ℤ`-submodules. -/
def toSelmerData : SelmerData ℤ ι (H1 G M) fun i => H1 (H i) (N i) where
  localization i := (𝓕.localization i).toIntLinearMap
  localCondition i := (𝓕.localCondition i).toIntSubmodule

/-- The localisation maps of `𝓕.toSelmerData` are those of `𝓕`. -/
@[simp]
theorem toSelmerData_localization (i : ι) :
    𝓕.toSelmerData.localization i = (𝓕.localization i).toIntLinearMap :=
  (rfl)

/-- The local conditions of `𝓕.toSelmerData` are those of `𝓕`. -/
@[simp]
theorem toSelmerData_localCondition (i : ι) :
    𝓕.toSelmerData.localCondition i = (𝓕.localCondition i).toIntSubmodule :=
  (rfl)

/-- **The Selmer module of the Selmer data of `𝓕` is the Selmer group of `𝓕`.** -/
@[simp]
theorem selmerModule_toSelmerData :
    𝓕.toSelmerData.selmerModule = 𝓕.selmerGroup.toIntSubmodule := by
  ext c
  rw [SelmerData.mem_selmerModule_iff, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule,
    SetLike.mem_coe, mem_selmerGroup_iff]
  exact Iff.rfl

/-- Replacing the local conditions of a Selmer structure replaces those of its Selmer data. -/
theorem toSelmerData_withLocalConditions (A : ∀ i, AddSubgroup (H1 (H i) (N i))) :
    (𝓕.withLocalConditions A).toSelmerData =
      𝓕.toSelmerData.withLocalConditions fun i => (A i).toIntSubmodule := by
  ext1
  · funext i
    simp
  · funext i
    simp

/-- Relaxing the local conditions of a Selmer structure commutes with passing to its Selmer
data. -/
@[simp]
theorem toSelmerData_relax (S : Set ι) :
    (𝓕.relax S).toSelmerData = 𝓕.toSelmerData.relax S := by
  ext1
  · funext i; simp
  · funext i
    by_cases hi : i ∈ S <;> simp [relax_localCondition, hi]

/-- Membership in the `S`-relaxed Selmer group is satisfaction of the local conditions outside
`S`. -/
theorem mem_selmerGroup_relax_iff (S : Set ι) {c : H1 G M} :
    c ∈ (𝓕.relax S).selmerGroup ↔ ∀ i ∉ S, 𝓕.localization i c ∈ 𝓕.localCondition i := by
  rw [← SetLike.mem_coe, ← AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe,
    ← selmerModule_toSelmerData, toSelmerData_relax, SelmerData.mem_selmerModule_relax_iff]
  rfl

/-- The original Selmer group is contained in every `S`-relaxed Selmer group. -/
theorem selmerGroup_le_relax (S : Set ι) : 𝓕.selmerGroup ≤ (𝓕.relax S).selmerGroup := by
  intro c hc
  have hc' : c ∈ (𝓕.toSelmerData.relax S).selmerModule :=
    𝓕.toSelmerData.le_selmerModule_relax S (by
      rwa [selmerModule_toSelmerData, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule])
  rwa [← toSelmerData_relax, selmerModule_toSelmerData, ← SetLike.mem_coe,
    AddSubgroup.coe_toIntSubmodule] at hc'

end TauCeti.ContCohomology.SelmerStructure
