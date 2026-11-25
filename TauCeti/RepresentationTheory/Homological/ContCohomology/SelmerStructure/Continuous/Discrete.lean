/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Continuous.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Comparison

/-!
# Selmer structures on discrete representations

A Selmer structure `𝓕` on a topological representation `X` (`TauCeti.ContinuousCohomology`'s
`TopSelmerStructure`) localises Mathlib's `continuousCohomology 1 X`. When `X` and the local
coefficients `Y i` are discrete, as is the quotient `A = V/T` of a rational representation by a
lattice, the explicit model identifies `continuousCohomology 1 X` with the explicit `H¹` of the
carrier `X.V` (`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete`), and the localisation
maps of `𝓕` with the explicit pullbacks along the same compatible pairs.

So `𝓕` is a discrete Selmer structure `TauCeti.ContCohomology.SelmerStructure` on `X.V`, with the
local conditions transported along the explicit comparison, and the explicit comparison carries
its Selmer group onto the Selmer module of `𝓕`. Hence the compact and rational Selmer modules of
`TauCeti/RepresentationTheory/Homological/ContCohomology/SelmerStructure/Continuous/Basic.lean`,
after change of coefficients to `A`, land in the discrete Selmer groups of the existing interface:
no second discrete carrier is introduced.

## Main definitions

* `TauCeti.ContinuousCohomology.TopSelmerStructure.toSelmerStructure`: the discrete Selmer
  structure on the carrier of a discrete representation.

## Main results

* `TopSelmerStructure.explicitH1AddEquivContinuousCohomologyOfDiscrete_localization`:
  the explicit comparison carries the explicit localisation to the localisation of `𝓕`.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.toSelmerStructure_withLocalConditions`:
  replacing the local conditions commutes with passing to the discrete Selmer structure.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.mem_selmerGroup_toSelmerStructure_iff`: a
  class is in the discrete Selmer group exactly when its image is in the Selmer module of `𝓕`.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.map_selmerGroup_toSelmerStructure`: the
  explicit comparison carries the discrete Selmer group onto the Selmer module of `𝓕`.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.1 and I.5.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.ContinuousCohomology.TopSelmerStructure

open TauCeti.ContCohomology

attribute [local instance] TopRep.distribMulAction

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type*} {H : ι → Type v} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)]
  {φ : ∀ i, H i →ₜ* G} {X : TopRep.{v} R G} {Y : ∀ i, TopRep.{v} R (H i)}
  [ContinuousSMul G X.V]
  [∀ i, DiscreteTopology (Y i).V] [∀ i, ContinuousSMul (H i) (Y i).V]
  (𝓕 : TopSelmerStructure φ X Y)

/-- **The discrete Selmer structure of a Selmer structure with discrete local coefficients**:
the compatible pairs `(φ i, 𝓕.coeffHom i)` on the carriers, and the local conditions of `𝓕` pulled
back along the explicit comparison `H¹(H i, (Y i).V) ≃ continuousCohomology 1 (Y i)`. -/
def toSelmerStructure : SelmerStructure G X.V H fun i => (Y i).V where
  groupHom := φ
  coeffHom i := (𝓕.coeffHom i).hom.toContinuousLinearMap.toLinearMap.toAddMonoidHom
  continuous_coeffHom i := (𝓕.coeffHom i).hom.toContinuousLinearMap.continuous
  coeffHom_smul i h x := (𝓕.coeffHom i).hom.isIntertwining h x
  localCondition i := (𝓕.localCondition i).toAddSubgroup.comap
    (Y i).explicitH1AddEquivContinuousCohomologyOfDiscrete.toAddMonoidHom

omit [IsTopologicalGroup G] [ContinuousSMul G X.V] in
/-- The local groups of `𝓕.toSelmerStructure` are those of `𝓕`. -/
@[simp]
theorem toSelmerStructure_groupHom (i : ι) : 𝓕.toSelmerStructure.groupHom i = φ i :=
  (rfl)

omit [IsTopologicalGroup G] [ContinuousSMul G X.V] in
/-- The coefficient maps of `𝓕.toSelmerStructure` are the underlying maps of those of `𝓕`. -/
@[simp]
theorem toSelmerStructure_coeffHom_apply (i : ι) (x : X.V) :
    𝓕.toSelmerStructure.coeffHom i x = (𝓕.coeffHom i).hom x :=
  (rfl)

omit [IsTopologicalGroup G] [ContinuousSMul G X.V] in
/-- The local conditions of `𝓕.toSelmerStructure` are those of `𝓕` pulled back along the
explicit comparison. Membership is unfolded by the simp lemma
`mem_toSelmerStructure_localCondition_iff`. -/
theorem toSelmerStructure_localCondition (i : ι) :
    𝓕.toSelmerStructure.localCondition i = (𝓕.localCondition i).toAddSubgroup.comap
      (Y i).explicitH1AddEquivContinuousCohomologyOfDiscrete.toAddMonoidHom :=
  (rfl)

omit [IsTopologicalGroup G] [ContinuousSMul G X.V] in
/-- Replacing the local conditions of `𝓕` replaces those of `𝓕.toSelmerStructure` by their
pullbacks along the explicit comparison. -/
@[simp]
theorem toSelmerStructure_withLocalConditions
    (L : ∀ i, Submodule R (_root_.continuousCohomology 1 (Y i))) :
    (𝓕.withLocalConditions L).toSelmerStructure =
      𝓕.toSelmerStructure.withLocalConditions fun i => (L i).toAddSubgroup.comap
        (Y i).explicitH1AddEquivContinuousCohomologyOfDiscrete.toAddMonoidHom :=
  SelmerStructure.ext (funext fun i => by simp) (funext fun i => by ext; simp)
    (funext fun i => by simp [toSelmerStructure_localCondition])

omit [IsTopologicalGroup G] [ContinuousSMul G X.V] in
/-- A local class satisfies the discrete local condition exactly when its image under the
explicit comparison satisfies the local condition of `𝓕`. -/
@[simp]
theorem mem_toSelmerStructure_localCondition_iff (i : ι) {c : H1 (H i) (Y i).V} :
    c ∈ 𝓕.toSelmerStructure.localCondition i ↔
      (Y i).explicitH1AddEquivContinuousCohomologyOfDiscrete c ∈ 𝓕.localCondition i :=
  Iff.rfl

variable [DiscreteTopology X.V]

/-- **The explicit comparison carries the explicit localisation to the localisation of `𝓕`.** -/
@[simp]
theorem explicitH1AddEquivContinuousCohomologyOfDiscrete_localization (i : ι) (c : H1 G X.V) :
    (Y i).explicitH1AddEquivContinuousCohomologyOfDiscrete
        (𝓕.toSelmerStructure.localization i c) =
      𝓕.localization i (X.explicitH1AddEquivContinuousCohomologyOfDiscrete c) := by
  rw [SelmerStructure.localization_eq_explicitMap1, localization_apply]
  exact (X.explicitH1AddEquivContinuousCohomologyOfDiscrete_map (Y i) (φ i) (𝓕.coeffHom i)
    (𝓕.toSelmerStructure.coeffHom i) (fun _ => rfl) (𝓕.toSelmerStructure.coeffHom_smul i) c).symm

/-- **A class is in the discrete Selmer group exactly when its image under the explicit
comparison is in the Selmer module of `𝓕`.** -/
theorem mem_selmerGroup_toSelmerStructure_iff {c : H1 G X.V} :
    c ∈ 𝓕.toSelmerStructure.selmerGroup ↔
      X.explicitH1AddEquivContinuousCohomologyOfDiscrete c ∈ 𝓕.toSelmerData.selmerModule := by
  rw [SelmerStructure.mem_selmerGroup_iff, mem_selmerModule_toSelmerData_iff]
  refine forall_congr' fun i => ?_
  rw [mem_toSelmerStructure_localCondition_iff,
    explicitH1AddEquivContinuousCohomologyOfDiscrete_localization]

/-- **The explicit comparison carries the discrete Selmer group onto the Selmer module of
`𝓕`.** -/
theorem map_selmerGroup_toSelmerStructure :
    𝓕.toSelmerStructure.selmerGroup.map
        X.explicitH1AddEquivContinuousCohomologyOfDiscrete.toAddMonoidHom =
      𝓕.toSelmerData.selmerModule.toAddSubgroup := by
  ext c
  obtain ⟨c, rfl⟩ := X.explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective c
  rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply,
    mem_selmerGroup_toSelmerStructure_iff, Submodule.mem_toAddSubgroup]

end TauCeti.ContinuousCohomology.TopSelmerStructure
