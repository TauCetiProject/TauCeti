/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Immersed.Differential
public import TauCeti.Geometry.Lie.InvariantVectorField.Distribution
public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Basic
import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.WeakEmbeddedness
import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic

/-!
# The canonical Lie algebra of an immersed subgroup

For a connected immersed subgroup presentation, its differential range is exactly the ambient
Lie subalgebra associated to its image. Membership is equivalent to the entire exponential line
remaining in the subgroup. The source keeps its intrinsic topology, so the image need not be closed
and its topology need not be the subspace topology.

The ambient Lie group is finite dimensional, real and smooth. No ambient second countability or
boundaryless-model hypothesis is imposed; Hausdorffness follows from its Lie-group structure.

## Main results

* `TauCeti.Lie.ImmersedLieSubgroupData.isIntegralManifold_toHom`: the presenting immersion is
  integral for the invariant distribution of its differential range.
* `TauCeti.Lie.ImmersedLieSubgroupData.range_lieMapToHom`: the differential range is the
  canonical subgroup Lie algebra.
* `TauCeti.Lie.ImmersedLieSubgroupData.mem_lieSubalgebraOfSubgroup_iff`: the exponential-line
  membership criterion without a closedness hypothesis.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorems 8.46 and 19.25, pp.197 and 506, and Proposition 20.9, pp.521–522.
-/

public section

noncomputable section

open Set Function TauCeti Topology
open scoped Manifold ContDiff Topology

namespace TauCeti.Lie.ImmersedLieSubgroupData

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] TauCeti.Lie.ImmersedLieSubgroupData.group
  TauCeti.Lie.ImmersedLieSubgroupData.topologicalSpace
  TauCeti.Lie.ImmersedLieSubgroupData.normedAddCommGroup
  TauCeti.Lie.ImmersedLieSubgroupData.normedSpace
  TauCeti.Lie.ImmersedLieSubgroupData.finiteDimensional
  TauCeti.Lie.ImmersedLieSubgroupData.modelTopology
  TauCeti.Lie.ImmersedLieSubgroupData.chartedSpace
  TauCeti.Lie.ImmersedLieSubgroupData.lieGroup
  TauCeti.Lie.ImmersedLieSubgroupData.connectedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {K : Subgroup G}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : IsManifold I ((∞ : ℕ∞ω) + 1) G := by
  exact IsManifold.of_le (n := ∞) (by simp)

private local instance : IsManifold I (1 + 1) G :=
  IsManifold.of_le (n := ∞) (by simp)

/-- The presenting immersion is integral for the invariant distribution of its
differential range. -/
theorem isIntegralManifold_toHom (d : TauCeti.Lie.ImmersedLieSubgroupData I K) :
    IsIntegralManifold d.I' ∞
      (mulInvariantDistribution (d.lieMapToHom.range.map
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint).toLieHom).toSubmodule)
      (d.toHom : d.X → G) := by
  apply isIntegralManifold_iff.mpr
  refine ⟨inferInstance, d.isImmersion, fun x ↦ ?_⟩
  let eX := leftInvariantDerivationLieEquivGroupLieAlgebra (I := d.I') (G := d.X)
    BoundarylessManifold.isInteriorPoint
  let eG := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  have hnat (Y : LeftInvariantDerivation d.I' d.X) :
      mfderiv d.I' I d.toHom x (mulInvariantVectorField (eX Y) x) =
        mulInvariantVectorField (eG (d.lieMapToHom Y)) (d.toHom x) := by
    have hcoe : (d.toContMDiffMonoidMorphism : d.X → G) = d.toHom :=
      funext d.toContMDiffMonoidMorphism_apply
    have h := d.toContMDiffMonoidMorphism.mfderiv_mulInvariantVectorField_lieMap x Y
    rw [TauCeti.Lie.ImmersedLieSubgroupData.lieMap_toContMDiffMonoidMorphism, hcoe] at h
    exact h
  ext v
  rw [LinearMap.mem_range, mem_mulInvariantDistribution]
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := exists_mulInvariantVectorField_eq (I := d.I') w
    refine ⟨eG (d.lieMapToHom (eX.symm z)), ?_, ?_⟩
    · exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rw [← hnat, eX.apply_symm_apply, hz]
  · rintro ⟨w, hw, h⟩
    obtain ⟨Y, ⟨Z, rfl⟩, rfl⟩ := hw
    exact ⟨mulInvariantVectorField (eX Z) x, (hnat Z).trans h⟩

private theorem mem_range_of_exp_smul_mem [T2Space G]
    (d : TauCeti.Lie.ImmersedLieSubgroupData I K) (X : LeftInvariantDerivation I G)
    (hX : ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K) :
    X ∈ d.lieMapToHom.range := by
  let _ : SecondCountableTopology d.X :=
    d.I'.secondCountableTopology_of_lieGroup ∞ d.X
  -- The canonical tangent distribution is obtained from the differential range.
  let eG := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  let T := d.lieMapToHom.range.map eG.toLieHom
  let γ : ℝ → G := fun t ↦ mulInvariantExp (I := I) (G := G) (t • eG X)
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := contMDiff_mulInvariantExp_smul (eG X)
  have hγexp (t : ℝ) : γ t = lieExp (I := I) (t • X) := by
    simpa only [γ, eG, leftInvariantDerivationLieEquivGroupLieAlgebra_apply] using
      (lieExp_smul_eq_mulInvariantExp X t).symm
  have hr : range γ ⊆ range d.toHom := by
    rintro _ ⟨t, rfl⟩
    rw [← MonoidHom.coe_range, d.range_eq]
    exact hγexp t ▸ hX t
  have hinv : IsInvolutiveDistribution I (mulInvariantDistribution T.toSubmodule) :=
    isInvolutiveDistribution_mulInvariantDistribution fun v hv w hw ↦ T.lie_mem hv hw
  have hD : IsContMDiffDistribution I ∞ (Module.finrank ℝ T)
      (mulInvariantDistribution T.toSubmodule) :=
    isContMDiffDistribution_mulInvariantDistribution (m := ∞) (n := ∞) (by simp)
  have hi : IsIntegralManifold d.I' ∞ (mulInvariantDistribution T.toSubmodule) d.toHom :=
    d.isIntegralManifold_toHom
  obtain ⟨a, ha, hca⟩ := hi.exists_contMDiff_factor (r := ∞)
    (by simp) d.injective (by simp) hinv hD hγ hr
  have hmap0 : d.toHom (a 0) = 1 := (congrFun hca 0).trans (by simp [γ])
  -- Lift the exponential line through the intrinsic presentation, then differentiate at zero.
  have hderγ := (hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) (eG X)).mfderiv
  have htangent : eG X ∈ d.lieMapToHom.range.map eG.toLieHom := by
    have hm := hi.mfderiv_mem_of_comp_eq (x := (0 : ℝ)) (by simp)
      (ha.mdifferentiableAt (by simp)) (rfl : d.toHom ∘ a = d.toHom ∘ a) (1 : ℝ)
    simp only [Function.comp_apply] at hm
    rw [hca, hderγ, hmap0, mulInvariantDistribution_one] at hm
    -- Reindexing the tangent fiber leaves module instances at the old base point. Normalize
    -- those instances so the scalar-action rewrite can match under implicit transparency.
    change ((1 : ℝ →L[ℝ] ℝ).smulRight (eG X)) (1 : ℝ) ∈ T.toSubmodule at hm
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul,
      T, LieSubalgebra.mem_toSubmodule] using hm
  -- Transport the tangent vector back through the derivation–tangent Lie equivalence.
  rw [LieSubalgebra.mem_map] at htangent
  obtain ⟨Y, hY, heq⟩ := htangent
  exact eG.injective heq ▸ hY

/-- The differential range of a connected immersed presentation is the canonical Lie
subalgebra of its image subgroup. -/
@[simp]
theorem range_lieMapToHom (d : ImmersedLieSubgroupData I K) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    d.lieMapToHom.range = lieSubalgebraOfSubgroup (I := I) K := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  apply le_antisymm d.range_lieMapToHom_le
  exact lieSubalgebraOfSubgroup_le_iff.mpr (mem_range_of_exp_smul_mem d)

/-- For an immersed subgroup, a derivation belongs to its Lie algebra exactly when its
exponential line stays in the subgroup. -/
theorem mem_lieSubalgebraOfSubgroup_iff (d : ImmersedLieSubgroupData I K)
    (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    X ∈ lieSubalgebraOfSubgroup (I := I) K ↔ ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space d.X := d.I'.t2Space_of_lieGroup ∞
  dsimp only
  rw [← d.range_lieMapToHom]
  constructor
  · rintro ⟨Y, rfl⟩ t
    have hmem : d.toHom (lieExp (t • Y)) ∈ K := by
      exact d.range_eq.le ⟨_, rfl⟩
    simpa only [d.toHom_lieExp, map_smul, LieHom.coe_toLinearMap] using hmem
  · exact mem_range_of_exp_smul_mem d X

end TauCeti.Lie.ImmersedLieSubgroupData
