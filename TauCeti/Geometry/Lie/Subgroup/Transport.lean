/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Transporting an embedded subgroup to its native group carrier

A continuous multiplicative equivalence with an embedded subgroup transports its charts,
smooth inclusion and Lie-algebra comparison to another group with its original topology.
The diffeomorphism is the canonical pullback of charts, and the Lie equivalence is the
differential of the actual transported inclusion.

## Main declarations

* `TauCeti.Lie.EmbeddedLieSubgroupData.pullbackSmoothHom`: the smooth ambient inclusion.
* `TauCeti.Lie.EmbeddedLieSubgroupData.pullbackSmoothHom_apply`: its underlying map.
* `TauCeti.Lie.EmbeddedLieSubgroupData.isSmoothEmbedding_pullbackSmoothHom`: the embedding.
* `TauCeti.Lie.EmbeddedLieSubgroupData.pullbackLieEquiv`: the native Lie-algebra comparison.
* `TauCeti.Lie.EmbeddedLieSubgroupData.coe_pullbackLieEquiv_apply`: its differential equation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12 and Proposition 7.11 (embedded Lie subgroups).
-/

public section

open scoped ContDiff Manifold
noncomputable section

namespace TauCeti.Lie.EmbeddedLieSubgroupData

universe u v w z

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {V : Type z} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {K : Subgroup G} {A : Type*} [Group A] [TopologicalSpace A]
  (d : EmbeddedLieSubgroupData I K V) (e : A ≃ₜ* K)

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The native carrier is diffeomorphic to the embedded subgroup in the pulled-back atlas. -/
private def pullbackDiffeomorph :
    let _ := d.chartedSpace
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    A ≃ₘ^∞⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ K := by
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  exact e.toHomeomorph.pullbackDiffeomorph 𝓘(ℝ, V) ∞

/-- The pullback diffeomorphism is the original continuous multiplicative equivalence. -/
@[simp]
private theorem coe_pullbackDiffeomorph :
    let _ := d.chartedSpace
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    (pullbackDiffeomorph d e : A → K) = e := by
  dsimp only
  let _ := d.chartedSpace
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  unfold pullbackDiffeomorph
  exact e.toHomeomorph.coe_pullbackDiffeomorph 𝓘(ℝ, V) ∞

private def pullbackToSubgroup :
    let _ := d.chartedSpace
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    ContMDiffMonoidMorphism 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ A K := by
  let _ := d.chartedSpace
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  exact
    { toMonoidHom := e.toMonoidHom
      contMDiff_toFun := by
        have h := (pullbackDiffeomorph d e).contMDiff
        rw [coe_pullbackDiffeomorph] at h
        exact h }

private theorem pullbackToSubgroup_apply (a : A) :
    let _ := d.chartedSpace
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    pullbackToSubgroup d e a = e a := by
  dsimp only
  let _ := d.chartedSpace
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  unfold pullbackToSubgroup
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [LieGroup I ∞ G] [T2Space G]

/-- The embedded subgroup inclusion transported to a continuously equivalent group. -/
def pullbackSmoothHom :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    ContMDiffMonoidMorphism 𝓘(ℝ, V) I ∞ A G := by
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  exact d.subtypeVal.comp (pullbackToSubgroup d e)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [LieGroup I ∞ G] [T2Space G] in
/-- The transported inclusion sends a native element to its original ambient group element. -/
@[simp]
theorem pullbackSmoothHom_apply (a : A) :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    pullbackSmoothHom d e a = (e a : G) := by
  dsimp only
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  rw [pullbackSmoothHom, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    EmbeddedLieSubgroupData.subtypeVal_apply, pullbackToSubgroup_apply]

/-- In a finite-dimensional Hausdorff real Lie group, transport identifies the native Lie algebra
of a finite-dimensional embedded subgroup with its ambient Lie subalgebra. -/
def pullbackLieEquiv :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    let _ := e.lieGroup_pullbackChartedSpace (I := 𝓘(ℝ, V)) (n := ∞)
    LeftInvariantDerivation 𝓘(ℝ, V) A ≃ₗ⁅ℝ⁆ lieSubalgebraOfSubgroup (I := I) K := by
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  let _ := e.lieGroup_pullbackChartedSpace (I := 𝓘(ℝ, V)) (n := ∞)
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ (pullbackToSubgroup d e) 1 := by
    have he : (pullbackToSubgroup d e : A → K) = pullbackDiffeomorph d e := by
      ext a
      rw [pullbackToSubgroup_apply, coe_pullbackDiffeomorph]
    rw [he]
    exact (pullbackDiffeomorph d e).isLocalDiffeomorph 1
  exact (lieEquivOfIsLocalDiffeomorphAt (pullbackToSubgroup d e) hlocal).trans
    d.lieEquivLieSubalgebraOfSubgroup

/-- The transported Lie equivalence is the differential of the transported inclusion. -/
@[simp]
theorem coe_pullbackLieEquiv_apply :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    let _ := e.lieGroup_pullbackChartedSpace (I := 𝓘(ℝ, V)) (n := ∞)
    ∀ D : LeftInvariantDerivation 𝓘(ℝ, V) A,
      (pullbackLieEquiv d e D : LeftInvariantDerivation I G) =
        lieMap (pullbackSmoothHom d e) D := by
  dsimp only
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  let _ := e.lieGroup_pullbackChartedSpace (I := 𝓘(ℝ, V)) (n := ∞)
  intro D
  rw [pullbackLieEquiv, LieEquiv.trans_apply,
    EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup_apply,
    EmbeddedLieSubgroupData.lieMapSubtypeVal_apply, lieEquivOfIsLocalDiffeomorphAt_apply]
  exact (DFunLike.congr_fun
    (lieMap_comp (pullbackToSubgroup d e) d.subtypeVal) D).symm

omit [FiniteDimensional ℝ V] [T2Space G] in
/-- The transported inclusion is a smooth embedding for a finite-dimensional boundaryless
ambient model. -/
theorem isSmoothEmbedding_pullbackSmoothHom [I.Boundaryless] :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
    Manifold.IsSmoothEmbedding 𝓘(ℝ, V) I ∞ (pullbackSmoothHom d e) := by
  dsimp only
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ := e.toHomeomorph.pullbackChartedSpace (H := V)
  let _ := e.lieGroup_pullbackChartedSpace (I := 𝓘(ℝ, V)) (n := ∞)
  have h := TauCeti.isSmoothEmbedding_comp_isLocalDiffeomorph
    (g := pullbackDiffeomorph d e) (f := fun x : K ↦ (x : G))
    (pullbackDiffeomorph d e).isLocalDiffeomorph
    (pullbackDiffeomorph d e).toHomeomorph.isEmbedding d.isSmoothEmbedding_subtypeVal
  have he : (fun x : K ↦ (x : G)) ∘ pullbackDiffeomorph d e = pullbackSmoothHom d e := by
    ext a
    rw [Function.comp_apply, coe_pullbackDiffeomorph, pullbackSmoothHom_apply]
  exact he ▸ h

end TauCeti.Lie.EmbeddedLieSubgroupData
