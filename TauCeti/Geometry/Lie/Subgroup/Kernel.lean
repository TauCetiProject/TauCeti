/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.Subgroup.Embedded

/-!
# Lie maps of homomorphisms with discrete kernel

If a continuous homomorphism `f : G → G'` of finite-dimensional real Lie groups has discrete kernel,
then its Lie map `df` is injective. For `df X = 0` the one-parameter subgroup `t ↦ exp(t X)` lies in
`ker f`, so `X` lies in the Lie algebra of the closed subgroup `ker f`, which is trivial because
`ker f` is discrete (`TauCeti.Lie.discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot`).

## Main results

* `ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`: a continuous homomorphism with
  discrete kernel has injective Lie map.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContinuousMonoidHom

open TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']

/-- **A continuous homomorphism with discrete kernel has injective Lie map.** In particular the Lie
map of a homomorphism with finite kernel is injective. -/
theorem lieMap_injective_of_discreteTopology_ker (f : G →ₜ* G') [DiscreteTopology f.ker] :
    Function.Injective (lieMap (I := I) (I' := I') f) := by
  refine (injective_iff_map_eq_zero (lieMap (I := I) (I' := I') f).toLinearMap).2 fun X hX ↦ ?_
  have hX' : lieMap (I := I) (I' := I') f X = 0 := hX
  -- The exponentials of `G` and `G'` need these instances; they hold for every Lie group.
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  have : T2Space G' := I'.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I' G' := ContMDiffMul.boundarylessManifold
  -- The one-parameter subgroup through `X` lies in the kernel of `f`.
  have hker (t : ℝ) : lieExp (I := I) (G := G) (t • X) ∈ f.ker := by
    rw [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      map_lieExp (I' := I'), map_smul, hX', smul_zero, lieExp_zero]
  -- So `X` lies in the Lie algebra of the closed discrete subgroup `ker f`, which is trivial.
  have hclosed : IsClosed (f.ker : Set G) := isClosed_singleton.preimage f.continuous
  have hmem := mem_lieSubalgebraOfSubgroup_of_forall (K := f.ker) hker
  rwa [(discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot (I := I) hclosed).1 inferInstance,
    LieSubalgebra.mem_bot] at hmem

end ContinuousMonoidHom
