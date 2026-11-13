/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# Orbit maps of smooth Lie group actions

Let a real Lie group `G`, modelled on a Banach space, with Lie algebra `𝔤 = GroupLieAlgebra I G`
act smoothly on the left on a manifold `M`, and fix `x : M`. This file studies the **orbit map**
`g ↦ g • x : G → M`.

The derivative of the orbit map is computed in
`TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap`. At the identity it is `ξ ↦ ξ_M(x)`, by
definition of the fundamental vector fields, and at `g` it reduces to the identity case
(`TauCeti.mfderiv_smul_const_apply`). There:

* the image of the derivative at `g` is the orbit tangent space `𝔤 · (g • x)`
  (`TauCeti.range_mfderiv_smul_const`);
* the derivative at `g` is injective exactly when the isotropy algebra `𝔤_x` is trivial
  (`TauCeti.injective_mfderiv_smul_const_iff`).

Hence the orbit map is an **immersion** exactly
when the action is locally free at `x`, that is, `𝔤_x = 0`
(`TauCeti.isImmersion_smul_const_iff`). For finite-dimensional `G`, by
`TauCeti.Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot` this means that the stabilizer `G_x`
is discrete; in particular the orbit map is an immersion where the stabilizer is trivial
(`TauCeti.isImmersion_smul_const_of_stabilizer_eq_bot`). For a proper action the orbit map is
moreover a closed topological embedding at such a point
(`ProperSMul.isClosedEmbedding_smul_const`). Hence **the orbit map of a free point of a proper
smooth action is a smooth embedding with closed image** (`TauCeti.isSmoothEmbedding_smul_const`).
This is the first step of the proof of the quotient manifold theorem for free proper actions.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Proposition 21.7 (orbits
  of proper actions are closed embedded submanifolds) and the proof of Theorem 21.10.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Section 1.6 and the proof of Theorem 1.21.
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [CompleteSpace E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

variable [FiniteDimensional ℝ E'] [I.Boundaryless] [I'.Boundaryless]

/-- **Orbit maps of locally free points are immersions.** The orbit map `g ↦ g • x` of a smooth
action is an immersion exactly when the isotropy algebra `𝔤_x` is trivial, that is, when the
action is locally free at `x`. -/
theorem isImmersion_smul_const_iff {x : M} :
    IsImmersion I I' ∞ (fun g : G ↦ g • x) ↔
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  constructor
  · intro h
    exact (injective_mfderiv_smul_const_iff x 1).1
      ((h.isImmersionAt 1).mfderiv_injective (by simp))
  · intro hx
    exact (ContMDiffSMul.contMDiff_smul_const x).isImmersion_of_injective_mfderiv (by simp)
      fun g ↦ (injective_mfderiv_smul_const_iff x g).2 hx

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] [CompleteSpace E'] in
/-- **Orbit maps of free points are immersions.** Where the stabilizer of `x` is trivial, the
orbit map `g ↦ g • x` of a smooth action on a Hausdorff manifold is an immersion. -/
theorem isImmersion_smul_const_of_stabilizer_eq_bot [T2Space M] {x : M}
    (hx : MulAction.stabilizer G x = ⊥) : IsImmersion I I' ∞ (fun g : G ↦ g • x) := by
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : Subsingleton (MulAction.stabilizer G x) := by
    rw [hx]
    infer_instance
  exact isImmersion_smul_const_iff.2
    ((Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := I) (I' := I')).1 inferInstance)

omit [CompleteSpace E] [CompleteSpace E'] in
/-- **Free orbits of proper smooth actions are closed embedded submanifolds.** Where the stabilizer
of `x` is trivial, the orbit map `g ↦ g • x` of a proper smooth action is a smooth embedding. Its
image, the orbit of `x`, is closed (`ProperSMul.isClosed_orbit`). -/
theorem isSmoothEmbedding_smul_const [ProperSMul G M] {x : M}
    (hx : MulAction.stabilizer G x = ⊥) : IsSmoothEmbedding I I' ∞ (fun g : G ↦ g • x) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  exact ⟨isImmersion_smul_const_of_stabilizer_eq_bot hx,
    (ProperSMul.isClosedEmbedding_smul_const hx).isEmbedding⟩

end TauCeti
