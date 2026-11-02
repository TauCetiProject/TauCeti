/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Lie.Tangent.LieEquiv

import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Stabilizers of smooth actions and their Lie algebras

Let a Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G` act smoothly on the left on a
manifold `M`. The **stabilizer** `G_x = {g ∈ G | g • x = x}` of a point `x` is Mathlib's
`MulAction.stabilizer G x`, and the **isotropy algebra** `𝔤_x = {ξ ∈ 𝔤 | ξ_M(x) = 0}` of `x` is the
kernel of the evaluation `ξ ↦ ξ_M(x)` of the fundamental vector fields at `x`
(`TauCeti.InfinitesimalAction.isotropy` of `TauCeti.InfinitesimalAction.fundamental`).

This file relates the two. On a `T₁` manifold the stabilizer is closed, hence an embedded Lie
subgroup by the closed-subgroup theorem. The one-parameter subgroup `t ↦ exp (t ξ)` fixes `x`
exactly when `ξ_M(x) = 0`: the curve `t ↦ exp (t ξ) • x` is an integral curve of `ξ_M` through
`x`, which is the constant curve exactly when `ξ_M(x) = 0`, by uniqueness of integral curves.
Consequently **the Lie algebra of `G_x` is `𝔤_x`**. Along an orbit, the isotropy algebras are
conjugate, `𝔤_{g • x} = Ad_g 𝔤_x`, as the stabilizers are.

The action is **locally free** at `x` when `G_x` is discrete. Since `G_x` is an embedded Lie
subgroup modelled on its Lie algebra `𝔤_x`, this happens exactly when `𝔤_x = 0`, that is, when
`ξ ↦ ξ_M(x)` is injective. In particular a free action has trivial isotropy algebras. Through
`TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_iff` this is what makes every point
with discrete stabilizer a regular point of a moment map.

## Main results

* `TauCeti.Lie.isEmbeddedLieSubgroup_stabilizer`: the stabilizer of a point of a `T₁` space under a
  continuous action of a Lie group is an embedded Lie subgroup.
* `TauCeti.Lie.mulInvariantExp_smul_smul_eq_iff`: `exp (t ξ) • x = x` for every `t` exactly when
  `ξ_M(x) = 0`.
* `TauCeti.Lie.lieSubalgebraOfSubgroup_stabilizer`: **the Lie algebra of `G_x` is the isotropy
  algebra `𝔤_x`**, transported to left-invariant derivations by evaluation at the identity.
* `TauCeti.Lie.adjointContinuousLinearMap_mem_isotropy_smul_iff`: `Ad_g ξ ∈ 𝔤_{g • x}` exactly
  when `ξ ∈ 𝔤_x`.
* `TauCeti.Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot`: the stabilizer is discrete
  exactly when the isotropy algebra is trivial.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 20 (the closed-subgroup
  theorem and infinitesimal generators of actions).
* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, §9.3
  (isotropy groups and their Lie algebras).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]

section OneParameter

variable [CompleteSpace E] [T2Space G]

/-- **The one-parameter subgroups fixing a point.** For a `C²` action on a Hausdorff manifold
without boundary, the one-parameter subgroup `t ↦ exp (t ξ)` fixes `x` exactly when the fundamental
vector field `ξ_M` vanishes at `x`. The curve `t ↦ exp (t ξ) • x` is an integral curve of `ξ_M`
through `x`; it is constant exactly when `ξ_M(x) = 0`, by uniqueness of integral curves. -/
theorem mulInvariantExp_smul_smul_eq_iff [IsManifold I' 1 M] [T2Space M]
    [BoundarylessManifold I' M] [ContMDiffSMul I I' 2 G M] {ξ : GroupLieAlgebra I G} {x : M} :
    (∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) • x = x) ↔ fundamentalVectorField I' ξ x = 0 := by
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) one_le_two
  have hcurve := isMIntegralCurve_mulInvariantExp_smul_smul (I' := I') ξ x
  constructor
  · -- If the integral curve is constant, its velocity `ξ_M(x)` at time `0` vanishes.
    intro h
    have hconst : (fun t : ℝ ↦ mulInvariantExp (I := I) (t • ξ) • x) = fun _ ↦ x := funext h
    have hderiv := DFunLike.congr_fun (hcurve 0).mfderiv 1
    rw [hconst, mfderiv_const] at hderiv
    -- Both sides are evaluated at `1`: `smulRight 1 v` sends `1` to `1 • v` by definition, and the
    -- zero map sends it to `0`. The rewriting lemmas do not fire through the tangent-space types.
    have h1 : (1 : ℝ) • fundamentalVectorField I' ξ x = 0 := hderiv.symm
    rwa [one_smul] at h1
  · -- If `ξ_M(x) = 0`, the constant curve at `x` is an integral curve of `ξ_M` through `x` too.
    intro h
    have hconst : IsMIntegralCurve (fun _ : ℝ ↦ x) (fundamentalVectorField I' ξ) := by
      intro t
      rw [h, ContinuousLinearMap.smulRight_zero]
      exact hasMFDerivAt_const x t
    have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
      (contMDiff_fundamentalVectorField (m := 1) (n := 2) (by norm_num) ξ) hcurve hconst
      (by simp)
    exact fun t ↦ congrFun heq t

end OneParameter

variable [FiniteDimensional ℝ E]

variable (I) in
/-- **The stabilizer is a Lie group.** For a continuous action of a finite-dimensional real Lie
group on a `T₁` space, the stabilizer of a point is closed, hence an embedded Lie subgroup by the
closed-subgroup theorem. -/
theorem isEmbeddedLieSubgroup_stabilizer [ContinuousSMul G M] [T1Space M] (x : M) :
    IsEmbeddedLieSubgroup (I := I) (MulAction.stabilizer G x) :=
  isEmbeddedLieSubgroup_of_isClosed (isClosed_stabilizer (continuous_id.smul continuous_const))

variable [T2Space G] [IsManifold I' ∞ M] [T2Space M] [BoundarylessManifold I' M]
  [ContMDiffSMul I I' ∞ G M]

/-- Membership in the isotropy algebra of the fundamental infinitesimal action: `ξ ∈ 𝔤_x` exactly
when the one-parameter subgroup generated by `ξ` fixes `x`. -/
theorem mem_isotropy_fundamental_iff [CompleteSpace E'] {ξ : GroupLieAlgebra I G} {x : M} :
    ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x ↔
      ∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) ∈ MulAction.stabilizer G x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : ContMDiffSMul I I' 2 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  simp only [InfinitesimalAction.mem_isotropy_iff, InfinitesimalAction.fundamental_apply,
    MulAction.mem_stabilizer_iff]
  exact mulInvariantExp_smul_smul_eq_iff.symm

/-- **The Lie algebra of the stabilizer is the isotropy algebra.** Under the identification of
left-invariant derivations with `𝔤` by evaluation at the identity, the Lie algebra
`TauCeti.Lie.lieSubalgebraOfSubgroup G_x` of the stabilizer of `x` is the isotropy algebra
`𝔤_x = {ξ | ξ_M(x) = 0}` of the fundamental infinitesimal action. -/
theorem lieSubalgebraOfSubgroup_stabilizer [CompleteSpace E'] (h₁ : I.IsInteriorPoint 1) (x : M) :
    lieSubalgebraOfSubgroup (I := I) (MulAction.stabilizer G x) =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).comap
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G) h₁).toLieHom := by
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') ∞
  ext X
  rw [mem_lieSubalgebraOfSubgroup (isClosed_stabilizer (continuous_id.smul continuous_const)),
    LieSubalgebra.mem_comap, LieEquiv.coe_toLieHom,
    leftInvariantDerivationLieEquivGroupLieAlgebra_apply, mem_isotropy_fundamental_iff]
  simp only [lieExp_eq_mulInvariantExp, map_smul]

/-- **Isotropy algebras along an orbit are conjugate.** `Ad_g ξ` lies in the isotropy algebra of
`g • x` exactly when `ξ` lies in that of `x`, matching the conjugation `G_{g • x} = g G_x g⁻¹` of
the stabilizers. -/
theorem adjointContinuousLinearMap_mem_isotropy_smul_iff [CompleteSpace E'] {g : G}
    {ξ : GroupLieAlgebra I G} {x : M} :
    adjointContinuousLinearMap (I := I) g ξ ∈
        (InfinitesimalAction.fundamental I G I' M).isotropy (g • x) ↔
      ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  simp only [mem_isotropy_fundamental_iff, MulAction.mem_stabilizer_iff]
  refine forall_congr' fun t ↦ ?_
  rw [← map_smul, ← tangentAd_apply, ← conj_mulInvariantExp, mul_smul, mul_smul, inv_smul_smul,
    smul_left_cancel_iff]

/-- **Locally free points.** The stabilizer of `x` is discrete exactly when the isotropy algebra
`𝔤_x` is trivial, that is, when `ξ ↦ ξ_M(x)` is injective
(`TauCeti.InfinitesimalAction.isotropy_eq_bot_iff`). -/
theorem discreteTopology_stabilizer_iff_isotropy_eq_bot [CompleteSpace E'] {x : M} :
    DiscreteTopology (MulAction.stabilizer G x) ↔
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') ∞
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  rw [discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot (I := I)
      (isClosed_stabilizer (continuous_id.smul continuous_const)),
    lieSubalgebraOfSubgroup_stabilizer (I' := I') BoundarylessManifold.isInteriorPoint x,
    LieSubalgebra.eq_bot_iff, LieSubalgebra.eq_bot_iff]
  -- Pulling back along the Lie equivalence `e` preserves triviality.
  refine ⟨fun h ξ hξ ↦ ?_, fun h X hX ↦ ?_⟩
  · have := h (e.symm ξ) (by
      rwa [LieSubalgebra.mem_comap, LieEquiv.coe_toLieHom, e.apply_symm_apply])
    simpa using congrArg e this
  · exact (LinearEquiv.map_eq_zero_iff e.toLinearEquiv).1 (h _ hX)

end TauCeti.Lie
