/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.InvariantVectorField.Distribution
public import TauCeti.Geometry.Manifold.Foliation.Leaf
public import Mathlib.Algebra.Lie.Subalgebra
import TauCeti.Geometry.Lie.Basic

/-!
# The integral leaf of a Lie subalgebra

A Lie subalgebra of a finite-dimensional real Lie group defines a left-invariant involutive
distribution, hence a foliation. Left multiplication preserves the tangent curves of this
foliation and therefore preserves its leaves. It follows that the leaf through the identity is a
subgroup. This file packages that subgroup and records its path-connectedness.

The topology on the subgroup subtype is still the subspace topology. Constructing the generally
finer manifold topology which makes this leaf an immersed Lie subgroup is separate work.

## Main definitions

* `LieSubalgebra.mulInvariantFoliation`: the foliation tangent to the left translates of a Lie
  subalgebra.
* `LieSubalgebra.integralLeafSubgroup`: the leaf through the identity, as a subgroup.

## Main results

* `LieSubalgebra.sameLeaf_mul_left_iff`: left multiplication preserves and reflects membership in
  the same leaf.
* `LieSubalgebra.isPathConnected_integralLeafSubgroup`: the integral leaf subgroup is
  path-connected as a subset of the ambient group.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19.
-/

public section

noncomputable section

open Set
open TauCeti
open TauCeti.Manifold
open scoped ContDiff Manifold

namespace LieSubalgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree

noncomputable local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local instance : IsManifold I (1 + 1) G := inferInstanceAs (IsManifold I 2 G)

/-- The foliation tangent to the left translates of a Lie subalgebra. -/
def mulInvariantFoliation (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    Foliation I 1 G (Module.finrank ℝ S) where
  one_le := le_rfl
  distribution := mulInvariantDistribution S.toSubmodule
  isContMDiffDistribution := by
    exact isContMDiffDistribution_mulInvariantDistribution (m := 1) (n := ∞) (by simp)
  isInvolutiveDistribution := by
    exact isInvolutiveDistribution_mulInvariantDistribution fun v hv w hw ↦ S.lie_mem hv hw

private theorem mulInvariantFoliation_distribution_def
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : G) :
    (S.mulInvariantFoliation (I := I)).distribution g =
      mulInvariantDistribution S.toSubmodule g :=
  rfl

/-- The tangent distribution of `S.mulInvariantFoliation` is the left-invariant distribution
defined by `S`. -/
@[simp]
theorem mulInvariantFoliation_distribution
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : G) :
    (S.mulInvariantFoliation (I := I)).distribution g =
      mulInvariantDistribution S.toSubmodule g :=
  mulInvariantFoliation_distribution_def S g

/-- Left multiplication carries a tangent curve of `S.mulInvariantFoliation` to another tangent
curve of the same foliation. -/
theorem joinedByTangentCurve_mul_left (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (h : G) {x y : G}
    (hxy : (S.mulInvariantFoliation (I := I)).JoinedByTangentCurve x y) :
    (S.mulInvariantFoliation (I := I)).JoinedByTangentCurve (h * x) (h * y) := by
  obtain ⟨γ, hγ, htan, rfl, rfl⟩ := TauCeti.Foliation.joinedByTangentCurve_iff.mp hxy
  apply TauCeti.Foliation.joinedByTangentCurve_iff.mpr
  refine ⟨(h * ·) ∘ γ, ?_, ?_, ?_, ?_⟩
  · exact (contMDiff_mul_left (I := I) (n := 1)).comp_contMDiffOn hγ
  · intro t ht
    rw [curveVelocityWithin_map (mdifferentiableAt_mul_left (I := I))
      (uniqueDiffOn_Icc zero_lt_one t ht)
      ((hγ.mdifferentiableOn one_ne_zero) t ht)]
    change mfderiv I I (h * ·) (γ t) (curveVelocityWithin I γ (Icc 0 1) t) ∈
      mulInvariantDistribution S.toSubmodule (h * γ t)
    rw [← map_mfderiv_mul_left_mulInvariantDistribution h (γ t)]
    exact Submodule.mem_map_of_mem (by simpa using htan t ht)
  · rfl
  · rfl

/-- Left multiplication preserves the equivalence relation of lying on the same leaf of
`S.mulInvariantFoliation`. -/
theorem sameLeaf_mul_left (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (h : G) {x y : G}
    (hxy : (S.mulInvariantFoliation (I := I)).SameLeaf x y) :
    (S.mulInvariantFoliation (I := I)).SameLeaf (h * x) (h * y) := by
  let F := S.mulInvariantFoliation (I := I)
  exact TauCeti.Foliation.SameLeaf.induction_on hxy
    (fun _ _ hrel ↦ (S.joinedByTangentCurve_mul_left h hrel).sameLeaf)
    (fun x ↦ TauCeti.Foliation.SameLeaf.refl F (h * x))
    (fun _ _ _ ih ↦ ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ ↦ ih₁.trans ih₂)

/-- Two points lie on the same leaf of `S.mulInvariantFoliation` if and only if their left
translates do. -/
theorem sameLeaf_mul_left_iff (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (h : G)
    {x y : G} :
    (S.mulInvariantFoliation (I := I)).SameLeaf (h * x) (h * y) ↔
      (S.mulInvariantFoliation (I := I)).SameLeaf x y := by
  constructor
  · intro hxy
    simpa only [inv_mul_cancel_left] using S.sameLeaf_mul_left h⁻¹ hxy
  · exact S.sameLeaf_mul_left h

/-- The leaf through the identity tangent to the left translates of `S`, as a subgroup of `G`.

Its subtype initially has the subspace topology; this definition does not assert that the leaf is
an immersed Lie subgroup with that topology. -/
def integralLeafSubgroup (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) : Subgroup G where
  carrier := (S.mulInvariantFoliation (I := I)).leaf 1
  one_mem' := (S.mulInvariantFoliation (I := I)).mem_leaf_self 1
  mul_mem' := by
    intro x y hx hy
    have hx' : (S.mulInvariantFoliation (I := I)).SameLeaf 1 x :=
      TauCeti.Foliation.mem_leaf.mp hx
    have hy' : (S.mulInvariantFoliation (I := I)).SameLeaf 1 y :=
      TauCeti.Foliation.mem_leaf.mp hy
    have hxy : (S.mulInvariantFoliation (I := I)).SameLeaf x (x * y) := by
      simpa only [mul_one] using S.sameLeaf_mul_left x hy'
    exact TauCeti.Foliation.mem_leaf.mpr (hx'.trans hxy)
  inv_mem' := by
    intro x hx
    have hx' : (S.mulInvariantFoliation (I := I)).SameLeaf 1 x :=
      TauCeti.Foliation.mem_leaf.mp hx
    exact TauCeti.Foliation.mem_leaf.mpr (by
      simpa using (S.sameLeaf_mul_left x⁻¹ hx').symm)

private theorem coe_integralLeafSubgroup_def
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    (S.integralLeafSubgroup (I := I) : Set G) =
      (S.mulInvariantFoliation (I := I)).leaf 1 :=
  rfl

/-- The carrier of the integral leaf subgroup is exactly the leaf through the identity. -/
theorem coe_integralLeafSubgroup (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    (S.integralLeafSubgroup (I := I) : Set G) =
      (S.mulInvariantFoliation (I := I)).leaf 1 :=
  coe_integralLeafSubgroup_def S

/-- Membership in the integral leaf subgroup means lying on the same leaf as the identity. -/
@[simp]
theorem mem_integralLeafSubgroup (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : G) :
    g ∈ S.integralLeafSubgroup (I := I) ↔
      (S.mulInvariantFoliation (I := I)).SameLeaf 1 g := by
  change g ∈ (S.integralLeafSubgroup (I := I) : Set G) ↔ _
  rw [coe_integralLeafSubgroup, TauCeti.Foliation.mem_leaf]

/-- The integral leaf subgroup is path-connected as a subset of the ambient group. -/
theorem isPathConnected_integralLeafSubgroup
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    IsPathConnected (S.integralLeafSubgroup (I := I) : Set G) := by
  rw [coe_integralLeafSubgroup]
  exact (S.mulInvariantFoliation (I := I)).isPathConnected_leaf 1

end LieSubalgebra
