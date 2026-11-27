/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.LocallyFree
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Null

/-!
# Generic isotropy algebras of compact commutative Lie group actions

Let a compact commutative Lie group `G`, such as a torus, act smoothly on a connected Hausdorff
σ-compact manifold `M` without boundary, and let `𝔨 = {ξ | ξ_M = 0}` be the kernel of the
infinitesimal action, the Lie algebra of the kernel `⋂ₓ G_x` of the action. Every isotropy algebra
`𝔤_x = {ξ | ξ_M(x) = 0}` contains `𝔨` (`TauCeti.InfinitesimalAction.ker_toLinearMap_le_isotropy`).
This file proves that `𝔤_x = 𝔨` outside a null set (`TauCeti.Lie.isNullSet_setOf_isotropy_ne_ker`):
almost every point has isotropy algebra `𝔨`, for Lebesgue measure in the charts and so for every
measure with densities, such as a Liouville measure.

A point `x` with `𝔤_x ≠ 𝔨` is fixed by an element `g` of finite order of `G` which moves some
point of `M` (`TauCeti.Lie.exists_isOfFinOrder_smul_eq_exists_smul_ne_of_mem_isotropy`). There
are countably many elements of finite order in `G` (`TauCeti.Lie.countable_setOf_isOfFinOrder`).
The fixed set of each such `g` has clopen interior, which on the connected manifold `M` is empty
since `g` acts nontrivially (`TauCeti.interior_fixedBy_eq_empty`), so it is a null set
(`TauCeti.isNullSet_fixedBy_iff_of_compactSpace`). Hence the points with `𝔤_x ≠ 𝔨` lie in a
countable union of null sets.

For an effective action `𝔨 = 0`, so the action is locally free outside a null set
(`TauCeti.Lie.isNullSet_setOf_isotropy_ne_bot`). This strengthens the density of the locally free
points (`TauCeti.Lie.exists_isOpen_dense_forall_isotropy_eq_bot`).

## Main results

* `TauCeti.Lie.isNullSet_setOf_isotropy_ne_ker`: the points whose isotropy algebra is not the
  kernel of the infinitesimal action form a null set.
* `TauCeti.Lie.isNullSet_setOf_isotropy_ne_bot`: for an effective action, the points with
  nontrivial isotropy algebra form a null set.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press, 1972, Chapter IV,
  § 3 (principal orbits).
-/

public section

open MulAction Set
open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [SigmaCompactSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]

/-- **The generic isotropy algebra is the kernel of the infinitesimal action.** For a smooth
action of a compact commutative Lie group, such as a torus, on a connected Hausdorff σ-compact
manifold without boundary, the points whose isotropy algebra `𝔤_x = {ξ | ξ_M(x) = 0}` differs
from the kernel `𝔨 = {ξ | ξ_M = 0}` of the infinitesimal action form a null set. -/
theorem isNullSet_setOf_isotropy_ne_ker [CompactSpace G] [IsMulCommutative G]
    [PreconnectedSpace M] :
    IsNullSet I' {x : M | ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule ≠
      LinearMap.ker (InfinitesimalAction.fundamental I G I' M).toLinearMap} := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  let S := {g : G | IsOfFinOrder g ∧ ∃ y : M, g • y ≠ y}
  have hS : S.Countable := (countable_setOf_isOfFinOrder I).mono fun _ hg ↦ hg.1
  refine (IsNullSet.biUnion (s := fun g : G ↦ fixedBy M g) hS fun g hg ↦ ?_).mono fun x hx ↦ ?_
  · -- The fixed set of an element of finite order acting nontrivially has empty interior.
    rw [isNullSet_fixedBy_iff_of_compactSpace I g]
    exact interior_fixedBy_eq_empty hg.1 hg.2
      ((ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := ∞) g).of_le ENat.LEInfty.out)
  · -- A point whose isotropy algebra exceeds the kernel is fixed by an element of `S`.
    obtain ⟨ξ, hξ, hξk⟩ := IsConcreteLE.not_le_iff_exists.1 fun hle ↦
      hx (le_antisymm hle (InfinitesimalAction.ker_toLinearMap_le_isotropy _ x))
    obtain ⟨g, hg, hgx, hgy⟩ := exists_isOfFinOrder_smul_eq_exists_smul_ne_of_mem_isotropy hξ
      (mt (InfinitesimalAction.mem_ker_toLinearMap_iff _).2 hξk)
    exact mem_iUnion₂.2 ⟨g, ⟨hg, hgy⟩, hgx⟩

/-- **Effective actions of compact commutative Lie groups are locally free almost everywhere.**
For an effective smooth action of a compact commutative Lie group, such as a torus, on a connected
Hausdorff σ-compact manifold without boundary, the points with nontrivial isotropy algebra form a
null set. -/
theorem isNullSet_setOf_isotropy_ne_bot [CompactSpace G] [IsMulCommutative G] [FaithfulSMul G M]
    [PreconnectedSpace M] :
    IsNullSet I' {x : M | (InfinitesimalAction.fundamental I G I' M).isotropy x ≠ ⊥} := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  refine (isNullSet_setOf_isotropy_ne_ker (I := I) (G := G)).mono fun x hx ↦ ?_
  rwa [mem_ofPred_eq, InfinitesimalAction.ker_toLinearMap_fundamental_eq_bot, Ne,
    LieSubalgebra.toSubmodule_eq_bot]

end TauCeti.Lie
