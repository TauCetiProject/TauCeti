/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.LocallyFree
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Null

/-!
# Effective actions of compact commutative Lie groups are locally free off a null set

Let a compact commutative Lie group `G`, such as a torus, act smoothly and effectively on a
connected Hausdorff σ-compact manifold `M` without boundary. The points `x` whose isotropy algebra
`𝔤_x = {ξ | ξ_M(x) = 0}` is nontrivial lie in the fixed sets of the finitely many involutions
`g ≠ 1` of `G` (`TauCeti.Lie.exists_sq_eq_one_ne_one_smul_eq_of_isotropy_ne_bot`). Each such
fixed set has empty interior, since `g` acts nontrivially on the connected manifold `M`
(`TauCeti.interior_fixedBy_eq_empty`), so it is a null set
(`TauCeti.isNullSet_fixedBy_iff_of_compactSpace`). Hence the action is locally free outside a
closed null set (`TauCeti.Lie.isNullSet_setOf_isotropy_ne_bot`): almost every point has trivial
isotropy algebra, for Lebesgue measure in the charts and so for every measure with densities, such
as a Liouville measure. This strengthens the density of the locally free points
(`TauCeti.Lie.exists_isOpen_dense_forall_isotropy_eq_bot`).

## Main results

* `TauCeti.Lie.isNullSet_setOf_isotropy_ne_bot`: the points with nontrivial isotropy algebra form
  a null set.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press, 1972, Chapter IV,
  § 3 (principal orbits).
-/

public section

open MulAction Set
open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [SigmaCompactSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]

/-- **Effective actions of compact commutative Lie groups are locally free almost everywhere.**
For an effective smooth action of a compact commutative Lie group, such as a torus, on a connected
Hausdorff σ-compact manifold without boundary, the points with nontrivial isotropy algebra form a
null set. -/
theorem isNullSet_setOf_isotropy_ne_bot [CompactSpace G] [IsMulCommutative G] [FaithfulSMul G M]
    [PreconnectedSpace M] :
    IsNullSet I' {x : M | (InfinitesimalAction.fundamental I G I' M).isotropy x ≠ ⊥} := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  let S := {g : G | g ^ 2 = 1 ∧ g ≠ 1}
  have hS : S.Finite := (finite_setOf_pow_eq_one I two_ne_zero).subset fun g hg ↦ hg.1
  -- Every point with nontrivial isotropy is fixed by one of the finitely many involutions `g ≠ 1`,
  -- whose fixed sets have empty interior, hence are null.
  refine (IsNullSet.biUnion (s := fun g : G ↦ fixedBy M g) hS.countable fun g hg ↦ ?_).mono
    fun x hx ↦ ?_
  · rw [isNullSet_fixedBy_iff_of_compactSpace I g]
    exact interior_fixedBy_eq_empty (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, hg.1⟩) hg.2
      ((ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := ∞) g).of_le
        ENat.LEInfty.out)
  · obtain ⟨g, hg2, hg1, hgx⟩ := exists_sq_eq_one_ne_one_smul_eq_of_isotropy_ne_bot hx
    exact mem_iUnion₂.2 ⟨g, ⟨hg2, hg1⟩, hgx⟩

end TauCeti.Lie
